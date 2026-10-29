-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1503_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:53:05.639478+00:00
-- url     : https://prove2.me/submissions/802b5c0d-0117-4867-af98-41dc0442cd25

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
theorem support_rectangle_w1503_s6_0 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1881396421/10000000000 : ℝ)*x 0 + (2717201767/5000000000 : ℝ)*x 1 + (5217171281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1881396421/10000000000 : ℝ)^4503 ≤ (11506220614073/100000000000000 : ℝ)^3479 := by
    have hnat : (1881396421 : ℕ)^4503*100000000000000^3479 ≤ 11506220614073^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1881396421 10000000000 11506220614073 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717201767/5000000000 : ℝ)^4503 ≤ (22707387350707/50000000000000 : ℝ)^3479 := by
    have hnat : (2717201767 : ℕ)^4503*50000000000000^3479 ≤ 22707387350707^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717201767 5000000000 22707387350707 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217171281/10000000000 : ℝ)^4503 ≤ (10769751165889/25000000000000 : ℝ)^3479 := by
    have hnat : (5217171281 : ℕ)^4503*25000000000000^3479 ≤ 10769751165889^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217171281 10000000000 10769751165889 25000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1881396421/10000000000 : ℝ), (2717201767/5000000000 : ℝ), (5217171281/10000000000 : ℝ)] ![(11506220614073/100000000000000 : ℝ), (22707387350707/50000000000000 : ℝ), (10769751165889/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1881396421/10000000000 : ℝ)|^4503 ≤ (11506220614073/100000000000000 : ℝ)^3479
        have hw : |(-1881396421/10000000000 : ℝ)|=(1881396421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717201767/5000000000 : ℝ)|^4503 ≤ (22707387350707/50000000000000 : ℝ)^3479
        have hw : |(2717201767/5000000000 : ℝ)|=(2717201767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217171281/10000000000 : ℝ)|^4503 ≤ (10769751165889/25000000000000 : ℝ)^3479
        have hw : |(5217171281/10000000000 : ℝ)|=(5217171281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s6_1 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352085579/10000000000 : ℝ)*x 0 + (-1992672671/10000000000 : ℝ)*x 1 + (81518299/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352085579/10000000000 : ℝ)^4503 ≤ (4452636220063/10000000000000 : ℝ)^3479 := by
    have hnat : (5352085579 : ℕ)^4503*10000000000000^3479 ≤ 4452636220063^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352085579 10000000000 4452636220063 10000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1992672671/10000000000 : ℝ)^4503 ≤ (6197317335441/50000000000000 : ℝ)^3479 := by
    have hnat : (1992672671 : ℕ)^4503*50000000000000^3479 ≤ 6197317335441^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992672671 10000000000 6197317335441 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81518299/156250000 : ℝ)^4503 ≤ (43079003113861/100000000000000 : ℝ)^3479 := by
    have hnat : (81518299 : ℕ)^4503*100000000000000^3479 ≤ 43079003113861^3479*156250000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81518299 156250000 43079003113861 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352085579/10000000000 : ℝ), (-1992672671/10000000000 : ℝ), (81518299/156250000 : ℝ)] ![(4452636220063/10000000000000 : ℝ), (6197317335441/50000000000000 : ℝ), (43079003113861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352085579/10000000000 : ℝ)|^4503 ≤ (4452636220063/10000000000000 : ℝ)^3479
        have hw : |(5352085579/10000000000 : ℝ)|=(5352085579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1992672671/10000000000 : ℝ)|^4503 ≤ (6197317335441/50000000000000 : ℝ)^3479
        have hw : |(-1992672671/10000000000 : ℝ)|=(1992672671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81518299/156250000 : ℝ)|^4503 ≤ (43079003113861/100000000000000 : ℝ)^3479
        have hw : |(81518299/156250000 : ℝ)|=(81518299/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s6_2 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352085403/10000000000 : ℝ)*x 0 + (5217171293/10000000000 : ℝ)*x 1 + (-996336349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352085403/10000000000 : ℝ)^4503 ≤ (44526360305433/100000000000000 : ℝ)^3479 := by
    have hnat : (5352085403 : ℕ)^4503*100000000000000^3479 ≤ 44526360305433^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352085403 10000000000 44526360305433 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217171293/10000000000 : ℝ)^4503 ≤ (43079004791807/100000000000000 : ℝ)^3479 := by
    have hnat : (5217171293 : ℕ)^4503*100000000000000^3479 ≤ 43079004791807^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217171293 10000000000 43079004791807 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (996336349/5000000000 : ℝ)^4503 ≤ (12394634888257/100000000000000 : ℝ)^3479 := by
    have hnat : (996336349 : ℕ)^4503*100000000000000^3479 ≤ 12394634888257^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996336349 5000000000 12394634888257 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352085403/10000000000 : ℝ), (5217171293/10000000000 : ℝ), (-996336349/5000000000 : ℝ)] ![(44526360305433/100000000000000 : ℝ), (43079004791807/100000000000000 : ℝ), (12394634888257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352085403/10000000000 : ℝ)|^4503 ≤ (44526360305433/100000000000000 : ℝ)^3479
        have hw : |(5352085403/10000000000 : ℝ)|=(5352085403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217171293/10000000000 : ℝ)|^4503 ≤ (43079004791807/100000000000000 : ℝ)^3479
        have hw : |(5217171293/10000000000 : ℝ)|=(5217171293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-996336349/5000000000 : ℝ)|^4503 ≤ (12394634888257/100000000000000 : ℝ)^3479
        have hw : |(-996336349/5000000000 : ℝ)|=(996336349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s6_3 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4273981971/10000000000 : ℝ)*x 0 + (403524101/1000000000 : ℝ)*x 1 + (4524711233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4273981971/10000000000 : ℝ)^4503 ≤ (207995019651/625000000000 : ℝ)^3479 := by
    have hnat : (4273981971 : ℕ)^4503*625000000000^3479 ≤ 207995019651^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273981971 10000000000 207995019651 625000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403524101/1000000000 : ℝ)^4503 ≤ (30893143711459/100000000000000 : ℝ)^3479 := by
    have hnat : (403524101 : ℕ)^4503*100000000000000^3479 ≤ 30893143711459^3479*1000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403524101 1000000000 30893143711459 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4524711233/10000000000 : ℝ)^4503 ≤ (35827653129931/100000000000000 : ℝ)^3479 := by
    have hnat : (4524711233 : ℕ)^4503*100000000000000^3479 ≤ 35827653129931^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524711233 10000000000 35827653129931 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4273981971/10000000000 : ℝ), (403524101/1000000000 : ℝ), (4524711233/10000000000 : ℝ)] ![(207995019651/625000000000 : ℝ), (30893143711459/100000000000000 : ℝ), (35827653129931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4273981971/10000000000 : ℝ)|^4503 ≤ (207995019651/625000000000 : ℝ)^3479
        have hw : |(4273981971/10000000000 : ℝ)|=(4273981971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(403524101/1000000000 : ℝ)|^4503 ≤ (30893143711459/100000000000000 : ℝ)^3479
        have hw : |(403524101/1000000000 : ℝ)|=(403524101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4524711233/10000000000 : ℝ)|^4503 ≤ (35827653129931/100000000000000 : ℝ)^3479
        have hw : |(4524711233/10000000000 : ℝ)|=(4524711233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s6_4 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-58794541/312500000 : ℝ)*x 0 + (40767873/78125000 : ℝ)*x 1 + (1086655837/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58794541/312500000 : ℝ)^4503 ≤ (1438306164081/12500000000000 : ℝ)^3479 := by
    have hnat : (58794541 : ℕ)^4503*12500000000000^3479 ≤ 1438306164081^3479*312500000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58794541 312500000 1438306164081 12500000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40767873/78125000 : ℝ)^4503 ≤ (43090937291381/100000000000000 : ℝ)^3479 := by
    have hnat : (40767873 : ℕ)^4503*100000000000000^3479 ≤ 43090937291381^3479*78125000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40767873 78125000 43090937291381 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086655837/2000000000 : ℝ)^4503 ≤ (22701306690769/50000000000000 : ℝ)^3479 := by
    have hnat : (1086655837 : ℕ)^4503*50000000000000^3479 ≤ 22701306690769^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086655837 2000000000 22701306690769 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-58794541/312500000 : ℝ), (40767873/78125000 : ℝ), (1086655837/2000000000 : ℝ)] ![(1438306164081/12500000000000 : ℝ), (43090937291381/100000000000000 : ℝ), (22701306690769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-58794541/312500000 : ℝ)|^4503 ≤ (1438306164081/12500000000000 : ℝ)^3479
        have hw : |(-58794541/312500000 : ℝ)|=(58794541/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40767873/78125000 : ℝ)|^4503 ≤ (43090937291381/100000000000000 : ℝ)^3479
        have hw : |(40767873/78125000 : ℝ)|=(40767873/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086655837/2000000000 : ℝ)|^4503 ≤ (22701306690769/50000000000000 : ℝ)^3479
        have hw : |(1086655837/2000000000 : ℝ)|=(1086655837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s6_5 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295137537/10000000000 : ℝ)*x 0 + (-1776564869/10000000000 : ℝ)*x 1 + (1358319937/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295137537/10000000000 : ℝ)^4503 ≤ (10978524748451/25000000000000 : ℝ)^3479 := by
    have hnat : (5295137537 : ℕ)^4503*25000000000000^3479 ≤ 10978524748451^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295137537 10000000000 10978524748451 25000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1776564869/10000000000 : ℝ)^4503 ≤ (2136656304879/20000000000000 : ℝ)^3479 := by
    have hnat : (1776564869 : ℕ)^4503*20000000000000^3479 ≤ 2136656304879^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1776564869 10000000000 2136656304879 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358319937/2500000000 : ℝ)^4503 ≤ (45402619470941/100000000000000 : ℝ)^3479 := by
    have hnat : (1358319937 : ℕ)^4503*100000000000000^3479 ≤ 45402619470941^3479*2500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358319937 2500000000 45402619470941 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295137537/10000000000 : ℝ), (-1776564869/10000000000 : ℝ), (1358319937/2500000000 : ℝ)] ![(10978524748451/25000000000000 : ℝ), (2136656304879/20000000000000 : ℝ), (45402619470941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295137537/10000000000 : ℝ)|^4503 ≤ (10978524748451/25000000000000 : ℝ)^3479
        have hw : |(5295137537/10000000000 : ℝ)|=(5295137537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1776564869/10000000000 : ℝ)|^4503 ≤ (2136656304879/20000000000000 : ℝ)^3479
        have hw : |(-1776564869/10000000000 : ℝ)|=(1776564869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358319937/2500000000 : ℝ)|^4503 ≤ (45402619470941/100000000000000 : ℝ)^3479
        have hw : |(1358319937/2500000000 : ℝ)|=(1358319937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s6_6 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661892209/1250000000 : ℝ)*x 0 + (2716639871/5000000000 : ℝ)*x 1 + (-1776564691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661892209/1250000000 : ℝ)^4503 ≤ (5489262555367/12500000000000 : ℝ)^3479 := by
    have hnat : (661892209 : ℕ)^4503*12500000000000^3479 ≤ 5489262555367^3479*1250000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661892209 1250000000 5489262555367 12500000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716639871/5000000000 : ℝ)^4503 ≤ (9080523881209/20000000000000 : ℝ)^3479 := by
    have hnat : (2716639871 : ℕ)^4503*20000000000000^3479 ≤ 9080523881209^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716639871 5000000000 9080523881209 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1776564691/10000000000 : ℝ)^4503 ≤ (166926252171/1562500000000 : ℝ)^3479 := by
    have hnat : (1776564691 : ℕ)^4503*1562500000000^3479 ≤ 166926252171^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1776564691 10000000000 166926252171 1562500000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661892209/1250000000 : ℝ), (2716639871/5000000000 : ℝ), (-1776564691/10000000000 : ℝ)] ![(5489262555367/12500000000000 : ℝ), (9080523881209/20000000000000 : ℝ), (166926252171/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661892209/1250000000 : ℝ)|^4503 ≤ (5489262555367/12500000000000 : ℝ)^3479
        have hw : |(661892209/1250000000 : ℝ)|=(661892209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716639871/5000000000 : ℝ)|^4503 ≤ (9080523881209/20000000000000 : ℝ)^3479
        have hw : |(2716639871/5000000000 : ℝ)|=(2716639871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1776564691/10000000000 : ℝ)|^4503 ≤ (166926252171/1562500000000 : ℝ)^3479
        have hw : |(-1776564691/10000000000 : ℝ)|=(1776564691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s6_7 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534256143/1250000000 : ℝ)*x 0 + (452219539/1000000000 : ℝ)*x 1 + (403777431/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534256143/1250000000 : ℝ)^4503 ≤ (4159985017013/12500000000000 : ℝ)^3479 := by
    have hnat : (534256143 : ℕ)^4503*12500000000000^3479 ≤ 4159985017013^3479*1250000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534256143 1250000000 4159985017013 12500000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (452219539/1000000000 : ℝ)^4503 ≤ (4475233843757/12500000000000 : ℝ)^3479 := by
    have hnat : (452219539 : ℕ)^4503*12500000000000^3479 ≤ 4475233843757^3479*1000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452219539 1000000000 4475233843757 12500000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403777431/1000000000 : ℝ)^4503 ≤ (30918249096401/100000000000000 : ℝ)^3479 := by
    have hnat : (403777431 : ℕ)^4503*100000000000000^3479 ≤ 30918249096401^3479*1000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403777431 1000000000 30918249096401 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534256143/1250000000 : ℝ), (452219539/1000000000 : ℝ), (403777431/1000000000 : ℝ)] ![(4159985017013/12500000000000 : ℝ), (4475233843757/12500000000000 : ℝ), (30918249096401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534256143/1250000000 : ℝ)|^4503 ≤ (4159985017013/12500000000000 : ℝ)^3479
        have hw : |(534256143/1250000000 : ℝ)|=(534256143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(452219539/1000000000 : ℝ)|^4503 ≤ (4475233843757/12500000000000 : ℝ)^3479
        have hw : |(452219539/1000000000 : ℝ)|=(452219539/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(403777431/1000000000 : ℝ)|^4503 ≤ (30918249096401/100000000000000 : ℝ)^3479
        have hw : |(403777431/1000000000 : ℝ)|=(403777431/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1503_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h) :
    (10881/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (387/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (68/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (68/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (68/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (68/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (68/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (68/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (68/625 : ℝ) ^ (4501/1024 : ℝ) ≤ (728458468154399/12500000000000000000 : ℝ) := by
    have hpowers : (68/625 : ℝ)^4501 ≤ (728458468154399/12500000000000000000 : ℝ)^1024 := by
      have hnat : (68 : ℕ)^4501*12500000000000000000^1024 ≤ 728458468154399^1024*625^4501 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68 625 728458468154399 12500000000000000000 4501 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68/625 : ℝ)) (X := (728458468154399/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15481/100000 : ℝ) ^ (4501/1024 : ℝ) ≤ (3432932265875229/12500000000000000000 : ℝ) := by
    have hpowers : (15481/100000 : ℝ)^4501 ≤ (3432932265875229/12500000000000000000 : ℝ)^1024 := by
      have hnat : (15481 : ℕ)^4501*12500000000000000000^1024 ≤ 3432932265875229^1024*100000^4501 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15481 100000 3432932265875229 12500000000000000000 4501 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15481/100000 : ℝ)) (X := (3432932265875229/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250728458468154399/6250000000000000000 : ℝ) ≤ (5000132576386151/5000000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (6250728458468154399/6250000000000000000 : ℝ)^1024 ≤ (5000132576386151/5000000000000000 : ℝ)^4501 := by
      have hnat : (6250728458468154399 : ℕ)^1024*5000000000000000^4501 ≤ 5000132576386151^4501*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250728458468154399 6250000000000000000 5000132576386151 5000000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000132576386151/5000000000000000 : ℝ)) (X := (6250728458468154399/6250000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126040347683507407/3125000000000000000 : ℝ) ≤ (625047330774049/625000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (3126040347683507407/3125000000000000000 : ℝ)^1024 ≤ (625047330774049/625000000000000 : ℝ)^4501 := by
      have hnat : (3126040347683507407 : ℕ)^1024*625000000000000^4501 ≤ 625047330774049^4501*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126040347683507407 3125000000000000000 625047330774049 625000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625047330774049/625000000000000 : ℝ)) (X := (3126040347683507407/3125000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253432932265875229/6250000000000000000 : ℝ) ≤ (5000624715998633/5000000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (6253432932265875229/6250000000000000000 : ℝ)^1024 ≤ (5000624715998633/5000000000000000 : ℝ)^4501 := by
      have hnat : (6253432932265875229 : ℕ)^1024*5000000000000000^4501 ≤ 5000624715998633^4501*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253432932265875229 6250000000000000000 5000624715998633 5000000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000624715998633/5000000000000000 : ℝ)) (X := (6253432932265875229/6250000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(728458468154399/12500000000000000000 : ℝ) ≤ ((23000255504968876591/23005000000000000000 : ℝ)+2*(246069806241/230050000000000 : ℝ)*(68/625 : ℝ))^(4501/1024 : ℝ) := by
    rw [show (23000255504968876591/23005000000000000000 : ℝ)+2*(246069806241/230050000000000 : ℝ)*(68/625 : ℝ)=(5000132576386151/5000000000000000 : ℝ) by norm_num, show 1+2*(728458468154399/12500000000000000000 : ℝ)=(6250728458468154399/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3432932265875229/12500000000000000000 : ℝ)+(728458468154399/12500000000000000000 : ℝ) ≤ ((23000255504968876591/23005000000000000000 : ℝ)+(246069806241/230050000000000 : ℝ)*((15481/100000 : ℝ)+(68/625 : ℝ)))^(4501/1024 : ℝ) := by
    rw [show (23000255504968876591/23005000000000000000 : ℝ)+(246069806241/230050000000000 : ℝ)*((15481/100000 : ℝ)+(68/625 : ℝ))=(625047330774049/625000000000000 : ℝ) by norm_num, show 1+(3432932265875229/12500000000000000000 : ℝ)+(728458468154399/12500000000000000000 : ℝ)=(3126040347683507407/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3432932265875229/12500000000000000000 : ℝ) ≤ ((23000255504968876591/23005000000000000000 : ℝ)+2*(246069806241/230050000000000 : ℝ)*(15481/100000 : ℝ))^(4501/1024 : ℝ) := by
    rw [show (23000255504968876591/23005000000000000000 : ℝ)+2*(246069806241/230050000000000 : ℝ)*(15481/100000 : ℝ)=(5000624715998633/5000000000000000 : ℝ) by norm_num, show 1+2*(3432932265875229/12500000000000000000 : ℝ)=(6253432932265875229/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23000255504968876591/23005000000000000000 : ℝ)*(X 1 0+X 2 0)+(246069806241/230050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (68/625 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (23000255504968876591/23005000000000000000 : ℝ)) (alpha := (246069806241/230050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23000255504968876591/23005000000000000000 : ℝ)*(X 0 1+X 2 1)+(246069806241/230050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (68/625 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (23000255504968876591/23005000000000000000 : ℝ)) (alpha := (246069806241/230050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23000255504968876591/23005000000000000000 : ℝ)*(X 0 2+X 1 2)+(246069806241/230050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (68/625 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (23000255504968876591/23005000000000000000 : ℝ)) (alpha := (246069806241/230050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1881396421/10000000000 : ℝ)*X 0 0+(2717201767/5000000000 : ℝ)*X 0 1+(5217171281/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352085579/10000000000 : ℝ)*X 1 0+(-1992672671/10000000000 : ℝ)*X 1 1+(81518299/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352085403/10000000000 : ℝ)*X 2 0+(5217171293/10000000000 : ℝ)*X 2 1+(-996336349/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4273981971/10000000000 : ℝ)*X 0 0+(403524101/1000000000 : ℝ)*X 0 1+(4524711233/10000000000 : ℝ)*X 0 2+(4273981971/10000000000 : ℝ)*X 1 0+(403524101/1000000000 : ℝ)*X 1 1+(4524711233/10000000000 : ℝ)*X 1 2+(4273981971/10000000000 : ℝ)*X 2 0+(403524101/1000000000 : ℝ)*X 2 1+(4524711233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-58794541/312500000 : ℝ)*X 0 0+(40767873/78125000 : ℝ)*X 0 1+(1086655837/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295137537/10000000000 : ℝ)*X 1 0+(-1776564869/10000000000 : ℝ)*X 1 1+(1358319937/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661892209/1250000000 : ℝ)*X 2 0+(2716639871/5000000000 : ℝ)*X 2 1+(-1776564691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((534256143/1250000000 : ℝ)*X 0 0+(452219539/1000000000 : ℝ)*X 0 1+(403777431/1000000000 : ℝ)*X 0 2+(534256143/1250000000 : ℝ)*X 1 0+(452219539/1000000000 : ℝ)*X 1 1+(403777431/1000000000 : ℝ)*X 1 2+(534256143/1250000000 : ℝ)*X 2 0+(452219539/1000000000 : ℝ)*X 2 1+(403777431/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2281830270764628584085914067/575125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39842147/5000000000000 : ℝ)*(base19) + (581398139/100000000000000 : ℝ)*(base23) + (5765321/5000000000000 : ℝ)*(upper3) + (34288259/100000000000000 : ℝ)*(upper4) + (19680063/100000000000000 : ℝ)*(upper5) + (1661605969530921/50000000000000 : ℝ)*(major0) + (1661605969530921/50000000000000 : ℝ)*(major1) + (1661605969530921/50000000000000 : ℝ)*(major2) + (4603380092383433/100000000000000 : ℝ)*(sp0) + (2301694253357843/50000000000000 : ℝ)*(sp1) + (4603388722160487/100000000000000 : ℝ)*(sp2) + (255378672937197/12500000000000 : ℝ)*(sp3) + (9211175193/100000000000000 : ℝ)*(sp4) + (5058816207/100000000000000 : ℝ)*(sp7) + (1021517221156891/50000000000000 : ℝ)*(f.failure) + (2301694651779313/50000000000000 : ℝ)*(f.sum) + (15983127076131/23005000000000000000000000000 : ℝ)*base66 + (9259185314727670311/1150250000000000000000000000000000 : ℝ)*base67 + (1439677171314670311/1150250000000000000000000000000000 : ℝ)*base69 + (6828583994879170311/1150250000000000000000000000000000 : ℝ)*base71 + (17519876894731/5751250000000000000000000000 : ℝ)*base73 + (1261855517135170311/1150250000000000000000000000000000 : ℝ)*base75 + (1686002526937579689/1150250000000000000000000000000000 : ℝ)*base78 + (6232741572041579689/1150250000000000000000000000000000 : ℝ)*base80 + (14153528303927/2875625000000000000000000000 : ℝ)*base82 + (63903637/5000000000000000000000 : ℝ)*base90 + (63903637/5000000000000000000000 : ℝ)*base92 + (63903637/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2778543068256458715507260079/575125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12294039/6250000000000 : ℝ)*(base15) + (1186453/1562500000000 : ℝ)*(lower1) + (192767097/100000000000000 : ℝ)*(lower2) + (39531273/50000000000000 : ℝ)*(upper3) + (103088779/50000000000000 : ℝ)*(lower4) + (110337349/100000000000000 : ℝ)*(upper5) + (1678915330882959/50000000000000 : ℝ)*(major0) + (1678915330882959/50000000000000 : ℝ)*(major1) + (1678915330882959/50000000000000 : ℝ)*(major2) + (2869862519/100000000000000 : ℝ)*(sp2) + (581417990482033/12500000000000 : ℝ)*(sp4) + (116283593178791/2500000000000 : ℝ)*(sp5) + (930268210798749/20000000000000 : ℝ)*(sp6) + (64509913707363/3125000000000 : ℝ)*(sp7) + (64509913707363/3125000000000 : ℝ)*(f.failure) + (581417990482033/12500000000000 : ℝ)*(f.sum) + (12897923382801/5751250000000000000000000000 : ℝ)*base66 + (2841981464983812769/1150250000000000000000000000000000 : ℝ)*base67 + (4350245461597812769/1150250000000000000000000000000000 : ℝ)*base69 + (2431819881601812769/1150250000000000000000000000000000 : ℝ)*base71 + (41377634556731/5751250000000000000000000000 : ℝ)*base74 + (5254431819127812769/1150250000000000000000000000000000 : ℝ)*base75 + (6223663731772562769/1150250000000000000000000000000000 : ℝ)*base77 + (14070891694723562769/1150250000000000000000000000000000 : ℝ)*base79 + (25341568414961/23005000000000000000000000000 : ℝ)*base81 + (296259/312500000000000000000 : ℝ)*base89 + (296259/312500000000000000000 : ℝ)*base91 + (296259/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1503_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10881/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (387/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1503_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1503_box_0 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1666149907/10000000000 : ℝ)*x 0 + (675475641/1250000000 : ℝ)*x 1 + (540380447/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1666149907/10000000000 : ℝ)^4503 ≤ (9831852976819/100000000000000 : ℝ)^3479 := by
    have hnat : (1666149907 : ℕ)^4503*100000000000000^3479 ≤ 9831852976819^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1666149907 10000000000 9831852976819 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675475641/1250000000 : ℝ)^4503 ≤ (11271019263983/25000000000000 : ℝ)^3479 := by
    have hnat : (675475641 : ℕ)^4503*25000000000000^3479 ≤ 11271019263983^3479*1250000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675475641 1250000000 11271019263983 25000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540380447/1000000000 : ℝ)^4503 ≤ (9016813990079/20000000000000 : ℝ)^3479 := by
    have hnat : (540380447 : ℕ)^4503*20000000000000^3479 ≤ 9016813990079^3479*1000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540380447 1000000000 9016813990079 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1666149907/10000000000 : ℝ), (675475641/1250000000 : ℝ), (540380447/1000000000 : ℝ)] ![(9831852976819/100000000000000 : ℝ), (11271019263983/25000000000000 : ℝ), (9016813990079/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1666149907/10000000000 : ℝ)|^4503 ≤ (9831852976819/100000000000000 : ℝ)^3479
        have hw : |(-1666149907/10000000000 : ℝ)|=(1666149907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675475641/1250000000 : ℝ)|^4503 ≤ (11271019263983/25000000000000 : ℝ)^3479
        have hw : |(675475641/1250000000 : ℝ)|=(675475641/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540380447/1000000000 : ℝ)|^4503 ≤ (9016813990079/20000000000000 : ℝ)^3479
        have hw : |(540380447/1000000000 : ℝ)|=(540380447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_box_1 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270651767/10000000000 : ℝ)*x 0 + (-1850785843/10000000000 : ℝ)*x 1 + (2701902091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270651767/10000000000 : ℝ)^4503 ≤ (1091286003589/2500000000000 : ℝ)^3479 := by
    have hnat : (5270651767 : ℕ)^4503*2500000000000^3479 ≤ 1091286003589^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270651767 10000000000 1091286003589 2500000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1850785843/10000000000 : ℝ)^4503 ≤ (11264492998269/100000000000000 : ℝ)^3479 := by
    have hnat : (1850785843 : ℕ)^4503*100000000000000^3479 ≤ 11264492998269^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1850785843 10000000000 11264492998269 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701902091/5000000000 : ℝ)^4503 ≤ (45084066840373/100000000000000 : ℝ)^3479 := by
    have hnat : (2701902091 : ℕ)^4503*100000000000000^3479 ≤ 45084066840373^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701902091 5000000000 45084066840373 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270651767/10000000000 : ℝ), (-1850785843/10000000000 : ℝ), (2701902091/5000000000 : ℝ)] ![(1091286003589/2500000000000 : ℝ), (11264492998269/100000000000000 : ℝ), (45084066840373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270651767/10000000000 : ℝ)|^4503 ≤ (1091286003589/2500000000000 : ℝ)^3479
        have hw : |(5270651767/10000000000 : ℝ)|=(5270651767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1850785843/10000000000 : ℝ)|^4503 ≤ (11264492998269/100000000000000 : ℝ)^3479
        have hw : |(-1850785843/10000000000 : ℝ)|=(1850785843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701902091/5000000000 : ℝ)|^4503 ≤ (45084066840373/100000000000000 : ℝ)^3479
        have hw : |(2701902091/5000000000 : ℝ)|=(2701902091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_box_2 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (6588317/12500000 : ℝ)*x 0 + (5403803317/10000000000 : ℝ)*x 1 + (-370156907/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6588317/12500000 : ℝ)^4503 ≤ (10912864948183/25000000000000 : ℝ)^3479 := by
    have hnat : (6588317 : ℕ)^4503*25000000000000^3479 ≤ 10912864948183^3479*12500000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6588317 12500000 10912864948183 25000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403803317/10000000000 : ℝ)^4503 ≤ (11271014374877/25000000000000 : ℝ)^3479 := by
    have hnat : (5403803317 : ℕ)^4503*25000000000000^3479 ≤ 11271014374877^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403803317 10000000000 11271014374877 25000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (370156907/2000000000 : ℝ)^4503 ≤ (5632241347077/50000000000000 : ℝ)^3479 := by
    have hnat : (370156907 : ℕ)^4503*50000000000000^3479 ≤ 5632241347077^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370156907 2000000000 5632241347077 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6588317/12500000 : ℝ), (5403803317/10000000000 : ℝ), (-370156907/2000000000 : ℝ)] ![(10912864948183/25000000000000 : ℝ), (11271014374877/25000000000000 : ℝ), (5632241347077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6588317/12500000 : ℝ)|^4503 ≤ (10912864948183/25000000000000 : ℝ)^3479
        have hw : |(6588317/12500000 : ℝ)|=(6588317/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403803317/10000000000 : ℝ)|^4503 ≤ (11271014374877/25000000000000 : ℝ)^3479
        have hw : |(5403803317/10000000000 : ℝ)|=(5403803317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-370156907/2000000000 : ℝ)|^4503 ≤ (5632241347077/50000000000000 : ℝ)^3479
        have hw : |(-370156907/2000000000 : ℝ)|=(370156907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_box_3 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2238729461/5000000000 : ℝ)*x 0 + (4179283703/10000000000 : ℝ)*x 1 + (835857067/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2238729461/5000000000 : ℝ)^4503 ≤ (276125918399/781250000000 : ℝ)^3479 := by
    have hnat : (2238729461 : ℕ)^4503*781250000000^3479 ≤ 276125918399^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238729461 5000000000 276125918399 781250000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4179283703/10000000000 : ℝ)^4503 ≤ (8081983260301/25000000000000 : ℝ)^3479 := by
    have hnat : (4179283703 : ℕ)^4503*25000000000000^3479 ≤ 8081983260301^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4179283703 10000000000 8081983260301 25000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (835857067/2000000000 : ℝ)^4503 ≤ (32327949380893/100000000000000 : ℝ)^3479 := by
    have hnat : (835857067 : ℕ)^4503*100000000000000^3479 ≤ 32327949380893^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835857067 2000000000 32327949380893 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2238729461/5000000000 : ℝ), (4179283703/10000000000 : ℝ), (835857067/2000000000 : ℝ)] ![(276125918399/781250000000 : ℝ), (8081983260301/25000000000000 : ℝ), (32327949380893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2238729461/5000000000 : ℝ)|^4503 ≤ (276125918399/781250000000 : ℝ)^3479
        have hw : |(2238729461/5000000000 : ℝ)|=(2238729461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4179283703/10000000000 : ℝ)|^4503 ≤ (8081983260301/25000000000000 : ℝ)^3479
        have hw : |(4179283703/10000000000 : ℝ)|=(4179283703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(835857067/2000000000 : ℝ)|^4503 ≤ (32327949380893/100000000000000 : ℝ)^3479
        have hw : |(835857067/2000000000 : ℝ)|=(835857067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_box_4 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2102089757/10000000000 : ℝ)*x 0 + (1310830861/2500000000 : ℝ)*x 1 + (1048664737/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102089757/10000000000 : ℝ)^4503 ≤ (6641285586529/50000000000000 : ℝ)^3479 := by
    have hnat : (2102089757 : ℕ)^4503*50000000000000^3479 ≤ 6641285586529^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102089757 10000000000 6641285586529 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310830861/2500000000 : ℝ)^4503 ≤ (10839678278683/25000000000000 : ℝ)^3479 := by
    have hnat : (1310830861 : ℕ)^4503*25000000000000^3479 ≤ 10839678278683^3479*2500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310830861 2500000000 10839678278683 25000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048664737/2000000000 : ℝ)^4503 ≤ (1734348627769/4000000000000 : ℝ)^3479 := by
    have hnat : (1048664737 : ℕ)^4503*4000000000000^3479 ≤ 1734348627769^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048664737 2000000000 1734348627769 4000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2102089757/10000000000 : ℝ), (1310830861/2500000000 : ℝ), (1048664737/2000000000 : ℝ)] ![(6641285586529/50000000000000 : ℝ), (10839678278683/25000000000000 : ℝ), (1734348627769/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2102089757/10000000000 : ℝ)|^4503 ≤ (6641285586529/50000000000000 : ℝ)^3479
        have hw : |(-2102089757/10000000000 : ℝ)|=(2102089757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310830861/2500000000 : ℝ)|^4503 ≤ (10839678278683/25000000000000 : ℝ)^3479
        have hw : |(1310830861/2500000000 : ℝ)|=(1310830861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048664737/2000000000 : ℝ)|^4503 ≤ (1734348627769/4000000000000 : ℝ)^3479
        have hw : |(1048664737/2000000000 : ℝ)|=(1048664737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_box_5 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345615083/2500000000 : ℝ)*x 0 + (-958420567/5000000000 : ℝ)*x 1 + (5243323429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345615083/2500000000 : ℝ)^4503 ≤ (44853715362377/100000000000000 : ℝ)^3479 := by
    have hnat : (1345615083 : ℕ)^4503*100000000000000^3479 ≤ 44853715362377^3479*2500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345615083 2500000000 44853715362377 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (958420567/5000000000 : ℝ)^4503 ≤ (2357514333267/20000000000000 : ℝ)^3479 := by
    have hnat : (958420567 : ℕ)^4503*20000000000000^3479 ≤ 2357514333267^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958420567 5000000000 2357514333267 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243323429/10000000000 : ℝ)^4503 ≤ (43358712954183/100000000000000 : ℝ)^3479 := by
    have hnat : (5243323429 : ℕ)^4503*100000000000000^3479 ≤ 43358712954183^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243323429 10000000000 43358712954183 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345615083/2500000000 : ℝ), (-958420567/5000000000 : ℝ), (5243323429/10000000000 : ℝ)] ![(44853715362377/100000000000000 : ℝ), (2357514333267/20000000000000 : ℝ), (43358712954183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345615083/2500000000 : ℝ)|^4503 ≤ (44853715362377/100000000000000 : ℝ)^3479
        have hw : |(1345615083/2500000000 : ℝ)|=(1345615083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-958420567/5000000000 : ℝ)|^4503 ≤ (2357514333267/20000000000000 : ℝ)^3479
        have hw : |(-958420567/5000000000 : ℝ)|=(958420567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243323429/10000000000 : ℝ)|^4503 ≤ (43358712954183/100000000000000 : ℝ)^3479
        have hw : |(5243323429/10000000000 : ℝ)|=(5243323429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_box_6 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345615109/2500000000 : ℝ)*x 0 + (1310830879/2500000000 : ℝ)*x 1 + (-1916840877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345615109/2500000000 : ℝ)^4503 ≤ (22426858242067/50000000000000 : ℝ)^3479 := by
    have hnat : (1345615109 : ℕ)^4503*50000000000000^3479 ≤ 22426858242067^3479*2500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345615109 2500000000 22426858242067 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310830879/2500000000 : ℝ)^4503 ≤ (43358713885369/100000000000000 : ℝ)^3479 := by
    have hnat : (1310830879 : ℕ)^4503*100000000000000^3479 ≤ 43358713885369^3479*2500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310830879 2500000000 43358713885369 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1916840877/10000000000 : ℝ)^4503 ≤ (11787569620743/100000000000000 : ℝ)^3479 := by
    have hnat : (1916840877 : ℕ)^4503*100000000000000^3479 ≤ 11787569620743^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916840877 10000000000 11787569620743 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345615109/2500000000 : ℝ), (1310830879/2500000000 : ℝ), (-1916840877/10000000000 : ℝ)] ![(22426858242067/50000000000000 : ℝ), (43358713885369/100000000000000 : ℝ), (11787569620743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345615109/2500000000 : ℝ)|^4503 ≤ (22426858242067/50000000000000 : ℝ)^3479
        have hw : |(1345615109/2500000000 : ℝ)|=(1345615109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310830879/2500000000 : ℝ)|^4503 ≤ (43358713885369/100000000000000 : ℝ)^3479
        have hw : |(1310830879/2500000000 : ℝ)|=(1310830879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1916840877/10000000000 : ℝ)|^4503 ≤ (11787569620743/100000000000000 : ℝ)^3479
        have hw : |(-1916840877/10000000000 : ℝ)|=(1916840877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_box_7 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4068132417/10000000000 : ℝ)*x 0 + (4383812091/10000000000 : ℝ)*x 1 + (4383812549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4068132417/10000000000 : ℝ)^4503 ≤ (1951216414691/6250000000000 : ℝ)^3479 := by
    have hnat : (4068132417 : ℕ)^4503*6250000000000^3479 ≤ 1951216414691^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4068132417 10000000000 1951216414691 6250000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4383812091/10000000000 : ℝ)^4503 ≤ (17195133173271/50000000000000 : ℝ)^3479 := by
    have hnat : (4383812091 : ℕ)^4503*50000000000000^3479 ≤ 17195133173271^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4383812091 10000000000 17195133173271 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4383812549/10000000000 : ℝ)^4503 ≤ (34390270997009/100000000000000 : ℝ)^3479 := by
    have hnat : (4383812549 : ℕ)^4503*100000000000000^3479 ≤ 34390270997009^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4383812549 10000000000 34390270997009 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4068132417/10000000000 : ℝ), (4383812091/10000000000 : ℝ), (4383812549/10000000000 : ℝ)] ![(1951216414691/6250000000000 : ℝ), (17195133173271/50000000000000 : ℝ), (34390270997009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4068132417/10000000000 : ℝ)|^4503 ≤ (1951216414691/6250000000000 : ℝ)^3479
        have hw : |(4068132417/10000000000 : ℝ)|=(4068132417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4383812091/10000000000 : ℝ)|^4503 ≤ (17195133173271/50000000000000 : ℝ)^3479
        have hw : |(4383812091/10000000000 : ℝ)|=(4383812091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4383812549/10000000000 : ℝ)|^4503 ≤ (34390270997009/100000000000000 : ℝ)^3479
        have hw : |(4383812549/10000000000 : ℝ)|=(4383812549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_box_8 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-502503399/2500000000 : ℝ)*x 0 + (2565497109/5000000000 : ℝ)*x 1 + (2712142021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502503399/2500000000 : ℝ)^4503 ≤ (12534423433921/100000000000000 : ℝ)^3479 := by
    have hnat : (502503399 : ℕ)^4503*100000000000000^3479 ≤ 12534423433921^3479*2500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502503399 2500000000 12534423433921 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2565497109/5000000000 : ℝ)^4503 ≤ (5270028856599/12500000000000 : ℝ)^3479 := by
    have hnat : (2565497109 : ℕ)^4503*12500000000000^3479 ≤ 5270028856599^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565497109 5000000000 5270028856599 12500000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712142021/5000000000 : ℝ)^4503 ≤ (9061069140571/20000000000000 : ℝ)^3479 := by
    have hnat : (2712142021 : ℕ)^4503*20000000000000^3479 ≤ 9061069140571^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712142021 5000000000 9061069140571 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-502503399/2500000000 : ℝ), (2565497109/5000000000 : ℝ), (2712142021/5000000000 : ℝ)] ![(12534423433921/100000000000000 : ℝ), (5270028856599/12500000000000 : ℝ), (9061069140571/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-502503399/2500000000 : ℝ)|^4503 ≤ (12534423433921/100000000000000 : ℝ)^3479
        have hw : |(-502503399/2500000000 : ℝ)|=(502503399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2565497109/5000000000 : ℝ)|^4503 ≤ (5270028856599/12500000000000 : ℝ)^3479
        have hw : |(2565497109/5000000000 : ℝ)|=(2565497109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712142021/5000000000 : ℝ)|^4503 ≤ (9061069140571/20000000000000 : ℝ)^3479
        have hw : |(2712142021/5000000000 : ℝ)|=(2712142021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_box_9 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628188611/5000000000 : ℝ)*x 0 + (-1842107459/10000000000 : ℝ)*x 1 + (1356070957/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628188611/5000000000 : ℝ)^4503 ≤ (43498482635269/100000000000000 : ℝ)^3479 := by
    have hnat : (2628188611 : ℕ)^4503*100000000000000^3479 ≤ 43498482635269^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628188611 5000000000 43498482635269 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1842107459/10000000000 : ℝ)^4503 ≤ (5598086981143/50000000000000 : ℝ)^3479 := by
    have hnat : (1842107459 : ℕ)^4503*50000000000000^3479 ≤ 5598086981143^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842107459 10000000000 5598086981143 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356070957/2500000000 : ℝ)^4503 ≤ (22652671694681/50000000000000 : ℝ)^3479 := by
    have hnat : (1356070957 : ℕ)^4503*50000000000000^3479 ≤ 22652671694681^3479*2500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356070957 2500000000 22652671694681 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628188611/5000000000 : ℝ), (-1842107459/10000000000 : ℝ), (1356070957/2500000000 : ℝ)] ![(43498482635269/100000000000000 : ℝ), (5598086981143/50000000000000 : ℝ), (22652671694681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628188611/5000000000 : ℝ)|^4503 ≤ (43498482635269/100000000000000 : ℝ)^3479
        have hw : |(2628188611/5000000000 : ℝ)|=(2628188611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1842107459/10000000000 : ℝ)|^4503 ≤ (5598086981143/50000000000000 : ℝ)^3479
        have hw : |(-1842107459/10000000000 : ℝ)|=(1842107459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356070957/2500000000 : ℝ)|^4503 ≤ (22652671694681/50000000000000 : ℝ)^3479
        have hw : |(1356070957/2500000000 : ℝ)|=(1356070957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_box_10 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164261779/312500000 : ℝ)*x 0 + (5424284963/10000000000 : ℝ)*x 1 + (-18421063/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164261779/312500000 : ℝ)^4503 ≤ (21749239743099/50000000000000 : ℝ)^3479 := by
    have hnat : (164261779 : ℕ)^4503*50000000000000^3479 ≤ 21749239743099^3479*312500000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164261779 312500000 21749239743099 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424284963/10000000000 : ℝ)^4503 ≤ (45305355659527/100000000000000 : ℝ)^3479 := by
    have hnat : (5424284963 : ℕ)^4503*100000000000000^3479 ≤ 45305355659527^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424284963 10000000000 45305355659527 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18421063/100000000 : ℝ)^4503 ≤ (11196164844579/100000000000000 : ℝ)^3479 := by
    have hnat : (18421063 : ℕ)^4503*100000000000000^3479 ≤ 11196164844579^3479*100000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18421063 100000000 11196164844579 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164261779/312500000 : ℝ), (5424284963/10000000000 : ℝ), (-18421063/100000000 : ℝ)] ![(21749239743099/50000000000000 : ℝ), (45305355659527/100000000000000 : ℝ), (11196164844579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164261779/312500000 : ℝ)|^4503 ≤ (21749239743099/50000000000000 : ℝ)^3479
        have hw : |(164261779/312500000 : ℝ)|=(164261779/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424284963/10000000000 : ℝ)|^4503 ≤ (45305355659527/100000000000000 : ℝ)^3479
        have hw : |(5424284963/10000000000 : ℝ)|=(5424284963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18421063/100000000 : ℝ)|^4503 ≤ (11196164844579/100000000000000 : ℝ)^3479
        have hw : |(-18421063/100000000 : ℝ)|=(18421063/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_box_11 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4528539487/10000000000 : ℝ)*x 0 + (830630703/2000000000 : ℝ)*x 1 + (415315279/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4528539487/10000000000 : ℝ)^4503 ≤ (560420206313/1562500000000 : ℝ)^3479 := by
    have hnat : (4528539487 : ℕ)^4503*1562500000000^3479 ≤ 560420206313^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528539487 10000000000 560420206313 1562500000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (830630703/2000000000 : ℝ)^4503 ≤ (32066557015897/100000000000000 : ℝ)^3479 := by
    have hnat : (830630703 : ℕ)^4503*100000000000000^3479 ≤ 32066557015897^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830630703 2000000000 32066557015897 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415315279/1000000000 : ℝ)^4503 ≤ (32066549770539/100000000000000 : ℝ)^3479 := by
    have hnat : (415315279 : ℕ)^4503*100000000000000^3479 ≤ 32066549770539^3479*1000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415315279 1000000000 32066549770539 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4528539487/10000000000 : ℝ), (830630703/2000000000 : ℝ), (415315279/1000000000 : ℝ)] ![(560420206313/1562500000000 : ℝ), (32066557015897/100000000000000 : ℝ), (32066549770539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4528539487/10000000000 : ℝ)|^4503 ≤ (560420206313/1562500000000 : ℝ)^3479
        have hw : |(4528539487/10000000000 : ℝ)|=(4528539487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(830630703/2000000000 : ℝ)|^4503 ≤ (32066557015897/100000000000000 : ℝ)^3479
        have hw : |(830630703/2000000000 : ℝ)|=(830630703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(415315279/1000000000 : ℝ)|^4503 ≤ (32066549770539/100000000000000 : ℝ)^3479
        have hw : |(415315279/1000000000 : ℝ)|=(415315279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_box_12 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-351644929/2000000000 : ℝ)*x 0 + (5512492491/10000000000 : ℝ)*x 1 + (5228305083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (351644929/2000000000 : ℝ)^4503 ≤ (5270374524663/50000000000000 : ℝ)^3479 := by
    have hnat : (351644929 : ℕ)^4503*50000000000000^3479 ≤ 5270374524663^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351644929 2000000000 5270374524663 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5512492491/10000000000 : ℝ)^4503 ≤ (46261215881371/100000000000000 : ℝ)^3479 := by
    have hnat : (5512492491 : ℕ)^4503*100000000000000^3479 ≤ 46261215881371^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512492491 10000000000 46261215881371 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228305083/10000000000 : ℝ)^4503 ≤ (21599017530763/50000000000000 : ℝ)^3479 := by
    have hnat : (5228305083 : ℕ)^4503*50000000000000^3479 ≤ 21599017530763^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228305083 10000000000 21599017530763 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-351644929/2000000000 : ℝ), (5512492491/10000000000 : ℝ), (5228305083/10000000000 : ℝ)] ![(5270374524663/50000000000000 : ℝ), (46261215881371/100000000000000 : ℝ), (21599017530763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-351644929/2000000000 : ℝ)|^4503 ≤ (5270374524663/50000000000000 : ℝ)^3479
        have hw : |(-351644929/2000000000 : ℝ)|=(351644929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5512492491/10000000000 : ℝ)|^4503 ≤ (46261215881371/100000000000000 : ℝ)^3479
        have hw : |(5512492491/10000000000 : ℝ)|=(5512492491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228305083/10000000000 : ℝ)|^4503 ≤ (21599017530763/50000000000000 : ℝ)^3479
        have hw : |(5228305083/10000000000 : ℝ)|=(5228305083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_box_13 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348230823/2500000000 : ℝ)*x 0 + (-120177667/625000000 : ℝ)*x 1 + (2614152527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348230823/2500000000 : ℝ)^4503 ≤ (8993320467557/20000000000000 : ℝ)^3479 := by
    have hnat : (1348230823 : ℕ)^4503*20000000000000^3479 ≤ 8993320467557^3479*2500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348230823 2500000000 8993320467557 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (120177667/625000000 : ℝ)^4503 ≤ (11835362898139/100000000000000 : ℝ)^3479 := by
    have hnat : (120177667 : ℕ)^4503*100000000000000^3479 ≤ 11835362898139^3479*625000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120177667 625000000 11835362898139 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614152527/5000000000 : ℝ)^4503 ≤ (1349938585981/3125000000000 : ℝ)^3479 := by
    have hnat : (2614152527 : ℕ)^4503*3125000000000^3479 ≤ 1349938585981^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614152527 5000000000 1349938585981 3125000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348230823/2500000000 : ℝ), (-120177667/625000000 : ℝ), (2614152527/5000000000 : ℝ)] ![(8993320467557/20000000000000 : ℝ), (11835362898139/100000000000000 : ℝ), (1349938585981/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348230823/2500000000 : ℝ)|^4503 ≤ (8993320467557/20000000000000 : ℝ)^3479
        have hw : |(1348230823/2500000000 : ℝ)|=(1348230823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-120177667/625000000 : ℝ)|^4503 ≤ (11835362898139/100000000000000 : ℝ)^3479
        have hw : |(-120177667/625000000 : ℝ)|=(120177667/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614152527/5000000000 : ℝ)|^4503 ≤ (1349938585981/3125000000000 : ℝ)^3479
        have hw : |(2614152527/5000000000 : ℝ)|=(2614152527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_box_14 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392923337/10000000000 : ℝ)*x 0 + (653538117/1250000000 : ℝ)*x 1 + (-1922842769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392923337/10000000000 : ℝ)^4503 ≤ (44966602823437/100000000000000 : ℝ)^3479 := by
    have hnat : (5392923337 : ℕ)^4503*100000000000000^3479 ≤ 44966602823437^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392923337 10000000000 44966602823437 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653538117/1250000000 : ℝ)^4503 ≤ (4319803348947/10000000000000 : ℝ)^3479 := by
    have hnat : (653538117 : ℕ)^4503*10000000000000^3479 ≤ 4319803348947^3479*1250000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653538117 1250000000 4319803348947 10000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1922842769/10000000000 : ℝ)^4503 ≤ (11835363670921/100000000000000 : ℝ)^3479 := by
    have hnat : (1922842769 : ℕ)^4503*100000000000000^3479 ≤ 11835363670921^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922842769 10000000000 11835363670921 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392923337/10000000000 : ℝ), (653538117/1250000000 : ℝ), (-1922842769/10000000000 : ℝ)] ![(44966602823437/100000000000000 : ℝ), (4319803348947/10000000000000 : ℝ), (11835363670921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392923337/10000000000 : ℝ)|^4503 ≤ (44966602823437/100000000000000 : ℝ)^3479
        have hw : |(5392923337/10000000000 : ℝ)|=(5392923337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(653538117/1250000000 : ℝ)|^4503 ≤ (4319803348947/10000000000000 : ℝ)^3479
        have hw : |(653538117/1250000000 : ℝ)|=(653538117/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1922842769/10000000000 : ℝ)|^4503 ≤ (11835363670921/100000000000000 : ℝ)^3479
        have hw : |(-1922842769/10000000000 : ℝ)|=(1922842769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_box_15 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1007241491/2500000000 : ℝ)*x 0 + (4402929879/10000000000 : ℝ)*x 1 + (137591567/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1007241491/2500000000 : ℝ)^4503 ≤ (7707744259843/25000000000000 : ℝ)^3479 := by
    have hnat : (1007241491 : ℕ)^4503*25000000000000^3479 ≤ 7707744259843^3479*2500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007241491 2500000000 7707744259843 25000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4402929879/10000000000 : ℝ)^4503 ≤ (4323063766067/12500000000000 : ℝ)^3479 := by
    have hnat : (4402929879 : ℕ)^4503*12500000000000^3479 ≤ 4323063766067^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4402929879 10000000000 4323063766067 12500000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137591567/312500000 : ℝ)^4503 ≤ (34584512822757/100000000000000 : ℝ)^3479 := by
    have hnat : (137591567 : ℕ)^4503*100000000000000^3479 ≤ 34584512822757^3479*312500000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137591567 312500000 34584512822757 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1007241491/2500000000 : ℝ), (4402929879/10000000000 : ℝ), (137591567/312500000 : ℝ)] ![(7707744259843/25000000000000 : ℝ), (4323063766067/12500000000000 : ℝ), (34584512822757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1007241491/2500000000 : ℝ)|^4503 ≤ (7707744259843/25000000000000 : ℝ)^3479
        have hw : |(1007241491/2500000000 : ℝ)|=(1007241491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4402929879/10000000000 : ℝ)|^4503 ≤ (4323063766067/12500000000000 : ℝ)^3479
        have hw : |(4402929879/10000000000 : ℝ)|=(4402929879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(137591567/312500000 : ℝ)|^4503 ≤ (34584512822757/100000000000000 : ℝ)^3479
        have hw : |(137591567/312500000 : ℝ)|=(137591567/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1503_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10881/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3983/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11717/20000 : ℝ) ∧ (40111/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10743/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10881/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10881/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10881/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10881/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10881/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10881/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10881/100000 : ℝ) ^ (4501/1024 : ℝ) ≤ (583002248388769/10000000000000000000 : ℝ) := by
    have hpowers : (10881/100000 : ℝ)^4501 ≤ (583002248388769/10000000000000000000 : ℝ)^1024 := by
      have hnat : (10881 : ℕ)^4501*10000000000000000000^1024 ≤ 583002248388769^1024*100000^4501 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10881 100000 583002248388769 10000000000000000000 4501 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10881/100000 : ℝ)) (X := (583002248388769/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (387/2500 : ℝ) ^ (4501/1024 : ℝ) ≤ (27455661304645333/100000000000000000000 : ℝ) := by
    have hpowers : (387/2500 : ℝ)^4501 ≤ (27455661304645333/100000000000000000000 : ℝ)^1024 := by
      have hnat : (387 : ℕ)^4501*100000000000000000000^1024 ≤ 27455661304645333^1024*2500^4501 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        387 2500 27455661304645333 100000000000000000000 4501 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (387/2500 : ℝ)) (X := (27455661304645333/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000583002248388769/5000000000000000000 : ℝ) ≤ (10000265259905617/10000000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (5000583002248388769/5000000000000000000 : ℝ)^1024 ≤ (10000265259905617/10000000000000000 : ℝ)^4501 := by
      have hnat : (5000583002248388769 : ℕ)^1024*10000000000000000^4501 ≤ 10000265259905617^4501*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000583002248388769 5000000000000000000 10000265259905617 10000000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000265259905617/10000000000000000 : ℝ)) (X := (5000583002248388769/5000000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100033285683788533023/100000000000000000000 : ℝ) ≤ (1250094646075811/1250000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (100033285683788533023/100000000000000000000 : ℝ)^1024 ≤ (1250094646075811/1250000000000000 : ℝ)^4501 := by
      have hnat : (100033285683788533023 : ℕ)^1024*1250000000000000^4501 ≤ 1250094646075811^4501*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100033285683788533023 100000000000000000000 1250094646075811 1250000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250094646075811/1250000000000000 : ℝ)) (X := (100033285683788533023/100000000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027455661304645333/50000000000000000000 : ℝ) ≤ (10001249077307359/10000000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (50027455661304645333/50000000000000000000 : ℝ)^1024 ≤ (10001249077307359/10000000000000000 : ℝ)^4501 := by
      have hnat : (50027455661304645333 : ℕ)^1024*10000000000000000^4501 ≤ 10001249077307359^4501*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027455661304645333 50000000000000000000 10001249077307359 10000000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001249077307359/10000000000000000 : ℝ)) (X := (50027455661304645333/50000000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(583002248388769/10000000000000000000 : ℝ) ≤ ((729849444653294887/730000000000000000 : ℝ)+2*(7808074617/7300000000000 : ℝ)*(10881/100000 : ℝ))^(4501/1024 : ℝ) := by
    rw [show (729849444653294887/730000000000000000 : ℝ)+2*(7808074617/7300000000000 : ℝ)*(10881/100000 : ℝ)=(10000265259905617/10000000000000000 : ℝ) by norm_num, show 1+2*(583002248388769/10000000000000000000 : ℝ)=(5000583002248388769/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27455661304645333/100000000000000000000 : ℝ)+(583002248388769/10000000000000000000 : ℝ) ≤ ((729849444653294887/730000000000000000 : ℝ)+(7808074617/7300000000000 : ℝ)*((387/2500 : ℝ)+(10881/100000 : ℝ)))^(4501/1024 : ℝ) := by
    rw [show (729849444653294887/730000000000000000 : ℝ)+(7808074617/7300000000000 : ℝ)*((387/2500 : ℝ)+(10881/100000 : ℝ))=(1250094646075811/1250000000000000 : ℝ) by norm_num, show 1+(27455661304645333/100000000000000000000 : ℝ)+(583002248388769/10000000000000000000 : ℝ)=(100033285683788533023/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27455661304645333/100000000000000000000 : ℝ) ≤ ((729849444653294887/730000000000000000 : ℝ)+2*(7808074617/7300000000000 : ℝ)*(387/2500 : ℝ))^(4501/1024 : ℝ) := by
    rw [show (729849444653294887/730000000000000000 : ℝ)+2*(7808074617/7300000000000 : ℝ)*(387/2500 : ℝ)=(10001249077307359/10000000000000000 : ℝ) by norm_num, show 1+2*(27455661304645333/100000000000000000000 : ℝ)=(50027455661304645333/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (729849444653294887/730000000000000000 : ℝ)*(X 1 0+X 2 0)+(7808074617/7300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (10881/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (729849444653294887/730000000000000000 : ℝ)) (alpha := (7808074617/7300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (729849444653294887/730000000000000000 : ℝ)*(X 0 1+X 2 1)+(7808074617/7300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (10881/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (729849444653294887/730000000000000000 : ℝ)) (alpha := (7808074617/7300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (729849444653294887/730000000000000000 : ℝ)*(X 0 2+X 1 2)+(7808074617/7300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (10881/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (729849444653294887/730000000000000000 : ℝ)) (alpha := (7808074617/7300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1666149907/10000000000 : ℝ)*X 0 0+(675475641/1250000000 : ℝ)*X 0 1+(540380447/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270651767/10000000000 : ℝ)*X 1 0+(-1850785843/10000000000 : ℝ)*X 1 1+(2701902091/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((6588317/12500000 : ℝ)*X 2 0+(5403803317/10000000000 : ℝ)*X 2 1+(-370156907/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2238729461/5000000000 : ℝ)*X 0 0+(4179283703/10000000000 : ℝ)*X 0 1+(835857067/2000000000 : ℝ)*X 0 2+(2238729461/5000000000 : ℝ)*X 1 0+(4179283703/10000000000 : ℝ)*X 1 1+(835857067/2000000000 : ℝ)*X 1 2+(2238729461/5000000000 : ℝ)*X 2 0+(4179283703/10000000000 : ℝ)*X 2 1+(835857067/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2102089757/10000000000 : ℝ)*X 0 0+(1310830861/2500000000 : ℝ)*X 0 1+(1048664737/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1345615083/2500000000 : ℝ)*X 1 0+(-958420567/5000000000 : ℝ)*X 1 1+(5243323429/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1345615109/2500000000 : ℝ)*X 2 0+(1310830879/2500000000 : ℝ)*X 2 1+(-1916840877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4068132417/10000000000 : ℝ)*X 0 0+(4383812091/10000000000 : ℝ)*X 0 1+(4383812549/10000000000 : ℝ)*X 0 2+(4068132417/10000000000 : ℝ)*X 1 0+(4383812091/10000000000 : ℝ)*X 1 1+(4383812549/10000000000 : ℝ)*X 1 2+(4068132417/10000000000 : ℝ)*X 2 0+(4383812091/10000000000 : ℝ)*X 2 1+(4383812549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-502503399/2500000000 : ℝ)*X 0 0+(2565497109/5000000000 : ℝ)*X 0 1+(2712142021/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628188611/5000000000 : ℝ)*X 1 0+(-1842107459/10000000000 : ℝ)*X 1 1+(1356070957/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((164261779/312500000 : ℝ)*X 2 0+(5424284963/10000000000 : ℝ)*X 2 1+(-18421063/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4528539487/10000000000 : ℝ)*X 0 0+(830630703/2000000000 : ℝ)*X 0 1+(415315279/1000000000 : ℝ)*X 0 2+(4528539487/10000000000 : ℝ)*X 1 0+(830630703/2000000000 : ℝ)*X 1 1+(415315279/1000000000 : ℝ)*X 1 2+(4528539487/10000000000 : ℝ)*X 2 0+(830630703/2000000000 : ℝ)*X 2 1+(415315279/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-351644929/2000000000 : ℝ)*X 0 0+(5512492491/10000000000 : ℝ)*X 0 1+(5228305083/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1348230823/2500000000 : ℝ)*X 1 0+(-120177667/625000000 : ℝ)*X 1 1+(2614152527/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5392923337/10000000000 : ℝ)*X 2 0+(653538117/1250000000 : ℝ)*X 2 1+(-1922842769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1007241491/2500000000 : ℝ)*X 0 0+(4402929879/10000000000 : ℝ)*X 0 1+(137591567/312500000 : ℝ)*X 0 2+(1007241491/2500000000 : ℝ)*X 1 0+(4402929879/10000000000 : ℝ)*X 1 1+(137591567/312500000 : ℝ)*X 1 2+(1007241491/2500000000 : ℝ)*X 2 0+(4402929879/10000000000 : ℝ)*X 2 1+(137591567/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3983/6250 : ℝ) ≤ (-23259745138949134254023558473323/36500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8946717/50000000000000 : ℝ)*(upper0) + (113637/3125000000000 : ℝ)*(lower1) + (35263069/100000000000000 : ℝ)*(lower2) + (19754089/25000000000000 : ℝ)*(lower3) + (39031061/100000000000000 : ℝ)*(upper5) + (2210119911647019/100000000000000 : ℝ)*(major0) + (2210119911647019/100000000000000 : ℝ)*(major1) + (2210119911647019/100000000000000 : ℝ)*(major2) + (110245117/50000000000000 : ℝ)*(sp1) + (1541375296834459/50000000000000 : ℝ)*(sp4) + (770687593294671/25000000000000 : ℝ)*(sp5) + (3082749889090673/100000000000000 : ℝ)*(sp6) + (679365503003859/50000000000000 : ℝ)*(sp7) + (140915649/20000000000000 : ℝ)*(sp14) + (679365503003859/50000000000000 : ℝ)*(f.failure) + (1541375296834459/50000000000000 : ℝ)*(f.sum) + (764668723477/365000000000000000000000000 : ℝ)*base66 + (102267343956208147/73000000000000000000000000000000 : ℝ)*base68 + (33300161942208147/73000000000000000000000000000000 : ℝ)*base70 + (240162084022208147/73000000000000000000000000000000 : ℝ)*base72 + (1203903318423/365000000000000000000000000 : ℝ)*base73 + (529862455104208147/73000000000000000000000000000000 : ℝ)*base76 + (300446245193208147/73000000000000000000000000000000 : ℝ)*base78 + (686659353664208147/73000000000000000000000000000000 : ℝ)*base80 + (337447566217/365000000000000000000000000 : ℝ)*base82 + (36228387/5000000000000000000000 : ℝ)*base89 + (36228387/5000000000000000000000 : ℝ)*base91 + (36228387/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (11717/20000 : ℝ) ≤ (2673070717964909495884410701823/4562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56810941/10000000000000 : ℝ)*(lower1) + (57117203/100000000000000 : ℝ)*(lower2) + (159848539/25000000000000 : ℝ)*(upper4) + (285718599432519/12500000000000 : ℝ)*(major0) + (285718599432519/12500000000000 : ℝ)*(major1) + (285718599432519/12500000000000 : ℝ)*(major2) + (196671223229879/6250000000000 : ℝ)*(sp0) + (786604479472637/25000000000000 : ℝ)*(sp1) + (1573250909371577/50000000000000 : ℝ)*(sp2) + (1405214006869387/100000000000000 : ℝ)*(sp3) + (11901448893/100000000000000 : ℝ)*(sp7) + (706784931/25000000000000 : ℝ)*(sp8) + (8112023181/2500000000000 : ℝ)*(sp9) + (240580074633/100000000000000 : ℝ)*(sp10) + (35130647707957/2500000000000 : ℝ)*(f.failure) + (786685599704447/25000000000000 : ℝ)*(f.sum) + (2842616122089/365000000000000000000000000 : ℝ)*base65 + (105321114486030353/9125000000000000000000000000000 : ℝ)*base67 + (87861932227780353/9125000000000000000000000000000 : ℝ)*base69 + (168159355318655353/9125000000000000000000000000000 : ℝ)*base71 + (40996079337/11406250000000000000000000 : ℝ)*base73 + (76586024019780353/9125000000000000000000000000000 : ℝ)*base75 + (131471414738155353/9125000000000000000000000000000 : ℝ)*base77 + (156188815957405353/9125000000000000000000000000000 : ℝ)*base79 + (246615862899/91250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3561499/250000000000000000000 : ℝ)*base90 + (3561499/250000000000000000000 : ℝ)*base92 + (3561499/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40111/50000 : ℝ) ≤ (73204872862470378373957917/91250000000000000000000000 : ℝ) := by norm_num
    linear_combination (27358851/100000000000000 : ℝ)*(lower2) + (100119233/100000000000000 : ℝ)*(lower3) + (31574917/12500000000000 : ℝ)*(upper4) + (46604243/100000000000000 : ℝ)*(lower5) + (620179117371113/25000000000000 : ℝ)*(major0) + (620179117371113/25000000000000 : ℝ)*(major1) + (620179117371113/25000000000000 : ℝ)*(major2) + (13258876609/100000000000000 : ℝ)*(sp1) + (34945730351/12500000000000 : ℝ)*(sp2) + (76347092271/100000000000000 : ℝ)*(sp3) + (426200484064967/12500000000000 : ℝ)*(sp8) + (1704795306821563/50000000000000 : ℝ)*(sp9) + (53270692291827/1562500000000 : ℝ)*(sp10) + (381252803322103/25000000000000 : ℝ)*(sp11) + (1525087560380683/100000000000000 : ℝ)*(f.failure) + (426200484064967/12500000000000 : ℝ)*(f.sum) + (103205759817/182500000000000000000000000 : ℝ)*base65 + (17501518803249231/18250000000000000000000000000000 : ℝ)*base67 + (20975942353750769/18250000000000000000000000000000 : ℝ)*base70 + (60016783773249231/18250000000000000000000000000000 : ℝ)*base71 + (19117569349/91250000000000000000000000 : ℝ)*base74 + (42050574010749231/18250000000000000000000000000000 : ℝ)*base75 + (51387273566000769/18250000000000000000000000000000 : ℝ)*base78 + (24720610870750769/18250000000000000000000000000000 : ℝ)*base80 + (1387402331359/365000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2525019/10000000000000000000000 : ℝ)*base89 + (2525019/10000000000000000000000 : ℝ)*base91 + (2525019/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-10743/12500 : ℝ) ≤ (-39210694160174470120628241/45625000000000000000000000 : ℝ) := by norm_num
    linear_combination (402817/3125000000000 : ℝ)*(lower0) + (5135777/12500000000000 : ℝ)*(lower1) + (1420149/100000000000000 : ℝ)*(lower3) + (23736591/100000000000000 : ℝ)*(lower4) + (2519564919707247/100000000000000 : ℝ)*(major0) + (2519564919707247/100000000000000 : ℝ)*(major1) + (2519564919707247/100000000000000 : ℝ)*(major2) + (33206392169/100000000000000 : ℝ)*(sp5) + (2841083337/4000000000000 : ℝ)*(sp6) + (441982029/5000000000000 : ℝ)*(sp7) + (351880622578457/10000000000000 : ℝ)*(sp12) + (3518773019392401/100000000000000 : ℝ)*(sp13) + (1759367599350573/50000000000000 : ℝ)*(sp14) + (1548961856480789/100000000000000 : ℝ)*(sp15) + (1548970696121369/100000000000000 : ℝ)*(f.failure) + (351880622578457/10000000000000 : ℝ)*(f.sum) + (855007579791/365000000000000000000000000 : ℝ)*base66 + (141365873271153911/73000000000000000000000000000000 : ℝ)*base68 + (490208214683846089/73000000000000000000000000000000 : ℝ)*base69 + (190727152053846089/73000000000000000000000000000000 : ℝ)*base71 + (893428550523/182500000000000000000000000 : ℝ)*base74 + (530843456998846089/73000000000000000000000000000000 : ℝ)*base75 + (274083798992153911/73000000000000000000000000000000 : ℝ)*base78 + (499672874549153911/73000000000000000000000000000000 : ℝ)*base80 + (2018261705447/182500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (18488183/10000000000000000000000 : ℝ)*base90 + (18488183/10000000000000000000000 : ℝ)*base92 + (18488183/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1503_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10881/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3983/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(11717/20000 : ℝ) else (40111/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10743/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1503_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1503_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3983/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(11717/20000 : ℝ) else (40111/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10743/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1503_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1503_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3983/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(11717/20000 : ℝ) else (40111/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10743/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1503_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

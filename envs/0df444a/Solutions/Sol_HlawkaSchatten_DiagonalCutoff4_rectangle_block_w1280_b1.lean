-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1280_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:22:58.47068+00:00
-- url     : https://prove2.me/submissions/c99a4c20-5aae-41b0-ac58-0e1dfc5ffe26

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
theorem support_rectangle_w1280_s3_0 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-209624903/1000000000 : ℝ)*x 0 + (5435898953/10000000000 : ℝ)*x 1 + (2612076623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209624903/1000000000 : ℝ)^265 ≤ (12746321970073/100000000000000 : ℝ)^201 := by
    have hnat : (209624903 : ℕ)^265*100000000000000^201 ≤ 12746321970073^201*1000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209624903 1000000000 12746321970073 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435898953/10000000000 : ℝ)^265 ≤ (44769235027521/100000000000000 : ℝ)^201 := by
    have hnat : (5435898953 : ℕ)^265*100000000000000^201 ≤ 44769235027521^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435898953 10000000000 44769235027521 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2612076623/5000000000 : ℝ)^265 ≤ (21242221493493/50000000000000 : ℝ)^201 := by
    have hnat : (2612076623 : ℕ)^265*50000000000000^201 ≤ 21242221493493^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612076623 5000000000 21242221493493 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-209624903/1000000000 : ℝ), (5435898953/10000000000 : ℝ), (2612076623/5000000000 : ℝ)] ![(12746321970073/100000000000000 : ℝ), (44769235027521/100000000000000 : ℝ), (21242221493493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-209624903/1000000000 : ℝ)|^265 ≤ (12746321970073/100000000000000 : ℝ)^201
        have hw : |(-209624903/1000000000 : ℝ)|=(209624903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435898953/10000000000 : ℝ)|^265 ≤ (44769235027521/100000000000000 : ℝ)^201
        have hw : |(5435898953/10000000000 : ℝ)|=(5435898953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2612076623/5000000000 : ℝ)|^265 ≤ (21242221493493/50000000000000 : ℝ)^201
        have hw : |(2612076623/5000000000 : ℝ)|=(2612076623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s3_1 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2677508237/5000000000 : ℝ)*x 0 + (-1102329159/5000000000 : ℝ)*x 1 + (2612076667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677508237/5000000000 : ℝ)^265 ≤ (43893083821609/100000000000000 : ℝ)^201 := by
    have hnat : (2677508237 : ℕ)^265*100000000000000^201 ≤ 43893083821609^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677508237 5000000000 43893083821609 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102329159/5000000000 : ℝ)^265 ≤ (13622472230517/100000000000000 : ℝ)^201 := by
    have hnat : (1102329159 : ℕ)^265*100000000000000^201 ≤ 13622472230517^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102329159 5000000000 13622472230517 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2612076667/5000000000 : ℝ)^265 ≤ (331909718207/781250000000 : ℝ)^201 := by
    have hnat : (2612076667 : ℕ)^265*781250000000^201 ≤ 331909718207^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612076667 5000000000 331909718207 781250000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677508237/5000000000 : ℝ), (-1102329159/5000000000 : ℝ), (2612076667/5000000000 : ℝ)] ![(43893083821609/100000000000000 : ℝ), (13622472230517/100000000000000 : ℝ), (331909718207/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677508237/5000000000 : ℝ)|^265 ≤ (43893083821609/100000000000000 : ℝ)^201
        have hw : |(2677508237/5000000000 : ℝ)|=(2677508237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1102329159/5000000000 : ℝ)|^265 ≤ (13622472230517/100000000000000 : ℝ)^201
        have hw : |(-1102329159/5000000000 : ℝ)|=(1102329159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2612076667/5000000000 : ℝ)|^265 ≤ (331909718207/781250000000 : ℝ)^201
        have hw : |(2612076667/5000000000 : ℝ)|=(2612076667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s3_2 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5355016499/10000000000 : ℝ)*x 0 + (1306038287/2500000000 : ℝ)*x 1 + (-220465853/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355016499/10000000000 : ℝ)^265 ≤ (10973271022943/25000000000000 : ℝ)^201 := by
    have hnat : (5355016499 : ℕ)^265*25000000000000^201 ≤ 10973271022943^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355016499 10000000000 10973271022943 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1306038287/2500000000 : ℝ)^265 ≤ (42484441936259/100000000000000 : ℝ)^201 := by
    have hnat : (1306038287 : ℕ)^265*100000000000000^201 ≤ 42484441936259^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306038287 2500000000 42484441936259 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220465853/1000000000 : ℝ)^265 ≤ (13622473957549/100000000000000 : ℝ)^201 := by
    have hnat : (220465853 : ℕ)^265*100000000000000^201 ≤ 13622473957549^201*1000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220465853 1000000000 13622473957549 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355016499/10000000000 : ℝ), (1306038287/2500000000 : ℝ), (-220465853/1000000000 : ℝ)] ![(10973271022943/25000000000000 : ℝ), (42484441936259/100000000000000 : ℝ), (13622473957549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355016499/10000000000 : ℝ)|^265 ≤ (10973271022943/25000000000000 : ℝ)^201
        have hw : |(5355016499/10000000000 : ℝ)|=(5355016499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1306038287/2500000000 : ℝ)|^265 ≤ (42484441936259/100000000000000 : ℝ)^201
        have hw : |(1306038287/2500000000 : ℝ)|=(1306038287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-220465853/1000000000 : ℝ)|^265 ≤ (13622473957549/100000000000000 : ℝ)^201
        have hw : |(-220465853/1000000000 : ℝ)|=(220465853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s3_3 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2170788993/5000000000 : ℝ)*x 0 + (516271251/1250000000 : ℝ)*x 1 + (1140840831/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170788993/5000000000 : ℝ)^265 ≤ (260052929423/781250000000 : ℝ)^201 := by
    have hnat : (2170788993 : ℕ)^265*781250000000^201 ≤ 260052929423^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170788993 5000000000 260052929423 781250000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516271251/1250000000 : ℝ)^265 ≤ (7791643415523/25000000000000 : ℝ)^201 := by
    have hnat : (516271251 : ℕ)^265*25000000000000^201 ≤ 7791643415523^201*1250000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516271251 1250000000 7791643415523 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1140840831/2500000000 : ℝ)^265 ≤ (1421866054273/4000000000000 : ℝ)^201 := by
    have hnat : (1140840831 : ℕ)^265*4000000000000^201 ≤ 1421866054273^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140840831 2500000000 1421866054273 4000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170788993/5000000000 : ℝ), (516271251/1250000000 : ℝ), (1140840831/2500000000 : ℝ)] ![(260052929423/781250000000 : ℝ), (7791643415523/25000000000000 : ℝ), (1421866054273/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170788993/5000000000 : ℝ)|^265 ≤ (260052929423/781250000000 : ℝ)^201
        have hw : |(2170788993/5000000000 : ℝ)|=(2170788993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(516271251/1250000000 : ℝ)|^265 ≤ (7791643415523/25000000000000 : ℝ)^201
        have hw : |(516271251/1250000000 : ℝ)|=(516271251/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1140840831/2500000000 : ℝ)|^265 ≤ (1421866054273/4000000000000 : ℝ)^201
        have hw : |(1140840831/2500000000 : ℝ)|=(1140840831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s3_4 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-524068127/2500000000 : ℝ)*x 0 + (5225073197/10000000000 : ℝ)*x 1 + (5434973183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524068127/2500000000 : ℝ)^265 ≤ (6373255092421/50000000000000 : ℝ)^201 := by
    have hnat : (524068127 : ℕ)^265*50000000000000^201 ≤ 6373255092421^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524068127 2500000000 6373255092421 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5225073197/10000000000 : ℝ)^265 ≤ (21247153353177/50000000000000 : ℝ)^201 := by
    have hnat : (5225073197 : ℕ)^265*50000000000000^201 ≤ 21247153353177^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225073197 10000000000 21247153353177 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434973183/10000000000 : ℝ)^265 ≤ (22379591548913/50000000000000 : ℝ)^201 := by
    have hnat : (5434973183 : ℕ)^265*50000000000000^201 ≤ 22379591548913^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434973183 10000000000 22379591548913 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-524068127/2500000000 : ℝ), (5225073197/10000000000 : ℝ), (5434973183/10000000000 : ℝ)] ![(6373255092421/50000000000000 : ℝ), (21247153353177/50000000000000 : ℝ), (22379591548913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-524068127/2500000000 : ℝ)|^265 ≤ (6373255092421/50000000000000 : ℝ)^201
        have hw : |(-524068127/2500000000 : ℝ)|=(524068127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5225073197/10000000000 : ℝ)|^265 ≤ (21247153353177/50000000000000 : ℝ)^201
        have hw : |(5225073197/10000000000 : ℝ)|=(5225073197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434973183/10000000000 : ℝ)|^265 ≤ (22379591548913/50000000000000 : ℝ)^201
        have hw : |(5434973183/10000000000 : ℝ)|=(5434973183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s3_5 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5300882339/10000000000 : ℝ)*x 0 + (-996919137/5000000000 : ℝ)*x 1 + (1358743279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5300882339/10000000000 : ℝ)^265 ≤ (43309026907561/100000000000000 : ℝ)^201 := by
    have hnat : (5300882339 : ℕ)^265*100000000000000^201 ≤ 43309026907561^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5300882339 10000000000 43309026907561 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (996919137/5000000000 : ℝ)^265 ≤ (47727162857/400000000000 : ℝ)^201 := by
    have hnat : (996919137 : ℕ)^265*400000000000^201 ≤ 47727162857^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996919137 5000000000 47727162857 400000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358743279/2500000000 : ℝ)^265 ≤ (22379591185183/50000000000000 : ℝ)^201 := by
    have hnat : (1358743279 : ℕ)^265*50000000000000^201 ≤ 22379591185183^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358743279 2500000000 22379591185183 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5300882339/10000000000 : ℝ), (-996919137/5000000000 : ℝ), (1358743279/2500000000 : ℝ)] ![(43309026907561/100000000000000 : ℝ), (47727162857/400000000000 : ℝ), (22379591185183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5300882339/10000000000 : ℝ)|^265 ≤ (43309026907561/100000000000000 : ℝ)^201
        have hw : |(5300882339/10000000000 : ℝ)|=(5300882339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-996919137/5000000000 : ℝ)|^265 ≤ (47727162857/400000000000 : ℝ)^201
        have hw : |(-996919137/5000000000 : ℝ)|=(996919137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358743279/2500000000 : ℝ)|^265 ≤ (22379591185183/50000000000000 : ℝ)^201
        have hw : |(1358743279/2500000000 : ℝ)|=(1358743279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s3_6 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2650441173/5000000000 : ℝ)*x 0 + (1086994619/2000000000 : ℝ)*x 1 + (-1993838293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650441173/5000000000 : ℝ)^265 ≤ (21654513491481/50000000000000 : ℝ)^201 := by
    have hnat : (2650441173 : ℕ)^265*50000000000000^201 ≤ 21654513491481^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650441173 5000000000 21654513491481 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086994619/2000000000 : ℝ)^265 ≤ (11189795535589/25000000000000 : ℝ)^201 := by
    have hnat : (1086994619 : ℕ)^265*25000000000000^201 ≤ 11189795535589^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086994619 2000000000 11189795535589 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1993838293/10000000000 : ℝ)^265 ≤ (2982947716039/25000000000000 : ℝ)^201 := by
    have hnat : (1993838293 : ℕ)^265*25000000000000^201 ≤ 2982947716039^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993838293 10000000000 2982947716039 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650441173/5000000000 : ℝ), (1086994619/2000000000 : ℝ), (-1993838293/10000000000 : ℝ)] ![(21654513491481/50000000000000 : ℝ), (11189795535589/25000000000000 : ℝ), (2982947716039/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650441173/5000000000 : ℝ)|^265 ≤ (21654513491481/50000000000000 : ℝ)^201
        have hw : |(2650441173/5000000000 : ℝ)|=(2650441173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086994619/2000000000 : ℝ)|^265 ≤ (11189795535589/25000000000000 : ℝ)^201
        have hw : |(1086994619/2000000000 : ℝ)|=(1086994619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1993838293/10000000000 : ℝ)|^265 ≤ (2982947716039/25000000000000 : ℝ)^201
        have hw : |(-1993838293/10000000000 : ℝ)|=(1993838293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s3_7 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (868325147/2000000000 : ℝ)*x 0 + (912296217/2000000000 : ℝ)*x 1 + (2066032101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868325147/2000000000 : ℝ)^265 ≤ (16643628811773/50000000000000 : ℝ)^201 := by
    have hnat : (868325147 : ℕ)^265*50000000000000^201 ≤ 16643628811773^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868325147 2000000000 16643628811773 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (912296217/2000000000 : ℝ)^265 ≤ (2220457646403/6250000000000 : ℝ)^201 := by
    have hnat : (912296217 : ℕ)^265*6250000000000^201 ≤ 2220457646403^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912296217 2000000000 2220457646403 6250000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066032101/5000000000 : ℝ)^265 ≤ (31185420005923/100000000000000 : ℝ)^201 := by
    have hnat : (2066032101 : ℕ)^265*100000000000000^201 ≤ 31185420005923^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066032101 5000000000 31185420005923 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(868325147/2000000000 : ℝ), (912296217/2000000000 : ℝ), (2066032101/5000000000 : ℝ)] ![(16643628811773/50000000000000 : ℝ), (2220457646403/6250000000000 : ℝ), (31185420005923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(868325147/2000000000 : ℝ)|^265 ≤ (16643628811773/50000000000000 : ℝ)^201
        have hw : |(868325147/2000000000 : ℝ)|=(868325147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(912296217/2000000000 : ℝ)|^265 ≤ (2220457646403/6250000000000 : ℝ)^201
        have hw : |(912296217/2000000000 : ℝ)|=(912296217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2066032101/5000000000 : ℝ)|^265 ≤ (31185420005923/100000000000000 : ℝ)^201
        have hw : |(2066032101/5000000000 : ℝ)|=(2066032101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1280_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16373/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1883/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2651/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15083/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16373/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1883/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16373/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1883/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16373/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1883/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16373/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1883/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16373/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1883/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16373/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1883/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1883/20000 : ℝ) ^ (4239/1024 : ℝ) ≤ (44133354580251/781250000000000000 : ℝ) := by
    have hpowers : (1883/20000 : ℝ)^4239 ≤ (44133354580251/781250000000000000 : ℝ)^1024 := by
      have hnat : (1883 : ℕ)^4239*781250000000000000^1024 ≤ 44133354580251^1024*20000^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1883 20000 44133354580251 781250000000000000 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1883/20000 : ℝ)) (X := (44133354580251/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16373/100000 : ℝ) ^ (4239/1024 : ℝ) ≤ (55817102337655983/100000000000000000000 : ℝ) := by
    have hpowers : (16373/100000 : ℝ)^4239 ≤ (55817102337655983/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16373 : ℕ)^4239*100000000000000000000^1024 ≤ 55817102337655983^1024*100000^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16373 100000 55817102337655983 100000000000000000000 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16373/100000 : ℝ)) (X := (55817102337655983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (390669133354580251/390625000000000000 : ℝ) ≤ (5000136456693277/5000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (390669133354580251/390625000000000000 : ℝ)^1024 ≤ (5000136456693277/5000000000000000 : ℝ)^4239 := by
      have hnat : (390669133354580251 : ℕ)^1024*5000000000000000^4239 ≤ 5000136456693277^4239*390625000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390669133354580251 390625000000000000 5000136456693277 5000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000136456693277/5000000000000000 : ℝ)) (X := (390669133354580251/390625000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100061466171723928111/100000000000000000000 : ℝ) ≤ (2500371117563837/2500000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (100061466171723928111/100000000000000000000 : ℝ)^1024 ≤ (2500371117563837/2500000000000000 : ℝ)^4239 := by
      have hnat : (100061466171723928111 : ℕ)^1024*2500000000000000^4239 ≤ 2500371117563837^4239*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100061466171723928111 100000000000000000000 2500371117563837 2500000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500371117563837/2500000000000000 : ℝ)) (X := (100061466171723928111/100000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50055817102337655983/50000000000000000000 : ℝ) ≤ (5001348013562071/5000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (50055817102337655983/50000000000000000000 : ℝ)^1024 ≤ (5001348013562071/5000000000000000 : ℝ)^4239 := by
      have hnat : (50055817102337655983 : ℕ)^1024*5000000000000000^4239 ≤ 5001348013562071^4239*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50055817102337655983 50000000000000000000 5001348013562071 5000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001348013562071/5000000000000000 : ℝ)) (X := (50055817102337655983/50000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(44133354580251/781250000000000000 : ℝ) ≤ ((155265815436393419/155312500000000000 : ℝ)+2*(605778434397/347900000000000 : ℝ)*(1883/20000 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (155265815436393419/155312500000000000 : ℝ)+2*(605778434397/347900000000000 : ℝ)*(1883/20000 : ℝ)=(5000136456693277/5000000000000000 : ℝ) by norm_num, show 1+2*(44133354580251/781250000000000000 : ℝ)=(390669133354580251/390625000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(55817102337655983/100000000000000000000 : ℝ)+(44133354580251/781250000000000000 : ℝ) ≤ ((155265815436393419/155312500000000000 : ℝ)+(605778434397/347900000000000 : ℝ)*((16373/100000 : ℝ)+(1883/20000 : ℝ)))^(4239/1024 : ℝ) := by
    rw [show (155265815436393419/155312500000000000 : ℝ)+(605778434397/347900000000000 : ℝ)*((16373/100000 : ℝ)+(1883/20000 : ℝ))=(2500371117563837/2500000000000000 : ℝ) by norm_num, show 1+(55817102337655983/100000000000000000000 : ℝ)+(44133354580251/781250000000000000 : ℝ)=(100061466171723928111/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(55817102337655983/100000000000000000000 : ℝ) ≤ ((155265815436393419/155312500000000000 : ℝ)+2*(605778434397/347900000000000 : ℝ)*(16373/100000 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (155265815436393419/155312500000000000 : ℝ)+2*(605778434397/347900000000000 : ℝ)*(16373/100000 : ℝ)=(5001348013562071/5000000000000000 : ℝ) by norm_num, show 1+2*(55817102337655983/100000000000000000000 : ℝ)=(50055817102337655983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (155265815436393419/155312500000000000 : ℝ)*(X 1 0+X 2 0)+(605778434397/347900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (1883/20000 : ℝ)) (hi := (16373/100000 : ℝ)) (c := (155265815436393419/155312500000000000 : ℝ)) (alpha := (605778434397/347900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (155265815436393419/155312500000000000 : ℝ)*(X 0 1+X 2 1)+(605778434397/347900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (1883/20000 : ℝ)) (hi := (16373/100000 : ℝ)) (c := (155265815436393419/155312500000000000 : ℝ)) (alpha := (605778434397/347900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (155265815436393419/155312500000000000 : ℝ)*(X 0 2+X 1 2)+(605778434397/347900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (1883/20000 : ℝ)) (hi := (16373/100000 : ℝ)) (c := (155265815436393419/155312500000000000 : ℝ)) (alpha := (605778434397/347900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-209624903/1000000000 : ℝ)*X 0 0+(5435898953/10000000000 : ℝ)*X 0 1+(2612076623/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677508237/5000000000 : ℝ)*X 1 0+(-1102329159/5000000000 : ℝ)*X 1 1+(2612076667/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355016499/10000000000 : ℝ)*X 2 0+(1306038287/2500000000 : ℝ)*X 2 1+(-220465853/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2170788993/5000000000 : ℝ)*X 0 0+(516271251/1250000000 : ℝ)*X 0 1+(1140840831/2500000000 : ℝ)*X 0 2+(2170788993/5000000000 : ℝ)*X 1 0+(516271251/1250000000 : ℝ)*X 1 1+(1140840831/2500000000 : ℝ)*X 1 2+(2170788993/5000000000 : ℝ)*X 2 0+(516271251/1250000000 : ℝ)*X 2 1+(1140840831/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-524068127/2500000000 : ℝ)*X 0 0+(5225073197/10000000000 : ℝ)*X 0 1+(5434973183/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5300882339/10000000000 : ℝ)*X 1 0+(-996919137/5000000000 : ℝ)*X 1 1+(1358743279/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2650441173/5000000000 : ℝ)*X 2 0+(1086994619/2000000000 : ℝ)*X 2 1+(-1993838293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((868325147/2000000000 : ℝ)*X 0 0+(912296217/2000000000 : ℝ)*X 0 1+(2066032101/5000000000 : ℝ)*X 0 2+(868325147/2000000000 : ℝ)*X 1 0+(912296217/2000000000 : ℝ)*X 1 1+(2066032101/5000000000 : ℝ)*X 1 2+(868325147/2000000000 : ℝ)*X 2 0+(912296217/2000000000 : ℝ)*X 2 1+(2066032101/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1524186260630899237857399/543593750000000000000000000000 : ℝ) := by norm_num
    linear_combination (90420503/25000000000000 : ℝ)*(base19) + (425024861/100000000000000 : ℝ)*(base23) + (22542249/100000000000000 : ℝ)*(lower2) + (10898629/6250000000000 : ℝ)*(upper3) + (44655813/100000000000000 : ℝ)*(lower4) + (70310995210573/2000000000000 : ℝ)*(major0) + (70310995210573/2000000000000 : ℝ)*(major1) + (70310995210573/2000000000000 : ℝ)*(major2) + (295165832243911/6250000000000 : ℝ)*(sp0) + (4722654847546499/100000000000000 : ℝ)*(sp1) + (94453095684073/2000000000000 : ℝ)*(sp2) + (1154220087422473/50000000000000 : ℝ)*(sp3) + (378665187/20000000000000 : ℝ)*(sp4) + (4043520273/100000000000000 : ℝ)*(sp7) + (115422210918261/5000000000000 : ℝ)*(f.failure) + (4722655209228511/100000000000000 : ℝ)*(f.sum) + (890875617481/3479000000000000000000000000 : ℝ)*base65 + (3486511106839133/1087187500000000000000000000000 : ℝ)*base68 + (399179796418609/2174375000000000000000000000000 : ℝ)*base69 + (10981387850922359/2174375000000000000000000000000 : ℝ)*base71 + (6698211294779/3479000000000000000000000000 : ℝ)*base74 + (5377521643417117/1087187500000000000000000000000 : ℝ)*base75 + (10110042743262641/2174375000000000000000000000000 : ℝ)*base78 + (33168716795769859/2174375000000000000000000000000 : ℝ)*base79 + (298112668149/86975000000000000000000000 : ℝ)*base81 + (5658809/500000000000000000000 : ℝ)*base89 + (5658809/500000000000000000000 : ℝ)*base91 + (5658809/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15308235847839216725239827/1553125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (545604241/25000000000000 : ℝ)*(base19) + (2290408733/100000000000000 : ℝ)*(base23) + (54109989/25000000000000 : ℝ)*(upper3) + (51048153/100000000000000 : ℝ)*(lower4) + (61486323/25000000000000 : ℝ)*(upper5) + (709291283717739/20000000000000 : ℝ)*(major0) + (709291283717739/20000000000000 : ℝ)*(major1) + (709291283717739/20000000000000 : ℝ)*(major2) + (35476712991/100000000000000 : ℝ)*(sp1) + (7201080991/20000000000000 : ℝ)*(sp2) + (2382086899187057/50000000000000 : ℝ)*(sp4) + (4764136139244159/100000000000000 : ℝ)*(sp5) + (4764135502560427/100000000000000 : ℝ)*(sp6) + (2328738710256289/100000000000000 : ℝ)*(sp7) + (2328738710256289/100000000000000 : ℝ)*(f.failure) + (2382086899187057/50000000000000 : ℝ)*(f.sum) + (7653450931277/1739500000000000000000000000 : ℝ)*base66 + (374703094419257/1358984375000000000000000000000 : ℝ)*base67 + (144173974693032181/10871875000000000000000000000000 : ℝ)*base69 + (34115072471188431/10871875000000000000000000000000 : ℝ)*base71 + (985168161259/869750000000000000000000000 : ℝ)*base74 + (41680388824582181/10871875000000000000000000000000 : ℝ)*base75 + (20864571829774069/10871875000000000000000000000000 : ℝ)*base78 + (103489536426249069/10871875000000000000000000000000 : ℝ)*base80 + (889392618017/173950000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (35474859/10000000000000000000000 : ℝ)*base90 + (35474859/10000000000000000000000 : ℝ)*base92 + (35474859/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1280_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16373/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1883/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2651/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15083/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1280_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1280_s4_0 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-262286971/1250000000 : ℝ)*x 0 + (541987237/1000000000 : ℝ)*x 1 + (5238839093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262286971/1250000000 : ℝ)^265 ≤ (12762732460771/100000000000000 : ℝ)^201 := by
    have hnat : (262286971 : ℕ)^265*100000000000000^201 ≤ 12762732460771^201*1250000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262286971 1250000000 12762732460771 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541987237/1000000000 : ℝ)^265 ≤ (8919059361709/20000000000000 : ℝ)^201 := by
    have hnat : (541987237 : ℕ)^265*20000000000000^201 ≤ 8919059361709^201*1000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541987237 1000000000 8919059361709 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238839093/10000000000 : ℝ)^265 ≤ (42641970724451/100000000000000 : ℝ)^201 := by
    have hnat : (5238839093 : ℕ)^265*100000000000000^201 ≤ 42641970724451^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238839093 10000000000 42641970724451 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-262286971/1250000000 : ℝ), (541987237/1000000000 : ℝ), (5238839093/10000000000 : ℝ)] ![(12762732460771/100000000000000 : ℝ), (8919059361709/20000000000000 : ℝ), (42641970724451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-262286971/1250000000 : ℝ)|^265 ≤ (12762732460771/100000000000000 : ℝ)^201
        have hw : |(-262286971/1250000000 : ℝ)|=(262286971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541987237/1000000000 : ℝ)|^265 ≤ (8919059361709/20000000000000 : ℝ)^201
        have hw : |(541987237/1000000000 : ℝ)|=(541987237/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238839093/10000000000 : ℝ)|^265 ≤ (42641970724451/100000000000000 : ℝ)^201
        have hw : |(5238839093/10000000000 : ℝ)|=(5238839093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s4_1 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (334435959/625000000 : ℝ)*x 0 + (-136916699/625000000 : ℝ)*x 1 + (1309709777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334435959/625000000 : ℝ)^265 ≤ (43849418593623/100000000000000 : ℝ)^201 := by
    have hnat : (334435959 : ℕ)^265*100000000000000^201 ≤ 43849418593623^201*625000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334435959 625000000 43849418593623 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136916699/625000000 : ℝ)^265 ≤ (1688576314053/12500000000000 : ℝ)^201 := by
    have hnat : (136916699 : ℕ)^265*12500000000000^201 ≤ 1688576314053^201*625000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136916699 625000000 1688576314053 12500000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1309709777/2500000000 : ℝ)^265 ≤ (42641970885421/100000000000000 : ℝ)^201 := by
    have hnat : (1309709777 : ℕ)^265*100000000000000^201 ≤ 42641970885421^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309709777 2500000000 42641970885421 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334435959/625000000 : ℝ), (-136916699/625000000 : ℝ), (1309709777/2500000000 : ℝ)] ![(43849418593623/100000000000000 : ℝ), (1688576314053/12500000000000 : ℝ), (42641970885421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334435959/625000000 : ℝ)|^265 ≤ (43849418593623/100000000000000 : ℝ)^201
        have hw : |(334435959/625000000 : ℝ)|=(334435959/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-136916699/625000000 : ℝ)|^265 ≤ (1688576314053/12500000000000 : ℝ)^201
        have hw : |(-136916699/625000000 : ℝ)|=(136916699/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1309709777/2500000000 : ℝ)|^265 ≤ (42641970885421/100000000000000 : ℝ)^201
        have hw : |(1309709777/2500000000 : ℝ)|=(1309709777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s4_2 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5350975153/10000000000 : ℝ)*x 0 + (1309709819/2500000000 : ℝ)*x 1 + (-1095333607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350975153/10000000000 : ℝ)^265 ≤ (43849416530077/100000000000000 : ℝ)^201 := by
    have hnat : (5350975153 : ℕ)^265*100000000000000^201 ≤ 43849416530077^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350975153 10000000000 43849416530077 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309709819/2500000000 : ℝ)^265 ≤ (21320986344139/50000000000000 : ℝ)^201 := by
    have hnat : (1309709819 : ℕ)^265*50000000000000^201 ≤ 21320986344139^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309709819 2500000000 21320986344139 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095333607/5000000000 : ℝ)^265 ≤ (13508610756321/100000000000000 : ℝ)^201 := by
    have hnat : (1095333607 : ℕ)^265*100000000000000^201 ≤ 13508610756321^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095333607 5000000000 13508610756321 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350975153/10000000000 : ℝ), (1309709819/2500000000 : ℝ), (-1095333607/5000000000 : ℝ)] ![(43849416530077/100000000000000 : ℝ), (21320986344139/50000000000000 : ℝ), (13508610756321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350975153/10000000000 : ℝ)|^265 ≤ (43849416530077/100000000000000 : ℝ)^201
        have hw : |(5350975153/10000000000 : ℝ)|=(5350975153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309709819/2500000000 : ℝ)|^265 ≤ (21320986344139/50000000000000 : ℝ)^201
        have hw : |(1309709819/2500000000 : ℝ)|=(1309709819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1095333607/5000000000 : ℝ)|^265 ≤ (13508610756321/100000000000000 : ℝ)^201
        have hw : |(-1095333607/5000000000 : ℝ)|=(1095333607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s4_3 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1085704011/2500000000 : ℝ)*x 0 + (2080714973/5000000000 : ℝ)*x 1 + (4531790667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085704011/2500000000 : ℝ)^265 ≤ (16649645037561/50000000000000 : ℝ)^201 := by
    have hnat : (1085704011 : ℕ)^265*50000000000000^201 ≤ 16649645037561^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085704011 2500000000 16649645037561 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080714973/5000000000 : ℝ)^265 ≤ (31477946810947/100000000000000 : ℝ)^201 := by
    have hnat : (2080714973 : ℕ)^265*100000000000000^201 ≤ 31477946810947^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080714973 5000000000 31477946810947 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4531790667/10000000000 : ℝ)^265 ≤ (17611381548563/50000000000000 : ℝ)^201 := by
    have hnat : (4531790667 : ℕ)^265*50000000000000^201 ≤ 17611381548563^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531790667 10000000000 17611381548563 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085704011/2500000000 : ℝ), (2080714973/5000000000 : ℝ), (4531790667/10000000000 : ℝ)] ![(16649645037561/50000000000000 : ℝ), (31477946810947/100000000000000 : ℝ), (17611381548563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085704011/2500000000 : ℝ)|^265 ≤ (16649645037561/50000000000000 : ℝ)^201
        have hw : |(1085704011/2500000000 : ℝ)|=(1085704011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2080714973/5000000000 : ℝ)|^265 ≤ (31477946810947/100000000000000 : ℝ)^201
        have hw : |(2080714973/5000000000 : ℝ)|=(2080714973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4531790667/10000000000 : ℝ)|^265 ≤ (17611381548563/50000000000000 : ℝ)^201
        have hw : |(4531790667/10000000000 : ℝ)|=(4531790667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s4_4 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-3357297/16000000 : ℝ)*x 0 + (523951251/1000000000 : ℝ)*x 1 + (5419195187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3357297/16000000 : ℝ)^265 ≤ (12762851600989/100000000000000 : ℝ)^201 := by
    have hnat : (3357297 : ℕ)^265*100000000000000^201 ≤ 12762851600989^201*16000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3357297 16000000 12762851600989 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523951251/1000000000 : ℝ)^265 ≤ (42649197507007/100000000000000 : ℝ)^201 := by
    have hnat : (523951251 : ℕ)^265*100000000000000^201 ≤ 42649197507007^201*1000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523951251 1000000000 42649197507007 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419195187/10000000000 : ℝ)^265 ≤ (22293975435569/50000000000000 : ℝ)^201 := by
    have hnat : (5419195187 : ℕ)^265*50000000000000^201 ≤ 22293975435569^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419195187 10000000000 22293975435569 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3357297/16000000 : ℝ), (523951251/1000000000 : ℝ), (5419195187/10000000000 : ℝ)] ![(12762851600989/100000000000000 : ℝ), (42649197507007/100000000000000 : ℝ), (22293975435569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3357297/16000000 : ℝ)|^265 ≤ (12762851600989/100000000000000 : ℝ)^201
        have hw : |(-3357297/16000000 : ℝ)|=(3357297/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523951251/1000000000 : ℝ)|^265 ≤ (42649197507007/100000000000000 : ℝ)^201
        have hw : |(523951251/1000000000 : ℝ)|=(523951251/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419195187/10000000000 : ℝ)|^265 ≤ (22293975435569/50000000000000 : ℝ)^201
        have hw : |(5419195187/10000000000 : ℝ)|=(5419195187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s4_5 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (8288589/15625000 : ℝ)*x 0 + (-502577771/2500000000 : ℝ)*x 1 + (2709597573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8288589/15625000 : ℝ)^265 ≤ (43350121172611/100000000000000 : ℝ)^201 := by
    have hnat : (8288589 : ℕ)^265*100000000000000^201 ≤ 43350121172611^201*15625000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8288589 15625000 43350121172611 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502577771/2500000000 : ℝ)^265 ≤ (12061928375753/100000000000000 : ℝ)^201 := by
    have hnat : (502577771 : ℕ)^265*100000000000000^201 ≤ 12061928375753^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502577771 2500000000 12061928375753 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709597573/5000000000 : ℝ)^265 ≤ (11146987606597/25000000000000 : ℝ)^201 := by
    have hnat : (2709597573 : ℕ)^265*25000000000000^201 ≤ 11146987606597^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709597573 5000000000 11146987606597 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8288589/15625000 : ℝ), (-502577771/2500000000 : ℝ), (2709597573/5000000000 : ℝ)] ![(43350121172611/100000000000000 : ℝ), (12061928375753/100000000000000 : ℝ), (11146987606597/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8288589/15625000 : ℝ)|^265 ≤ (43350121172611/100000000000000 : ℝ)^201
        have hw : |(8288589/15625000 : ℝ)|=(8288589/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-502577771/2500000000 : ℝ)|^265 ≤ (12061928375753/100000000000000 : ℝ)^201
        have hw : |(-502577771/2500000000 : ℝ)|=(502577771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709597573/5000000000 : ℝ)|^265 ≤ (11146987606597/25000000000000 : ℝ)^201
        have hw : |(2709597573/5000000000 : ℝ)|=(2709597573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s4_6 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5304697213/10000000000 : ℝ)*x 0 + (1354798823/2500000000 : ℝ)*x 1 + (-2010310541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304697213/10000000000 : ℝ)^265 ≤ (43350123898449/100000000000000 : ℝ)^201 := by
    have hnat : (5304697213 : ℕ)^265*100000000000000^201 ≤ 43350123898449^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304697213 10000000000 43350123898449 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354798823/2500000000 : ℝ)^265 ≤ (44587952010133/100000000000000 : ℝ)^201 := by
    have hnat : (1354798823 : ℕ)^265*100000000000000^201 ≤ 44587952010133^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354798823 2500000000 44587952010133 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2010310541/10000000000 : ℝ)^265 ≤ (6030962040179/50000000000000 : ℝ)^201 := by
    have hnat : (2010310541 : ℕ)^265*50000000000000^201 ≤ 6030962040179^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010310541 10000000000 6030962040179 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304697213/10000000000 : ℝ), (1354798823/2500000000 : ℝ), (-2010310541/10000000000 : ℝ)] ![(43350123898449/100000000000000 : ℝ), (44587952010133/100000000000000 : ℝ), (6030962040179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304697213/10000000000 : ℝ)|^265 ≤ (43350123898449/100000000000000 : ℝ)^201
        have hw : |(5304697213/10000000000 : ℝ)|=(5304697213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354798823/2500000000 : ℝ)|^265 ≤ (44587952010133/100000000000000 : ℝ)^201
        have hw : |(1354798823/2500000000 : ℝ)|=(1354798823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2010310541/10000000000 : ℝ)|^265 ≤ (6030962040179/50000000000000 : ℝ)^201
        have hw : |(-2010310541/10000000000 : ℝ)|=(2010310541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s4_7 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2171422979/5000000000 : ℝ)*x 0 + (4530413499/10000000000 : ℝ)*x 1 + (4162814547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171422979/5000000000 : ℝ)^265 ≤ (33299592479673/100000000000000 : ℝ)^201 := by
    have hnat : (2171422979 : ℕ)^265*100000000000000^201 ≤ 33299592479673^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171422979 5000000000 33299592479673 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4530413499/10000000000 : ℝ)^265 ≤ (35208651722971/100000000000000 : ℝ)^201 := by
    have hnat : (4530413499 : ℕ)^265*100000000000000^201 ≤ 35208651722971^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530413499 10000000000 35208651722971 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4162814547/10000000000 : ℝ)^265 ≤ (31491755780407/100000000000000 : ℝ)^201 := by
    have hnat : (4162814547 : ℕ)^265*100000000000000^201 ≤ 31491755780407^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162814547 10000000000 31491755780407 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171422979/5000000000 : ℝ), (4530413499/10000000000 : ℝ), (4162814547/10000000000 : ℝ)] ![(33299592479673/100000000000000 : ℝ), (35208651722971/100000000000000 : ℝ), (31491755780407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171422979/5000000000 : ℝ)|^265 ≤ (33299592479673/100000000000000 : ℝ)^201
        have hw : |(2171422979/5000000000 : ℝ)|=(2171422979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4530413499/10000000000 : ℝ)|^265 ≤ (35208651722971/100000000000000 : ℝ)^201
        have hw : |(4530413499/10000000000 : ℝ)|=(4530413499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4162814547/10000000000 : ℝ)|^265 ≤ (31491755780407/100000000000000 : ℝ)^201
        have hw : |(4162814547/10000000000 : ℝ)|=(4162814547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1280_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2651/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10917/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3687/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15083/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2651/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15083/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2651/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15083/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2651/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15083/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2651/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15083/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2651/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15083/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2651/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2651/25000 : ℝ) ^ (4239/1024 : ℝ) ≤ (4621226440957219/50000000000000000000 : ℝ) := by
    have hpowers : (2651/25000 : ℝ)^4239 ≤ (4621226440957219/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2651 : ℕ)^4239*50000000000000000000^1024 ≤ 4621226440957219^1024*25000^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2651 25000 4621226440957219 50000000000000000000 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2651/25000 : ℝ)) (X := (4621226440957219/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15083/100000 : ℝ) ^ (4239/1024 : ℝ) ≤ (39740014336001831/100000000000000000000 : ℝ) := by
    have hpowers : (15083/100000 : ℝ)^4239 ≤ (39740014336001831/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15083 : ℕ)^4239*100000000000000000000^1024 ≤ 39740014336001831^1024*100000^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15083 100000 39740014336001831 100000000000000000000 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15083/100000 : ℝ)) (X := (39740014336001831/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004621226440957219/25000000000000000000 : ℝ) ≤ (1250055812741199/1250000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (25004621226440957219/25000000000000000000 : ℝ)^1024 ≤ (1250055812741199/1250000000000000 : ℝ)^4239 := by
      have hnat : (25004621226440957219 : ℕ)^1024*1250000000000000^4239 ≤ 1250055812741199^4239*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004621226440957219 25000000000000000000 1250055812741199 1250000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250055812741199/1250000000000000 : ℝ)) (X := (25004621226440957219/25000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048982467217916269/100000000000000000000 : ℝ) ≤ (1250147879017047/1250000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (100048982467217916269/100000000000000000000 : ℝ)^1024 ≤ (1250147879017047/1250000000000000 : ℝ)^4239 := by
      have hnat : (100048982467217916269 : ℕ)^1024*1250000000000000^4239 ≤ 1250147879017047^4239*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048982467217916269 100000000000000000000 1250147879017047 1250000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250147879017047/1250000000000000 : ℝ)) (X := (100048982467217916269/100000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039740014336001831/50000000000000000000 : ℝ) ≤ (250047989058579/250000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (50039740014336001831/50000000000000000000 : ℝ)^1024 ≤ (250047989058579/250000000000000 : ℝ)^4239 := by
      have hnat : (50039740014336001831 : ℕ)^1024*250000000000000^4239 ≤ 250047989058579^4239*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039740014336001831 50000000000000000000 250047989058579 250000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250047989058579/250000000000000 : ℝ)) (X := (50039740014336001831/50000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4621226440957219/50000000000000000000 : ℝ) ≤ ((1865682481229881979/1866250000000000000 : ℝ)+2*(3836094827/2332812500000 : ℝ)*(2651/25000 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (1865682481229881979/1866250000000000000 : ℝ)+2*(3836094827/2332812500000 : ℝ)*(2651/25000 : ℝ)=(1250055812741199/1250000000000000 : ℝ) by norm_num, show 1+2*(4621226440957219/50000000000000000000 : ℝ)=(25004621226440957219/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39740014336001831/100000000000000000000 : ℝ)+(4621226440957219/50000000000000000000 : ℝ) ≤ ((1865682481229881979/1866250000000000000 : ℝ)+(3836094827/2332812500000 : ℝ)*((15083/100000 : ℝ)+(2651/25000 : ℝ)))^(4239/1024 : ℝ) := by
    rw [show (1865682481229881979/1866250000000000000 : ℝ)+(3836094827/2332812500000 : ℝ)*((15083/100000 : ℝ)+(2651/25000 : ℝ))=(1250147879017047/1250000000000000 : ℝ) by norm_num, show 1+(39740014336001831/100000000000000000000 : ℝ)+(4621226440957219/50000000000000000000 : ℝ)=(100048982467217916269/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39740014336001831/100000000000000000000 : ℝ) ≤ ((1865682481229881979/1866250000000000000 : ℝ)+2*(3836094827/2332812500000 : ℝ)*(15083/100000 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (1865682481229881979/1866250000000000000 : ℝ)+2*(3836094827/2332812500000 : ℝ)*(15083/100000 : ℝ)=(250047989058579/250000000000000 : ℝ) by norm_num, show 1+2*(39740014336001831/100000000000000000000 : ℝ)=(50039740014336001831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1865682481229881979/1866250000000000000 : ℝ)*(X 1 0+X 2 0)+(3836094827/2332812500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (2651/25000 : ℝ)) (hi := (15083/100000 : ℝ)) (c := (1865682481229881979/1866250000000000000 : ℝ)) (alpha := (3836094827/2332812500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1865682481229881979/1866250000000000000 : ℝ)*(X 0 1+X 2 1)+(3836094827/2332812500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (2651/25000 : ℝ)) (hi := (15083/100000 : ℝ)) (c := (1865682481229881979/1866250000000000000 : ℝ)) (alpha := (3836094827/2332812500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1865682481229881979/1866250000000000000 : ℝ)*(X 0 2+X 1 2)+(3836094827/2332812500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (2651/25000 : ℝ)) (hi := (15083/100000 : ℝ)) (c := (1865682481229881979/1866250000000000000 : ℝ)) (alpha := (3836094827/2332812500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-262286971/1250000000 : ℝ)*X 0 0+(541987237/1000000000 : ℝ)*X 0 1+(5238839093/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334435959/625000000 : ℝ)*X 1 0+(-136916699/625000000 : ℝ)*X 1 1+(1309709777/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350975153/10000000000 : ℝ)*X 2 0+(1309709819/2500000000 : ℝ)*X 2 1+(-1095333607/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1085704011/2500000000 : ℝ)*X 0 0+(2080714973/5000000000 : ℝ)*X 0 1+(4531790667/10000000000 : ℝ)*X 0 2+(1085704011/2500000000 : ℝ)*X 1 0+(2080714973/5000000000 : ℝ)*X 1 1+(4531790667/10000000000 : ℝ)*X 1 2+(1085704011/2500000000 : ℝ)*X 2 0+(2080714973/5000000000 : ℝ)*X 2 1+(4531790667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-3357297/16000000 : ℝ)*X 0 0+(523951251/1000000000 : ℝ)*X 0 1+(5419195187/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((8288589/15625000 : ℝ)*X 1 0+(-502577771/2500000000 : ℝ)*X 1 1+(2709597573/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304697213/10000000000 : ℝ)*X 2 0+(1354798823/2500000000 : ℝ)*X 2 1+(-2010310541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2171422979/5000000000 : ℝ)*X 0 0+(4530413499/10000000000 : ℝ)*X 0 1+(4162814547/10000000000 : ℝ)*X 0 2+(2171422979/5000000000 : ℝ)*X 1 0+(4530413499/10000000000 : ℝ)*X 1 1+(4162814547/10000000000 : ℝ)*X 1 2+(2171422979/5000000000 : ℝ)*X 2 0+(4530413499/10000000000 : ℝ)*X 2 1+(4162814547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (208740841505310267829627569/18662500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (387734433/25000000000000 : ℝ)*(base19) + (269740167/25000000000000 : ℝ)*(base23) + (171783997/100000000000000 : ℝ)*(lower2) + (69564271/25000000000000 : ℝ)*(upper3) + (1236841/5000000000000 : ℝ)*(lower4) + (822400408994237/20000000000000 : ℝ)*(major0) + (822400408994237/20000000000000 : ℝ)*(major1) + (2056001022485593/50000000000000 : ℝ)*(major2) + (1380970044651941/25000000000000 : ℝ)*(sp0) + (69048807519673/1250000000000 : ℝ)*(sp1) + (5523905073550903/100000000000000 : ℝ)*(sp2) + (164799912064/6103515625 : ℝ)*(sp3) + (25973903807/100000000000000 : ℝ)*(sp4) + (1580533949/10000000000000 : ℝ)*(sp7) + (1350048782298033/50000000000000 : ℝ)*(f.failure) + (1380976538127893/25000000000000 : ℝ)*(f.sum) + (77269667091061/7465000000000000000000000000 : ℝ)*base66 + (50150932937475023/37325000000000000000000000000000 : ℝ)*base67 + (255030721960358953/93312500000000000000000000000000 : ℝ)*base70 + (629969580425624977/37325000000000000000000000000000 : ℝ)*base72 + (8557630356877/3732500000000000000000000000 : ℝ)*base73 + (72511105527953547/93312500000000000000000000000000 : ℝ)*base75 + (182620358425619977/37325000000000000000000000000000 : ℝ)*base78 + (97428535913694977/37325000000000000000000000000000 : ℝ)*base80 + (1263644975301/373250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (12560677/5000000000000000000000 : ℝ)*base89 + (12560677/5000000000000000000000 : ℝ)*base91 + (37439323/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (227382035880490549828249341/46656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (457623729/50000000000000 : ℝ)*(base19) + (1420796241/100000000000000 : ℝ)*(base23) + (60837929/50000000000000 : ℝ)*(upper3) + (5619971/25000000000000 : ℝ)*(lower4) + (2071432076639653/50000000000000 : ℝ)*(major0) + (2071432076639653/50000000000000 : ℝ)*(major1) + (1035716038319827/25000000000000 : ℝ)*(major2) + (15234485471/100000000000000 : ℝ)*(sp1) + (37900877507/100000000000000 : ℝ)*(sp2) + (1827442439/100000000000000 : ℝ)*(sp3) + (556536534068777/10000000000000 : ℝ)*(sp4) + (5565349190954841/100000000000000 : ℝ)*(sp5) + (2782663009507011/50000000000000 : ℝ)*(sp6) + (2720360975976397/100000000000000 : ℝ)*(sp7) + (680090700854709/25000000000000 : ℝ)*(f.failure) + (556536534068777/10000000000000 : ℝ)*(f.sum) + (2869798409173/933125000000000000000000000 : ℝ)*base66 + (221002290936600787/93312500000000000000000000000000 : ℝ)*base67 + (121286533857285133/46656250000000000000000000000000 : ℝ)*base69 + (951944318875711713/93312500000000000000000000000000 : ℝ)*base72 + (4827599108511/7465000000000000000000000000 : ℝ)*base73 + (180482179940035133/46656250000000000000000000000000 : ℝ)*base75 + (354376370738375787/93312500000000000000000000000000 : ℝ)*base77 + (579804267737000787/93312500000000000000000000000000 : ℝ)*base79 + (4755527549003/1866250000000000000000000000 : ℝ)*base82 + (26352121/2500000000000000000000 : ℝ)*base89 + (26352121/2500000000000000000000 : ℝ)*base91 + (23647879/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1280_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2651/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10917/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1280_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1280_s5_0 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-262336247/1250000000 : ℝ)*x 0 + (338536023/625000000 : ℝ)*x 1 + (5241875751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262336247/1250000000 : ℝ)^265 ≤ (12765893757047/100000000000000 : ℝ)^201 := by
    have hnat : (262336247 : ℕ)^265*100000000000000^201 ≤ 12765893757047^201*1250000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262336247 1250000000 12765893757047 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338536023/625000000 : ℝ)^265 ≤ (22279772614789/50000000000000 : ℝ)^201 := by
    have hnat : (338536023 : ℕ)^265*50000000000000^201 ≤ 22279772614789^201*625000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338536023 625000000 22279772614789 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241875751/10000000000 : ℝ)^265 ≤ (10668640248971/25000000000000 : ℝ)^201 := by
    have hnat : (5241875751 : ℕ)^265*25000000000000^201 ≤ 10668640248971^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241875751 10000000000 10668640248971 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-262336247/1250000000 : ℝ), (338536023/625000000 : ℝ), (5241875751/10000000000 : ℝ)] ![(12765893757047/100000000000000 : ℝ), (22279772614789/50000000000000 : ℝ), (10668640248971/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-262336247/1250000000 : ℝ)|^265 ≤ (12765893757047/100000000000000 : ℝ)^201
        have hw : |(-262336247/1250000000 : ℝ)|=(262336247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338536023/625000000 : ℝ)|^265 ≤ (22279772614789/50000000000000 : ℝ)^201
        have hw : |(338536023/625000000 : ℝ)|=(338536023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241875751/10000000000 : ℝ)|^265 ≤ (10668640248971/25000000000000 : ℝ)^201
        have hw : |(5241875751/10000000000 : ℝ)|=(5241875751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s5_1 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2675070147/5000000000 : ℝ)*x 0 + (-273470941/1250000000 : ℝ)*x 1 + (5241875783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675070147/5000000000 : ℝ)^265 ≤ (21920198508979/50000000000000 : ℝ)^201 := by
    have hnat : (2675070147 : ℕ)^265*50000000000000^201 ≤ 21920198508979^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675070147 5000000000 21920198508979 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273470941/1250000000 : ℝ)^265 ≤ (3371260407133/25000000000000 : ℝ)^201 := by
    have hnat : (273470941 : ℕ)^265*25000000000000^201 ≤ 3371260407133^201*1250000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273470941 1250000000 3371260407133 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241875783/10000000000 : ℝ)^265 ≤ (42674561339349/100000000000000 : ℝ)^201 := by
    have hnat : (5241875783 : ℕ)^265*100000000000000^201 ≤ 42674561339349^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241875783 10000000000 42674561339349 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675070147/5000000000 : ℝ), (-273470941/1250000000 : ℝ), (5241875783/10000000000 : ℝ)] ![(21920198508979/50000000000000 : ℝ), (3371260407133/25000000000000 : ℝ), (42674561339349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675070147/5000000000 : ℝ)|^265 ≤ (21920198508979/50000000000000 : ℝ)^201
        have hw : |(2675070147/5000000000 : ℝ)|=(2675070147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273470941/1250000000 : ℝ)|^265 ≤ (3371260407133/25000000000000 : ℝ)^201
        have hw : |(-273470941/1250000000 : ℝ)|=(273470941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241875783/10000000000 : ℝ)|^265 ≤ (42674561339349/100000000000000 : ℝ)^201
        have hw : |(5241875783/10000000000 : ℝ)|=(5241875783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s5_2 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5350140371/10000000000 : ℝ)*x 0 + (5241875809/10000000000 : ℝ)*x 1 + (-218776739/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350140371/10000000000 : ℝ)^265 ≤ (43840397849817/100000000000000 : ℝ)^201 := by
    have hnat : (5350140371 : ℕ)^265*100000000000000^201 ≤ 43840397849817^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350140371 10000000000 43840397849817 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241875809/10000000000 : ℝ)^265 ≤ (21337280809207/50000000000000 : ℝ)^201 := by
    have hnat : (5241875809 : ℕ)^265*50000000000000^201 ≤ 21337280809207^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241875809 10000000000 21337280809207 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218776739/1000000000 : ℝ)^265 ≤ (6742520253541/50000000000000 : ℝ)^201 := by
    have hnat : (218776739 : ℕ)^265*50000000000000^201 ≤ 6742520253541^201*1000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218776739 1000000000 6742520253541 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350140371/10000000000 : ℝ), (5241875809/10000000000 : ℝ), (-218776739/1000000000 : ℝ)] ![(43840397849817/100000000000000 : ℝ), (21337280809207/50000000000000 : ℝ), (6742520253541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350140371/10000000000 : ℝ)|^265 ≤ (43840397849817/100000000000000 : ℝ)^201
        have hw : |(5350140371/10000000000 : ℝ)|=(5350140371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241875809/10000000000 : ℝ)|^265 ≤ (21337280809207/50000000000000 : ℝ)^201
        have hw : |(5241875809/10000000000 : ℝ)|=(5241875809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-218776739/1000000000 : ℝ)|^265 ≤ (6742520253541/50000000000000 : ℝ)^201
        have hw : |(-218776739/1000000000 : ℝ)|=(218776739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s5_3 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (868609607/2000000000 : ℝ)*x 0 + (1041969381/2500000000 : ℝ)*x 1 + (4525283863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868609607/2000000000 : ℝ)^265 ≤ (8325408829989/25000000000000 : ℝ)^201 := by
    have hnat : (868609607 : ℕ)^265*25000000000000^201 ≤ 8325408829989^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868609607 2000000000 8325408829989 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041969381/2500000000 : ℝ)^265 ≤ (31542262555979/100000000000000 : ℝ)^201 := by
    have hnat : (1041969381 : ℕ)^265*100000000000000^201 ≤ 31542262555979^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041969381 2500000000 31542262555979 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4525283863/10000000000 : ℝ)^265 ≤ (35156102100141/100000000000000 : ℝ)^201 := by
    have hnat : (4525283863 : ℕ)^265*100000000000000^201 ≤ 35156102100141^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525283863 10000000000 35156102100141 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(868609607/2000000000 : ℝ), (1041969381/2500000000 : ℝ), (4525283863/10000000000 : ℝ)] ![(8325408829989/25000000000000 : ℝ), (31542262555979/100000000000000 : ℝ), (35156102100141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(868609607/2000000000 : ℝ)|^265 ≤ (8325408829989/25000000000000 : ℝ)^201
        have hw : |(868609607/2000000000 : ℝ)|=(868609607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1041969381/2500000000 : ℝ)|^265 ≤ (31542262555979/100000000000000 : ℝ)^201
        have hw : |(1041969381/2500000000 : ℝ)|=(1041969381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4525283863/10000000000 : ℝ)|^265 ≤ (35156102100141/100000000000000 : ℝ)^201
        have hw : |(4525283863/10000000000 : ℝ)|=(4525283863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s5_4 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2098702867/10000000000 : ℝ)*x 0 + (2621251401/5000000000 : ℝ)*x 1 + (2707973137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098702867/10000000000 : ℝ)^265 ≤ (12765997137823/100000000000000 : ℝ)^201 := by
    have hnat : (2098702867 : ℕ)^265*100000000000000^201 ≤ 12765997137823^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098702867 10000000000 12765997137823 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621251401/5000000000 : ℝ)^265 ≤ (21340645716659/50000000000000 : ℝ)^201 := by
    have hnat : (2621251401 : ℕ)^265*50000000000000^201 ≤ 21340645716659^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621251401 5000000000 21340645716659 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707973137/5000000000 : ℝ)^265 ≤ (22276355709029/50000000000000 : ℝ)^201 := by
    have hnat : (2707973137 : ℕ)^265*50000000000000^201 ≤ 22276355709029^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707973137 5000000000 22276355709029 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2098702867/10000000000 : ℝ), (2621251401/5000000000 : ℝ), (2707973137/5000000000 : ℝ)] ![(12765997137823/100000000000000 : ℝ), (21340645716659/50000000000000 : ℝ), (22276355709029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2098702867/10000000000 : ℝ)|^265 ≤ (12765997137823/100000000000000 : ℝ)^201
        have hw : |(-2098702867/10000000000 : ℝ)|=(2098702867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621251401/5000000000 : ℝ)|^265 ≤ (21340645716659/50000000000000 : ℝ)^201
        have hw : |(2621251401/5000000000 : ℝ)|=(2621251401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707973137/5000000000 : ℝ)|^265 ≤ (22276355709029/50000000000000 : ℝ)^201
        have hw : |(2707973137/5000000000 : ℝ)|=(2707973137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s5_5 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5305481069/10000000000 : ℝ)*x 0 + (-503424203/2500000000 : ℝ)*x 1 + (5415946351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305481069/10000000000 : ℝ)^265 ≤ (43358569411999/100000000000000 : ℝ)^201 := by
    have hnat : (5305481069 : ℕ)^265*100000000000000^201 ≤ 43358569411999^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305481069 10000000000 43358569411999 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503424203/2500000000 : ℝ)^265 ≤ (3022179579021/25000000000000 : ℝ)^201 := by
    have hnat : (503424203 : ℕ)^265*25000000000000^201 ≤ 3022179579021^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503424203 2500000000 3022179579021 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415946351/10000000000 : ℝ)^265 ≤ (22276356126581/50000000000000 : ℝ)^201 := by
    have hnat : (5415946351 : ℕ)^265*50000000000000^201 ≤ 22276356126581^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415946351 10000000000 22276356126581 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305481069/10000000000 : ℝ), (-503424203/2500000000 : ℝ), (5415946351/10000000000 : ℝ)] ![(43358569411999/100000000000000 : ℝ), (3022179579021/25000000000000 : ℝ), (22276356126581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305481069/10000000000 : ℝ)|^265 ≤ (43358569411999/100000000000000 : ℝ)^201
        have hw : |(5305481069/10000000000 : ℝ)|=(5305481069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-503424203/2500000000 : ℝ)|^265 ≤ (3022179579021/25000000000000 : ℝ)^201
        have hw : |(-503424203/2500000000 : ℝ)|=(503424203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415946351/10000000000 : ℝ)|^265 ≤ (22276356126581/50000000000000 : ℝ)^201
        have hw : |(5415946351/10000000000 : ℝ)|=(5415946351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s5_6 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1326370291/2500000000 : ℝ)*x 0 + (5415946261/10000000000 : ℝ)*x 1 + (-1006848403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326370291/2500000000 : ℝ)^265 ≤ (43358570435583/100000000000000 : ℝ)^201 := by
    have hnat : (1326370291 : ℕ)^265*100000000000000^201 ≤ 43358570435583^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326370291 2500000000 43358570435583 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415946261/10000000000 : ℝ)^265 ≤ (44552711277067/100000000000000 : ℝ)^201 := by
    have hnat : (5415946261 : ℕ)^265*100000000000000^201 ≤ 44552711277067^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415946261 10000000000 44552711277067 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006848403/5000000000 : ℝ)^265 ≤ (3022179567149/25000000000000 : ℝ)^201 := by
    have hnat : (1006848403 : ℕ)^265*25000000000000^201 ≤ 3022179567149^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006848403 5000000000 3022179567149 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326370291/2500000000 : ℝ), (5415946261/10000000000 : ℝ), (-1006848403/5000000000 : ℝ)] ![(43358570435583/100000000000000 : ℝ), (44552711277067/100000000000000 : ℝ), (3022179567149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326370291/2500000000 : ℝ)|^265 ≤ (43358570435583/100000000000000 : ℝ)^201
        have hw : |(1326370291/2500000000 : ℝ)|=(1326370291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415946261/10000000000 : ℝ)|^265 ≤ (44552711277067/100000000000000 : ℝ)^201
        have hw : |(5415946261/10000000000 : ℝ)|=(5415946261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1006848403/5000000000 : ℝ)|^265 ≤ (3022179567149/25000000000000 : ℝ)^201
        have hw : |(-1006848403/5000000000 : ℝ)|=(1006848403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_s5_7 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4343074379/10000000000 : ℝ)*x 0 + (565500139/1250000000 : ℝ)*x 1 + (4169167509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343074379/10000000000 : ℝ)^265 ≤ (33301901639403/100000000000000 : ℝ)^201 := by
    have hnat : (4343074379 : ℕ)^265*100000000000000^201 ≤ 33301901639403^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343074379 10000000000 33301901639403 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565500139/1250000000 : ℝ)^265 ≤ (17571482077141/50000000000000 : ℝ)^201 := by
    have hnat : (565500139 : ℕ)^265*50000000000000^201 ≤ 17571482077141^201*1250000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565500139 1250000000 17571482077141 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4169167509/10000000000 : ℝ)^265 ≤ (31555134192537/100000000000000 : ℝ)^201 := by
    have hnat : (4169167509 : ℕ)^265*100000000000000^201 ≤ 31555134192537^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169167509 10000000000 31555134192537 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343074379/10000000000 : ℝ), (565500139/1250000000 : ℝ), (4169167509/10000000000 : ℝ)] ![(33301901639403/100000000000000 : ℝ), (17571482077141/50000000000000 : ℝ), (31555134192537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343074379/10000000000 : ℝ)|^265 ≤ (33301901639403/100000000000000 : ℝ)^201
        have hw : |(4343074379/10000000000 : ℝ)|=(4343074379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(565500139/1250000000 : ℝ)|^265 ≤ (17571482077141/50000000000000 : ℝ)^201
        have hw : |(565500139/1250000000 : ℝ)|=(565500139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4169167509/10000000000 : ℝ)|^265 ≤ (31555134192537/100000000000000 : ℝ)^201
        have hw : |(4169167509/10000000000 : ℝ)|=(4169167509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1280_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10917/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5491/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14679/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10917/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10917/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10917/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10917/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10917/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10917/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10917/100000 : ℝ) ^ (4239/1024 : ℝ) ≤ (325788607316047/3125000000000000000 : ℝ) := by
    have hpowers : (10917/100000 : ℝ)^4239 ≤ (325788607316047/3125000000000000000 : ℝ)^1024 := by
      have hnat : (10917 : ℕ)^4239*3125000000000000000^1024 ≤ 325788607316047^1024*100000^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10917 100000 325788607316047 3125000000000000000 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10917/100000 : ℝ)) (X := (325788607316047/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3687/25000 : ℝ) ^ (4239/1024 : ℝ) ≤ (2263223340828153/6250000000000000000 : ℝ) := by
    have hpowers : (3687/25000 : ℝ)^4239 ≤ (2263223340828153/6250000000000000000 : ℝ)^1024 := by
      have hnat : (3687 : ℕ)^4239*6250000000000000000^1024 ≤ 2263223340828153^1024*25000^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3687 25000 2263223340828153 6250000000000000000 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3687/25000 : ℝ)) (X := (2263223340828153/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562825788607316047/1562500000000000000 : ℝ) ≤ (10000503637513409/10000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (1562825788607316047/1562500000000000000 : ℝ)^1024 ≤ (10000503637513409/10000000000000000 : ℝ)^4239 := by
      have hnat : (1562825788607316047 : ℕ)^1024*10000000000000000^4239 ≤ 10000503637513409^4239*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562825788607316047 1562500000000000000 10000503637513409 10000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000503637513409/10000000000000000 : ℝ)) (X := (1562825788607316047/1562500000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252914800555460247/6250000000000000000 : ℝ) ≤ (10001126389448537/10000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (6252914800555460247/6250000000000000000 : ℝ)^1024 ≤ (10001126389448537/10000000000000000 : ℝ)^4239 := by
      have hnat : (6252914800555460247 : ℕ)^1024*10000000000000000^4239 ≤ 10001126389448537^4239*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252914800555460247 6250000000000000000 10001126389448537 10000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001126389448537/10000000000000000 : ℝ)) (X := (6252914800555460247/6250000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127263223340828153/3125000000000000000 : ℝ) ≤ (2000349828276733/2000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (3127263223340828153/3125000000000000000 : ℝ)^1024 ≤ (2000349828276733/2000000000000000 : ℝ)^4239 := by
      have hnat : (3127263223340828153 : ℕ)^1024*2000000000000000^4239 ≤ 2000349828276733^4239*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127263223340828153 3125000000000000000 2000349828276733 2000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000349828276733/2000000000000000 : ℝ)) (X := (3127263223340828153/3125000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(325788607316047/3125000000000000000 : ℝ) ≤ ((12766110756520761709/12770000000000000000 : ℝ)+2*(25947997297/15962500000000 : ℝ)*(10917/100000 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (12766110756520761709/12770000000000000000 : ℝ)+2*(25947997297/15962500000000 : ℝ)*(10917/100000 : ℝ)=(10000503637513409/10000000000000000 : ℝ) by norm_num, show 1+2*(325788607316047/3125000000000000000 : ℝ)=(1562825788607316047/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2263223340828153/6250000000000000000 : ℝ)+(325788607316047/3125000000000000000 : ℝ) ≤ ((12766110756520761709/12770000000000000000 : ℝ)+(25947997297/15962500000000 : ℝ)*((3687/25000 : ℝ)+(10917/100000 : ℝ)))^(4239/1024 : ℝ) := by
    rw [show (12766110756520761709/12770000000000000000 : ℝ)+(25947997297/15962500000000 : ℝ)*((3687/25000 : ℝ)+(10917/100000 : ℝ))=(10001126389448537/10000000000000000 : ℝ) by norm_num, show 1+(2263223340828153/6250000000000000000 : ℝ)+(325788607316047/3125000000000000000 : ℝ)=(6252914800555460247/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2263223340828153/6250000000000000000 : ℝ) ≤ ((12766110756520761709/12770000000000000000 : ℝ)+2*(25947997297/15962500000000 : ℝ)*(3687/25000 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (12766110756520761709/12770000000000000000 : ℝ)+2*(25947997297/15962500000000 : ℝ)*(3687/25000 : ℝ)=(2000349828276733/2000000000000000 : ℝ) by norm_num, show 1+2*(2263223340828153/6250000000000000000 : ℝ)=(3127263223340828153/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12766110756520761709/12770000000000000000 : ℝ)*(X 1 0+X 2 0)+(25947997297/15962500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (10917/100000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (12766110756520761709/12770000000000000000 : ℝ)) (alpha := (25947997297/15962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12766110756520761709/12770000000000000000 : ℝ)*(X 0 1+X 2 1)+(25947997297/15962500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (10917/100000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (12766110756520761709/12770000000000000000 : ℝ)) (alpha := (25947997297/15962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12766110756520761709/12770000000000000000 : ℝ)*(X 0 2+X 1 2)+(25947997297/15962500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (10917/100000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (12766110756520761709/12770000000000000000 : ℝ)) (alpha := (25947997297/15962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-262336247/1250000000 : ℝ)*X 0 0+(338536023/625000000 : ℝ)*X 0 1+(5241875751/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675070147/5000000000 : ℝ)*X 1 0+(-273470941/1250000000 : ℝ)*X 1 1+(5241875783/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350140371/10000000000 : ℝ)*X 2 0+(5241875809/10000000000 : ℝ)*X 2 1+(-218776739/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((868609607/2000000000 : ℝ)*X 0 0+(1041969381/2500000000 : ℝ)*X 0 1+(4525283863/10000000000 : ℝ)*X 0 2+(868609607/2000000000 : ℝ)*X 1 0+(1041969381/2500000000 : ℝ)*X 1 1+(4525283863/10000000000 : ℝ)*X 1 2+(868609607/2000000000 : ℝ)*X 2 0+(1041969381/2500000000 : ℝ)*X 2 1+(4525283863/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2098702867/10000000000 : ℝ)*X 0 0+(2621251401/5000000000 : ℝ)*X 0 1+(2707973137/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305481069/10000000000 : ℝ)*X 1 0+(-503424203/2500000000 : ℝ)*X 1 1+(5415946351/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326370291/2500000000 : ℝ)*X 2 0+(5415946261/10000000000 : ℝ)*X 2 1+(-1006848403/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4343074379/10000000000 : ℝ)*X 0 0+(565500139/1250000000 : ℝ)*X 0 1+(4169167509/10000000000 : ℝ)*X 0 2+(4343074379/10000000000 : ℝ)*X 1 0+(565500139/1250000000 : ℝ)*X 1 1+(4169167509/10000000000 : ℝ)*X 1 2+(4343074379/10000000000 : ℝ)*X 2 0+(565500139/1250000000 : ℝ)*X 2 1+(4169167509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4509547473152796709490514873/638500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (417876501/25000000000000 : ℝ)*(base19) + (411998771/25000000000000 : ℝ)*(base23) + (11330901/20000000000000 : ℝ)*(lower2) + (132082337/50000000000000 : ℝ)*(upper3) + (362379779/100000000000000 : ℝ)*(upper5) + (532631632650391/12500000000000 : ℝ)*(major0) + (532631632650391/12500000000000 : ℝ)*(major1) + (4261053061203129/100000000000000 : ℝ)*(major2) + (5724104167151831/100000000000000 : ℝ)*(sp0) + (2862067030962709/50000000000000 : ℝ)*(sp1) + (2862067042718169/50000000000000 : ℝ)*(sp2) + (2797953269416419/100000000000000 : ℝ)*(sp3) + (31566279591/100000000000000 : ℝ)*(sp4) + (527629199/3125000000000 : ℝ)*(sp7) + (699492538387697/25000000000000 : ℝ)*(f.failure) + (2862067866715711/50000000000000 : ℝ)*(f.sum) + (2353294541497/798125000000000000000000000 : ℝ)*base65 + (30010031536271781/159625000000000000000000000000000 : ℝ)*base68 + (17533316120118987461/1277000000000000000000000000000000 : ℝ)*base69 + (1311576817706146781/159625000000000000000000000000000 : ℝ)*base72 + (2645371271267/798125000000000000000000000 : ℝ)*base73 + (14476806047835987461/1277000000000000000000000000000000 : ℝ)*base75 + (519176625206096781/159625000000000000000000000000000 : ℝ)*base78 + (737377698283528219/159625000000000000000000000000000 : ℝ)*base79 + (33136271461863/6385000000000000000000000000 : ℝ)*base81 + (35038693/2500000000000000000000 : ℝ)*base89 + (35038693/2500000000000000000000 : ℝ)*base91 + (10038693/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (526761075596174310117549927/127700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (606588867/100000000000000 : ℝ)*(base19) + (773437221/100000000000000 : ℝ)*(base23) + (1998837/2500000000000 : ℝ)*(upper3) + (1755183/6250000000000 : ℝ)*(lower4) + (24217709/25000000000000 : ℝ)*(upper5) + (858379052917599/20000000000000 : ℝ)*(major0) + (858379052917599/20000000000000 : ℝ)*(major1) + (858379052917599/20000000000000 : ℝ)*(major2) + (557256721/4000000000000 : ℝ)*(sp1) + (15199977601/100000000000000 : ℝ)*(sp2) + (2882784034817751/50000000000000 : ℝ)*(sp4) + (5765553531628611/100000000000000 : ℝ)*(sp5) + (5765552096220679/100000000000000 : ℝ)*(sp6) + (1409111161020427/50000000000000 : ℝ)*(sp7) + (1409111161020427/50000000000000 : ℝ)*(f.failure) + (2882784034817751/50000000000000 : ℝ)*(f.sum) + (2157667843/15962500000000000000000000 : ℝ)*base66 + (1636299538546983309/255400000000000000000000000000000 : ℝ)*base68 + (260779485650216691/255400000000000000000000000000000 : ℝ)*base69 + (188983495918816691/255400000000000000000000000000000 : ℝ)*base71 + (65996934327/319250000000000000000000000 : ℝ)*base74 + (1612532900784983309/255400000000000000000000000000000 : ℝ)*base76 + (1997737580001616691/255400000000000000000000000000000 : ℝ)*base77 + (2876360807803416691/255400000000000000000000000000000 : ℝ)*base79 + (418267860113/127700000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (4581063/5000000000000000000000 : ℝ)*base89 + (4581063/5000000000000000000000 : ℝ)*base91 + (4581063/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1280_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10917/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5491/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1280_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1280_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16373/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1883/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5491/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1280_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1280_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1280_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16373/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1883/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5491/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1280_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

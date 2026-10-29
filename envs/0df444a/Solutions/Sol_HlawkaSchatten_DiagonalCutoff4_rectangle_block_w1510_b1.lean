-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1510_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:55:00.091045+00:00
-- url     : https://prove2.me/submissions/f9d24685-e11b-4dc2-849c-28c7f7bc852a

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
theorem support_rectangle_w1510_s3_0 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-7481863/40000000 : ℝ)*x 0 + (5436843201/10000000000 : ℝ)*x 1 + (5214522469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7481863/40000000 : ℝ)^4517 ≤ (11442375465311/100000000000000 : ℝ)^3493 := by
    have hnat : (7481863 : ℕ)^4517*100000000000000^3493 ≤ 11442375465311^3493*40000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7481863 40000000 11442375465311 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436843201/10000000000 : ℝ)^4517 ≤ (45473844817863/100000000000000 : ℝ)^3493 := by
    have hnat : (5436843201 : ℕ)^4517*100000000000000^3493 ≤ 45473844817863^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436843201 10000000000 45473844817863 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214522469/10000000000 : ℝ)^4517 ≤ (21541889850343/50000000000000 : ℝ)^3493 := by
    have hnat : (5214522469 : ℕ)^4517*50000000000000^3493 ≤ 21541889850343^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214522469 10000000000 21541889850343 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7481863/40000000 : ℝ), (5436843201/10000000000 : ℝ), (5214522469/10000000000 : ℝ)] ![(11442375465311/100000000000000 : ℝ), (45473844817863/100000000000000 : ℝ), (21541889850343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7481863/40000000 : ℝ)|^4517 ≤ (11442375465311/100000000000000 : ℝ)^3493
        have hw : |(-7481863/40000000 : ℝ)|=(7481863/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436843201/10000000000 : ℝ)|^4517 ≤ (45473844817863/100000000000000 : ℝ)^3493
        have hw : |(5436843201/10000000000 : ℝ)|=(5436843201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214522469/10000000000 : ℝ)|^4517 ≤ (21541889850343/50000000000000 : ℝ)^3493
        have hw : |(5214522469/10000000000 : ℝ)|=(5214522469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s3_1 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676288939/5000000000 : ℝ)*x 0 + (-99220579/500000000 : ℝ)*x 1 + (5214522571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676288939/5000000000 : ℝ)^4517 ≤ (11141127475797/25000000000000 : ℝ)^3493 := by
    have hnat : (2676288939 : ℕ)^4517*25000000000000^3493 ≤ 11141127475797^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676288939 5000000000 11141127475797 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (99220579/500000000 : ℝ)^4517 ≤ (6175854648669/50000000000000 : ℝ)^3493 := by
    have hnat : (99220579 : ℕ)^4517*50000000000000^3493 ≤ 6175854648669^3493*500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99220579 500000000 6175854648669 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214522571/10000000000 : ℝ)^4517 ≤ (1346368149703/3125000000000 : ℝ)^3493 := by
    have hnat : (5214522571 : ℕ)^4517*3125000000000^3493 ≤ 1346368149703^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214522571 10000000000 1346368149703 3125000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676288939/5000000000 : ℝ), (-99220579/500000000 : ℝ), (5214522571/10000000000 : ℝ)] ![(11141127475797/25000000000000 : ℝ), (6175854648669/50000000000000 : ℝ), (1346368149703/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676288939/5000000000 : ℝ)|^4517 ≤ (11141127475797/25000000000000 : ℝ)^3493
        have hw : |(2676288939/5000000000 : ℝ)|=(2676288939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-99220579/500000000 : ℝ)|^4517 ≤ (6175854648669/50000000000000 : ℝ)^3493
        have hw : |(-99220579/500000000 : ℝ)|=(99220579/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214522571/10000000000 : ℝ)|^4517 ≤ (1346368149703/3125000000000 : ℝ)^3493
        have hw : |(5214522571/10000000000 : ℝ)|=(5214522571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s3_2 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669072249/1250000000 : ℝ)*x 0 + (2607261231/5000000000 : ℝ)*x 1 + (-1984411571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669072249/1250000000 : ℝ)^4517 ≤ (22282255565289/50000000000000 : ℝ)^3493 := by
    have hnat : (669072249 : ℕ)^4517*50000000000000^3493 ≤ 22282255565289^3493*1250000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669072249 1250000000 22282255565289 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607261231/5000000000 : ℝ)^4517 ≤ (8616755925179/20000000000000 : ℝ)^3493 := by
    have hnat : (2607261231 : ℕ)^4517*20000000000000^3493 ≤ 8616755925179^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607261231 5000000000 8616755925179 20000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1984411571/10000000000 : ℝ)^4517 ≤ (192995456639/1562500000000 : ℝ)^3493 := by
    have hnat : (1984411571 : ℕ)^4517*1562500000000^3493 ≤ 192995456639^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984411571 10000000000 192995456639 1562500000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669072249/1250000000 : ℝ), (2607261231/5000000000 : ℝ), (-1984411571/10000000000 : ℝ)] ![(22282255565289/50000000000000 : ℝ), (8616755925179/20000000000000 : ℝ), (192995456639/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669072249/1250000000 : ℝ)|^4517 ≤ (22282255565289/50000000000000 : ℝ)^3493
        have hw : |(669072249/1250000000 : ℝ)|=(669072249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607261231/5000000000 : ℝ)|^4517 ≤ (8616755925179/20000000000000 : ℝ)^3493
        have hw : |(2607261231/5000000000 : ℝ)|=(2607261231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1984411571/10000000000 : ℝ)|^4517 ≤ (192995456639/1562500000000 : ℝ)^3493
        have hw : |(-1984411571/10000000000 : ℝ)|=(1984411571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s3_3 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4270385803/10000000000 : ℝ)*x 0 + (4024982917/10000000000 : ℝ)*x 1 + (4528404273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4270385803/10000000000 : ℝ)^4517 ≤ (166381750557/500000000000 : ℝ)^3493 := by
    have hnat : (4270385803 : ℕ)^4517*500000000000^3493 ≤ 166381750557^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4270385803 10000000000 166381750557 500000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4024982917/10000000000 : ℝ)^4517 ≤ (3853075974699/12500000000000 : ℝ)^3493 := by
    have hnat : (4024982917 : ℕ)^4517*12500000000000^3493 ≤ 3853075974699^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024982917 10000000000 3853075974699 12500000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4528404273/10000000000 : ℝ)^4517 ≤ (7179808414289/20000000000000 : ℝ)^3493 := by
    have hnat : (4528404273 : ℕ)^4517*20000000000000^3493 ≤ 7179808414289^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528404273 10000000000 7179808414289 20000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4270385803/10000000000 : ℝ), (4024982917/10000000000 : ℝ), (4528404273/10000000000 : ℝ)] ![(166381750557/500000000000 : ℝ), (3853075974699/12500000000000 : ℝ), (7179808414289/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4270385803/10000000000 : ℝ)|^4517 ≤ (166381750557/500000000000 : ℝ)^3493
        have hw : |(4270385803/10000000000 : ℝ)|=(4270385803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4024982917/10000000000 : ℝ)|^4517 ≤ (3853075974699/12500000000000 : ℝ)^3493
        have hw : |(4024982917/10000000000 : ℝ)|=(4024982917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4528404273/10000000000 : ℝ)|^4517 ≤ (7179808414289/20000000000000 : ℝ)^3493
        have hw : |(4528404273/10000000000 : ℝ)|=(4528404273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s3_4 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1870496979/10000000000 : ℝ)*x 0 + (2607849969/5000000000 : ℝ)*x 1 + (5435657139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1870496979/10000000000 : ℝ)^4517 ≤ (5721311255443/50000000000000 : ℝ)^3493 := by
    have hnat : (1870496979 : ℕ)^4517*50000000000000^3493 ≤ 5721311255443^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870496979 10000000000 5721311255443 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607849969/5000000000 : ℝ)^4517 ≤ (21548180342397/50000000000000 : ℝ)^3493 := by
    have hnat : (2607849969 : ℕ)^4517*50000000000000^3493 ≤ 21548180342397^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607849969 5000000000 21548180342397 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435657139/10000000000 : ℝ)^4517 ≤ (45461016790551/100000000000000 : ℝ)^3493 := by
    have hnat : (5435657139 : ℕ)^4517*100000000000000^3493 ≤ 45461016790551^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435657139 10000000000 45461016790551 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1870496979/10000000000 : ℝ), (2607849969/5000000000 : ℝ), (5435657139/10000000000 : ℝ)] ![(5721311255443/50000000000000 : ℝ), (21548180342397/50000000000000 : ℝ), (45461016790551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1870496979/10000000000 : ℝ)|^4517 ≤ (5721311255443/50000000000000 : ℝ)^3493
        have hw : |(-1870496979/10000000000 : ℝ)|=(1870496979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607849969/5000000000 : ℝ)|^4517 ≤ (21548180342397/50000000000000 : ℝ)^3493
        have hw : |(2607849969/5000000000 : ℝ)|=(2607849969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435657139/10000000000 : ℝ)|^4517 ≤ (45461016790551/100000000000000 : ℝ)^3493
        have hw : |(5435657139/10000000000 : ℝ)|=(5435657139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s3_5 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323557971/2500000000 : ℝ)*x 0 + (-70531073/400000000 : ℝ)*x 1 + (5435657349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323557971/2500000000 : ℝ)^4517 ≤ (43937329574241/100000000000000 : ℝ)^3493 := by
    have hnat : (1323557971 : ℕ)^4517*100000000000000^3493 ≤ 43937329574241^3493*2500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323557971 2500000000 43937329574241 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70531073/400000000 : ℝ)^4517 ≤ (2650412835741/25000000000000 : ℝ)^3493 := by
    have hnat : (70531073 : ℕ)^4517*25000000000000^3493 ≤ 2650412835741^3493*400000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70531073 400000000 2650412835741 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435657349/10000000000 : ℝ)^4517 ≤ (11365254765441/25000000000000 : ℝ)^3493 := by
    have hnat : (5435657349 : ℕ)^4517*25000000000000^3493 ≤ 11365254765441^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435657349 10000000000 11365254765441 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323557971/2500000000 : ℝ), (-70531073/400000000 : ℝ), (5435657349/10000000000 : ℝ)] ![(43937329574241/100000000000000 : ℝ), (2650412835741/25000000000000 : ℝ), (11365254765441/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323557971/2500000000 : ℝ)|^4517 ≤ (43937329574241/100000000000000 : ℝ)^3493
        have hw : |(1323557971/2500000000 : ℝ)|=(1323557971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-70531073/400000000 : ℝ)|^4517 ≤ (2650412835741/25000000000000 : ℝ)^3493
        have hw : |(-70531073/400000000 : ℝ)|=(70531073/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435657349/10000000000 : ℝ)|^4517 ≤ (11365254765441/25000000000000 : ℝ)^3493
        have hw : |(5435657349/10000000000 : ℝ)|=(5435657349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s3_6 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647116079/5000000000 : ℝ)*x 0 + (2717828517/5000000000 : ℝ)*x 1 + (-352655377/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647116079/5000000000 : ℝ)^4517 ≤ (43937332514819/100000000000000 : ℝ)^3493 := by
    have hnat : (2647116079 : ℕ)^4517*100000000000000^3493 ≤ 43937332514819^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647116079 5000000000 43937332514819 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717828517/5000000000 : ℝ)^4517 ≤ (9092203130989/20000000000000 : ℝ)^3493 := by
    have hnat : (2717828517 : ℕ)^4517*20000000000000^3493 ≤ 9092203130989^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717828517 5000000000 9092203130989 20000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352655377/2000000000 : ℝ)^4517 ≤ (2650412952367/25000000000000 : ℝ)^3493 := by
    have hnat : (352655377 : ℕ)^4517*25000000000000^3493 ≤ 2650412952367^3493*2000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352655377 2000000000 2650412952367 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647116079/5000000000 : ℝ), (2717828517/5000000000 : ℝ), (-352655377/2000000000 : ℝ)] ![(43937332514819/100000000000000 : ℝ), (9092203130989/20000000000000 : ℝ), (2650412952367/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647116079/5000000000 : ℝ)|^4517 ≤ (43937332514819/100000000000000 : ℝ)^3493
        have hw : |(2647116079/5000000000 : ℝ)|=(2647116079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717828517/5000000000 : ℝ)|^4517 ≤ (9092203130989/20000000000000 : ℝ)^3493
        have hw : |(2717828517/5000000000 : ℝ)|=(2717828517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-352655377/2000000000 : ℝ)|^4517 ≤ (2650412952367/25000000000000 : ℝ)^3493
        have hw : |(-352655377/2000000000 : ℝ)|=(352655377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s3_7 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (854091489/2000000000 : ℝ)*x 0 + (452573831/1000000000 : ℝ)*x 1 + (2013834599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854091489/2000000000 : ℝ)^4517 ≤ (16638536015511/50000000000000 : ℝ)^3493 := by
    have hnat : (854091489 : ℕ)^4517*50000000000000^3493 ≤ 16638536015511^3493*2000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854091489 2000000000 16638536015511 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (452573831/1000000000 : ℝ)^4517 ≤ (35871714199917/100000000000000 : ℝ)^3493 := by
    have hnat : (452573831 : ℕ)^4517*100000000000000^3493 ≤ 35871714199917^3493*1000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452573831 1000000000 35871714199917 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2013834599/5000000000 : ℝ)^4517 ≤ (15425606878993/50000000000000 : ℝ)^3493 := by
    have hnat : (2013834599 : ℕ)^4517*50000000000000^3493 ≤ 15425606878993^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013834599 5000000000 15425606878993 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(854091489/2000000000 : ℝ), (452573831/1000000000 : ℝ), (2013834599/5000000000 : ℝ)] ![(16638536015511/50000000000000 : ℝ), (35871714199917/100000000000000 : ℝ), (15425606878993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(854091489/2000000000 : ℝ)|^4517 ≤ (16638536015511/50000000000000 : ℝ)^3493
        have hw : |(854091489/2000000000 : ℝ)|=(854091489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(452573831/1000000000 : ℝ)|^4517 ≤ (35871714199917/100000000000000 : ℝ)^3493
        have hw : |(452573831/1000000000 : ℝ)|=(452573831/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2013834599/5000000000 : ℝ)|^4517 ≤ (15425606878993/50000000000000 : ℝ)^3493
        have hw : |(2013834599/5000000000 : ℝ)|=(2013834599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1510_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4001/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2607/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2711/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15551/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4001/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2607/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4001/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2607/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4001/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2607/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4001/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2607/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4001/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2607/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4001/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2607/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2607/25000 : ℝ) ^ (4515/1024 : ℝ) ≤ (2344454969284327/50000000000000000000 : ℝ) := by
    have hpowers : (2607/25000 : ℝ)^4515 ≤ (2344454969284327/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2607 : ℕ)^4515*50000000000000000000^1024 ≤ 2344454969284327^1024*25000^4515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2607 25000 2344454969284327 50000000000000000000 4515 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2607/25000 : ℝ)) (X := (2344454969284327/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4001/25000 : ℝ) ^ (4515/1024 : ℝ) ≤ (30995643318013203/100000000000000000000 : ℝ) := by
    have hpowers : (4001/25000 : ℝ)^4515 ≤ (30995643318013203/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4001 : ℕ)^4515*100000000000000000000^1024 ≤ 30995643318013203^1024*25000^4515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001 25000 30995643318013203 100000000000000000000 4515 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4001/25000 : ℝ)) (X := (30995643318013203/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002344454969284327/25000000000000000000 : ℝ) ≤ (10000212680828881/10000000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (25002344454969284327/25000000000000000000 : ℝ)^1024 ≤ (10000212680828881/10000000000000000 : ℝ)^4515 := by
      have hnat : (25002344454969284327 : ℕ)^1024*10000000000000000^4515 ≤ 10000212680828881^4515*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002344454969284327 25000000000000000000 10000212680828881 10000000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000212680828881/10000000000000000 : ℝ)) (X := (25002344454969284327/25000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035684553256581857/100000000000000000000 : ℝ) ≤ (2500202303114781/2500000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (100035684553256581857/100000000000000000000 : ℝ)^1024 ≤ (2500202303114781/2500000000000000 : ℝ)^4515 := by
      have hnat : (100035684553256581857 : ℕ)^1024*2500000000000000^4515 ≤ 2500202303114781^4515*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035684553256581857 100000000000000000000 2500202303114781 2500000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500202303114781/2500000000000000 : ℝ)) (X := (100035684553256581857/100000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030995643318013203/50000000000000000000 : ℝ) ≤ (10001405744089367/10000000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (50030995643318013203/50000000000000000000 : ℝ)^1024 ≤ (10001405744089367/10000000000000000 : ℝ)^4515 := by
      have hnat : (50030995643318013203 : ℕ)^1024*10000000000000000^4515 ≤ 10001405744089367^4515*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030995643318013203 50000000000000000000 10001405744089367 10000000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001405744089367/10000000000000000 : ℝ)) (X := (50030995643318013203/50000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2344454969284327/50000000000000000000 : ℝ) ≤ ((1742148270144421639/1742500000000000000 : ℝ)+2*(596531630243/557600000000000 : ℝ)*(2607/25000 : ℝ))^(4515/1024 : ℝ) := by
    rw [show (1742148270144421639/1742500000000000000 : ℝ)+2*(596531630243/557600000000000 : ℝ)*(2607/25000 : ℝ)=(10000212680828881/10000000000000000 : ℝ) by norm_num, show 1+2*(2344454969284327/50000000000000000000 : ℝ)=(25002344454969284327/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30995643318013203/100000000000000000000 : ℝ)+(2344454969284327/50000000000000000000 : ℝ) ≤ ((1742148270144421639/1742500000000000000 : ℝ)+(596531630243/557600000000000 : ℝ)*((4001/25000 : ℝ)+(2607/25000 : ℝ)))^(4515/1024 : ℝ) := by
    rw [show (1742148270144421639/1742500000000000000 : ℝ)+(596531630243/557600000000000 : ℝ)*((4001/25000 : ℝ)+(2607/25000 : ℝ))=(2500202303114781/2500000000000000 : ℝ) by norm_num, show 1+(30995643318013203/100000000000000000000 : ℝ)+(2344454969284327/50000000000000000000 : ℝ)=(100035684553256581857/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30995643318013203/100000000000000000000 : ℝ) ≤ ((1742148270144421639/1742500000000000000 : ℝ)+2*(596531630243/557600000000000 : ℝ)*(4001/25000 : ℝ))^(4515/1024 : ℝ) := by
    rw [show (1742148270144421639/1742500000000000000 : ℝ)+2*(596531630243/557600000000000 : ℝ)*(4001/25000 : ℝ)=(10001405744089367/10000000000000000 : ℝ) by norm_num, show 1+2*(30995643318013203/100000000000000000000 : ℝ)=(50030995643318013203/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1742148270144421639/1742500000000000000 : ℝ)*(X 1 0+X 2 0)+(596531630243/557600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (2607/25000 : ℝ)) (hi := (4001/25000 : ℝ)) (c := (1742148270144421639/1742500000000000000 : ℝ)) (alpha := (596531630243/557600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1742148270144421639/1742500000000000000 : ℝ)*(X 0 1+X 2 1)+(596531630243/557600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (2607/25000 : ℝ)) (hi := (4001/25000 : ℝ)) (c := (1742148270144421639/1742500000000000000 : ℝ)) (alpha := (596531630243/557600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1742148270144421639/1742500000000000000 : ℝ)*(X 0 2+X 1 2)+(596531630243/557600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (2607/25000 : ℝ)) (hi := (4001/25000 : ℝ)) (c := (1742148270144421639/1742500000000000000 : ℝ)) (alpha := (596531630243/557600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-7481863/40000000 : ℝ)*X 0 0+(5436843201/10000000000 : ℝ)*X 0 1+(5214522469/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676288939/5000000000 : ℝ)*X 1 0+(-99220579/500000000 : ℝ)*X 1 1+(5214522571/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669072249/1250000000 : ℝ)*X 2 0+(2607261231/5000000000 : ℝ)*X 2 1+(-1984411571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4270385803/10000000000 : ℝ)*X 0 0+(4024982917/10000000000 : ℝ)*X 0 1+(4528404273/10000000000 : ℝ)*X 0 2+(4270385803/10000000000 : ℝ)*X 1 0+(4024982917/10000000000 : ℝ)*X 1 1+(4528404273/10000000000 : ℝ)*X 1 2+(4270385803/10000000000 : ℝ)*X 2 0+(4024982917/10000000000 : ℝ)*X 2 1+(4528404273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1870496979/10000000000 : ℝ)*X 0 0+(2607849969/5000000000 : ℝ)*X 0 1+(5435657139/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323557971/2500000000 : ℝ)*X 1 0+(-70531073/400000000 : ℝ)*X 1 1+(5435657349/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647116079/5000000000 : ℝ)*X 2 0+(2717828517/5000000000 : ℝ)*X 2 1+(-352655377/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((854091489/2000000000 : ℝ)*X 0 0+(452573831/1000000000 : ℝ)*X 0 1+(2013834599/5000000000 : ℝ)*X 0 2+(854091489/2000000000 : ℝ)*X 1 0+(452573831/1000000000 : ℝ)*X 1 1+(2013834599/5000000000 : ℝ)*X 1 2+(854091489/2000000000 : ℝ)*X 2 0+(452573831/1000000000 : ℝ)*X 2 1+(2013834599/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1284686930324544033465273/531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (946815403/100000000000000 : ℝ)*(base19) + (150525727/20000000000000 : ℝ)*(base23) + (255236491/100000000000000 : ℝ)*(upper3) + (15521751/10000000000000 : ℝ)*(upper4) + (37374921/50000000000000 : ℝ)*(upper5) + (810556259208193/25000000000000 : ℝ)*(major0) + (810556259208193/25000000000000 : ℝ)*(major1) + (810556259208193/25000000000000 : ℝ)*(major2) + (4498018699058901/100000000000000 : ℝ)*(sp0) + (2249014387238257/50000000000000 : ℝ)*(sp1) + (2249014484331641/50000000000000 : ℝ)*(sp2) + (496603109160823/25000000000000 : ℝ)*(sp3) + (1377779127/12500000000000 : ℝ)*(sp4) + (195878063/2500000000000 : ℝ)*(sp7) + (496605067941453/25000000000000 : ℝ)*(f.failure) + (4498029721291917/100000000000000 : ℝ)*(f.sum) + (28465152310759/6970000000000000000000000000 : ℝ)*base65 + (314109616488482399/21781250000000000000000000000000 : ℝ)*base68 + (197419932551357399/21781250000000000000000000000000 : ℝ)*base70 + (153211154526451149/21781250000000000000000000000000 : ℝ)*base72 + (8286308171781/6970000000000000000000000000 : ℝ)*base74 + (227947436976263649/21781250000000000000000000000000 : ℝ)*base76 + (175531108246576149/21781250000000000000000000000000 : ℝ)*base78 + (290814682331451149/21781250000000000000000000000000 : ℝ)*base80 + (34820787292519/6970000000000000000000000000 : ℝ)*base81 + (851897/250000000000000000000 : ℝ)*base89 + (851897/250000000000000000000 : ℝ)*base91 + (851897/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29053650831972202614967209/10890625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (271361901/100000000000000 : ℝ)*(base19) + (579446293/100000000000000 : ℝ)*(base23) + (37322703/50000000000000 : ℝ)*(upper3) + (15340487/50000000000000 : ℝ)*(lower4) + (14526311/50000000000000 : ℝ)*(upper5) + (204815401149417/6250000000000 : ℝ)*(major0) + (204815401149417/6250000000000 : ℝ)*(major1) + (204815401149417/6250000000000 : ℝ)*(major2) + (6542913403/100000000000000 : ℝ)*(sp1) + (3944726353/50000000000000 : ℝ)*(sp2) + (4546338393035351/100000000000000 : ℝ)*(sp4) + (2273165789380023/50000000000000 : ℝ)*(sp5) + (142072810129261/3125000000000 : ℝ)*(sp6) + (31371161794069/1562500000000 : ℝ)*(sp7) + (31371161794069/1562500000000 : ℝ)*(f.failure) + (4546338393035351/100000000000000 : ℝ)*(f.sum) + (14053253294473/3485000000000000000000000000 : ℝ)*base66 + (1973315423768739/1361328125000000000000000000000 : ℝ)*base68 + (96205315662384287/10890625000000000000000000000000 : ℝ)*base70 + (21616009448084353/2722656250000000000000000000000 : ℝ)*base72 + (12861890067/54453125000000000000000000 : ℝ)*base74 + (18303328716540537/10890625000000000000000000000000 : ℝ)*base76 + (80857214080465581/5445312500000000000000000000000 : ℝ)*base78 + (43859953177059331/5445312500000000000000000000000 : ℝ)*base80 + (5405467266127/871250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (220481/15625000000000000000 : ℝ)*base89 + (220481/15625000000000000000 : ℝ)*base91 + (220481/15625000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1510_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4001/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2607/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2711/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15551/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1510_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1510_s4_0 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-935457193/5000000000 : ℝ)*x 0 + (217355983/400000000 : ℝ)*x 1 + (5217169729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (935457193/5000000000 : ℝ)^4517 ≤ (11445924639597/100000000000000 : ℝ)^3493 := by
    have hnat : (935457193 : ℕ)^4517*100000000000000^3493 ≤ 11445924639597^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935457193 5000000000 11445924639597 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217355983/400000000 : ℝ)^4517 ≤ (710031392321/1562500000000 : ℝ)^3493 := by
    have hnat : (217355983 : ℕ)^4517*1562500000000^3493 ≤ 710031392321^3493*400000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217355983 400000000 710031392321 1562500000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217169729/10000000000 : ℝ)^4517 ≤ (43112066230287/100000000000000 : ℝ)^3493 := by
    have hnat : (5217169729 : ℕ)^4517*100000000000000^3493 ≤ 43112066230287^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217169729 10000000000 43112066230287 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-935457193/5000000000 : ℝ), (217355983/400000000 : ℝ), (5217169729/10000000000 : ℝ)] ![(11445924639597/100000000000000 : ℝ), (710031392321/1562500000000 : ℝ), (43112066230287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-935457193/5000000000 : ℝ)|^4517 ≤ (11445924639597/100000000000000 : ℝ)^3493
        have hw : |(-935457193/5000000000 : ℝ)|=(935457193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217355983/400000000 : ℝ)|^4517 ≤ (710031392321/1562500000000 : ℝ)^3493
        have hw : |(217355983/400000000 : ℝ)|=(217355983/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217169729/10000000000 : ℝ)|^4517 ≤ (43112066230287/100000000000000 : ℝ)^3493
        have hw : |(5217169729/10000000000 : ℝ)|=(5217169729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s4_1 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351808273/10000000000 : ℝ)*x 0 + (-1981927133/10000000000 : ℝ)*x 1 + (5217169191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351808273/10000000000 : ℝ)^4517 ≤ (8911244813289/20000000000000 : ℝ)^3493 := by
    have hnat : (5351808273 : ℕ)^4517*20000000000000^3493 ≤ 8911244813289^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351808273 10000000000 8911244813289 20000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1981927133/10000000000 : ℝ)^4517 ≤ (6165857714669/50000000000000 : ℝ)^3493 := by
    have hnat : (1981927133 : ℕ)^4517*50000000000000^3493 ≤ 6165857714669^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981927133 10000000000 6165857714669 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217169191/10000000000 : ℝ)^4517 ≤ (673625945019/1562500000000 : ℝ)^3493 := by
    have hnat : (5217169191 : ℕ)^4517*1562500000000^3493 ≤ 673625945019^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217169191 10000000000 673625945019 1562500000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351808273/10000000000 : ℝ), (-1981927133/10000000000 : ℝ), (5217169191/10000000000 : ℝ)] ![(8911244813289/20000000000000 : ℝ), (6165857714669/50000000000000 : ℝ), (673625945019/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351808273/10000000000 : ℝ)|^4517 ≤ (8911244813289/20000000000000 : ℝ)^3493
        have hw : |(5351808273/10000000000 : ℝ)|=(5351808273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1981927133/10000000000 : ℝ)|^4517 ≤ (6165857714669/50000000000000 : ℝ)^3493
        have hw : |(-1981927133/10000000000 : ℝ)|=(1981927133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217169191/10000000000 : ℝ)|^4517 ≤ (673625945019/1562500000000 : ℝ)^3493
        have hw : |(5217169191/10000000000 : ℝ)|=(5217169191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s4_2 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070361551/2000000000 : ℝ)*x 0 + (2608584887/5000000000 : ℝ)*x 1 + (-1981927053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070361551/2000000000 : ℝ)^4517 ≤ (22278109244797/50000000000000 : ℝ)^3493 := by
    have hnat : (1070361551 : ℕ)^4517*50000000000000^3493 ≤ 22278109244797^3493*2000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070361551 2000000000 22278109244797 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608584887/5000000000 : ℝ)^4517 ≤ (43112066711157/100000000000000 : ℝ)^3493 := by
    have hnat : (2608584887 : ℕ)^4517*100000000000000^3493 ≤ 43112066711157^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608584887 5000000000 43112066711157 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1981927053/10000000000 : ℝ)^4517 ≤ (12331714785647/100000000000000 : ℝ)^3493 := by
    have hnat : (1981927053 : ℕ)^4517*100000000000000^3493 ≤ 12331714785647^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981927053 10000000000 12331714785647 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070361551/2000000000 : ℝ), (2608584887/5000000000 : ℝ), (-1981927053/10000000000 : ℝ)] ![(22278109244797/50000000000000 : ℝ), (43112066711157/100000000000000 : ℝ), (12331714785647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070361551/2000000000 : ℝ)|^4517 ≤ (22278109244797/50000000000000 : ℝ)^3493
        have hw : |(1070361551/2000000000 : ℝ)|=(1070361551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608584887/5000000000 : ℝ)|^4517 ≤ (43112066711157/100000000000000 : ℝ)^3493
        have hw : |(2608584887/5000000000 : ℝ)|=(2608584887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1981927053/10000000000 : ℝ)|^4517 ≤ (12331714785647/100000000000000 : ℝ)^3493
        have hw : |(-1981927053/10000000000 : ℝ)|=(1981927053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s4_3 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4270665947/10000000000 : ℝ)*x 0 + (4031281047/10000000000 : ℝ)*x 1 + (2261020971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4270665947/10000000000 : ℝ)^4517 ≤ (4159896634619/12500000000000 : ℝ)^3493 := by
    have hnat : (4270665947 : ℕ)^4517*12500000000000^3493 ≤ 4159896634619^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4270665947 10000000000 4159896634619 12500000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4031281047/10000000000 : ℝ)^4517 ≤ (15443497549871/50000000000000 : ℝ)^3493 := by
    have hnat : (4031281047 : ℕ)^4517*50000000000000^3493 ≤ 15443497549871^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031281047 10000000000 15443497549871 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2261020971/5000000000 : ℝ)^4517 ≤ (17916915903969/50000000000000 : ℝ)^3493 := by
    have hnat : (2261020971 : ℕ)^4517*50000000000000^3493 ≤ 17916915903969^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261020971 5000000000 17916915903969 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4270665947/10000000000 : ℝ), (4031281047/10000000000 : ℝ), (2261020971/5000000000 : ℝ)] ![(4159896634619/12500000000000 : ℝ), (15443497549871/50000000000000 : ℝ), (17916915903969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4270665947/10000000000 : ℝ)|^4517 ≤ (4159896634619/12500000000000 : ℝ)^3493
        have hw : |(4270665947/10000000000 : ℝ)|=(4270665947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4031281047/10000000000 : ℝ)|^4517 ≤ (15443497549871/50000000000000 : ℝ)^3493
        have hw : |(4031281047/10000000000 : ℝ)|=(4031281047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2261020971/5000000000 : ℝ)|^4517 ≤ (17916915903969/50000000000000 : ℝ)^3493
        have hw : |(2261020971/5000000000 : ℝ)|=(2261020971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s4_4 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1870944169/10000000000 : ℝ)*x 0 + (130457217/250000000 : ℝ)*x 1 + (135819301/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1870944169/10000000000 : ℝ)^4517 ≤ (11446160262731/100000000000000 : ℝ)^3493 := by
    have hnat : (1870944169 : ℕ)^4517*100000000000000^3493 ≤ 11446160262731^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870944169 10000000000 11446160262731 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130457217/250000000 : ℝ)^4517 ≤ (43124023722257/100000000000000 : ℝ)^3493 := by
    have hnat : (130457217 : ℕ)^4517*100000000000000^3493 ≤ 43124023722257^3493*250000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130457217 250000000 43124023722257 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135819301/250000000 : ℝ)^4517 ≤ (22714908002761/50000000000000 : ℝ)^3493 := by
    have hnat : (135819301 : ℕ)^4517*50000000000000^3493 ≤ 22714908002761^3493*250000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135819301 250000000 22714908002761 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1870944169/10000000000 : ℝ), (130457217/250000000 : ℝ), (135819301/250000000 : ℝ)] ![(11446160262731/100000000000000 : ℝ), (43124023722257/100000000000000 : ℝ), (22714908002761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1870944169/10000000000 : ℝ)|^4517 ≤ (11446160262731/100000000000000 : ℝ)^3493
        have hw : |(-1870944169/10000000000 : ℝ)|=(1870944169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130457217/250000000 : ℝ)|^4517 ≤ (43124023722257/100000000000000 : ℝ)^3493
        have hw : |(130457217/250000000 : ℝ)|=(130457217/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135819301/250000000 : ℝ)|^4517 ≤ (22714908002761/50000000000000 : ℝ)^3493
        have hw : |(135819301/250000000 : ℝ)|=(135819301/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s4_5 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058986143/2000000000 : ℝ)*x 0 + (-883162337/5000000000 : ℝ)*x 1 + (5432772021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058986143/2000000000 : ℝ)^4517 ≤ (43944829600223/100000000000000 : ℝ)^3493 := by
    have hnat : (1058986143 : ℕ)^4517*100000000000000^3493 ≤ 43944829600223^3493*2000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058986143 2000000000 43944829600223 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (883162337/5000000000 : ℝ)^4517 ≤ (2656338648901/25000000000000 : ℝ)^3493 := by
    have hnat : (883162337 : ℕ)^4517*25000000000000^3493 ≤ 2656338648901^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883162337 5000000000 2656338648901 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432772021/10000000000 : ℝ)^4517 ≤ (177460217969/390625000000 : ℝ)^3493 := by
    have hnat : (5432772021 : ℕ)^4517*390625000000^3493 ≤ 177460217969^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432772021 10000000000 177460217969 390625000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058986143/2000000000 : ℝ), (-883162337/5000000000 : ℝ), (5432772021/10000000000 : ℝ)] ![(43944829600223/100000000000000 : ℝ), (2656338648901/25000000000000 : ℝ), (177460217969/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058986143/2000000000 : ℝ)|^4517 ≤ (43944829600223/100000000000000 : ℝ)^3493
        have hw : |(1058986143/2000000000 : ℝ)|=(1058986143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-883162337/5000000000 : ℝ)|^4517 ≤ (2656338648901/25000000000000 : ℝ)^3493
        have hw : |(-883162337/5000000000 : ℝ)|=(883162337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432772021/10000000000 : ℝ)|^4517 ≤ (177460217969/390625000000 : ℝ)^3493
        have hw : |(5432772021/10000000000 : ℝ)|=(5432772021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s4_6 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294930687/10000000000 : ℝ)*x 0 + (5432772043/10000000000 : ℝ)*x 1 + (-44158117/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294930687/10000000000 : ℝ)^4517 ≤ (8788965859943/20000000000000 : ℝ)^3493 := by
    have hnat : (5294930687 : ℕ)^4517*20000000000000^3493 ≤ 8788965859943^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294930687 10000000000 8788965859943 20000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432772043/10000000000 : ℝ)^4517 ≤ (45429816037963/100000000000000 : ℝ)^3493 := by
    have hnat : (5432772043 : ℕ)^4517*100000000000000^3493 ≤ 45429816037963^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432772043 10000000000 45429816037963 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44158117/250000000 : ℝ)^4517 ≤ (5312677321139/50000000000000 : ℝ)^3493 := by
    have hnat : (44158117 : ℕ)^4517*50000000000000^3493 ≤ 5312677321139^3493*250000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44158117 250000000 5312677321139 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294930687/10000000000 : ℝ), (5432772043/10000000000 : ℝ), (-44158117/250000000 : ℝ)] ![(8788965859943/20000000000000 : ℝ), (45429816037963/100000000000000 : ℝ), (5312677321139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294930687/10000000000 : ℝ)|^4517 ≤ (8788965859943/20000000000000 : ℝ)^3493
        have hw : |(5294930687/10000000000 : ℝ)|=(5294930687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432772043/10000000000 : ℝ)|^4517 ≤ (45429816037963/100000000000000 : ℝ)^3493
        have hw : |(5432772043/10000000000 : ℝ)|=(5432772043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44158117/250000000 : ℝ)|^4517 ≤ (5312677321139/50000000000000 : ℝ)^3493
        have hw : |(-44158117/250000000 : ℝ)|=(44158117/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s4_7 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2135366383/5000000000 : ℝ)*x 0 + (2259753813/5000000000 : ℝ)*x 1 + (806766751/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135366383/5000000000 : ℝ)^4517 ≤ (33279846409173/100000000000000 : ℝ)^3493 := by
    have hnat : (2135366383 : ℕ)^4517*100000000000000^3493 ≤ 33279846409173^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135366383 5000000000 33279846409173 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259753813/5000000000 : ℝ)^4517 ≤ (35807864002263/100000000000000 : ℝ)^3493 := by
    have hnat : (2259753813 : ℕ)^4517*100000000000000^3493 ≤ 35807864002263^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259753813 5000000000 35807864002263 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806766751/2000000000 : ℝ)^4517 ≤ (30912289566541/100000000000000 : ℝ)^3493 := by
    have hnat : (806766751 : ℕ)^4517*100000000000000^3493 ≤ 30912289566541^3493*2000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806766751 2000000000 30912289566541 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2135366383/5000000000 : ℝ), (2259753813/5000000000 : ℝ), (806766751/2000000000 : ℝ)] ![(33279846409173/100000000000000 : ℝ), (35807864002263/100000000000000 : ℝ), (30912289566541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2135366383/5000000000 : ℝ)|^4517 ≤ (33279846409173/100000000000000 : ℝ)^3493
        have hw : |(2135366383/5000000000 : ℝ)|=(2135366383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2259753813/5000000000 : ℝ)|^4517 ≤ (35807864002263/100000000000000 : ℝ)^3493
        have hw : |(2259753813/5000000000 : ℝ)|=(2259753813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(806766751/2000000000 : ℝ)|^4517 ≤ (30912289566541/100000000000000 : ℝ)^3493
        have hw : |(806766751/2000000000 : ℝ)|=(806766751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1510_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15551/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2711/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (109/1000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15551/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2711/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15551/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2711/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15551/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2711/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15551/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2711/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15551/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2711/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15551/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2711/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2711/25000 : ℝ) ^ (4515/1024 : ℝ) ≤ (5571564728836743/100000000000000000000 : ℝ) := by
    have hpowers : (2711/25000 : ℝ)^4515 ≤ (5571564728836743/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2711 : ℕ)^4515*100000000000000000000^1024 ≤ 5571564728836743^1024*25000^4515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2711 25000 5571564728836743 100000000000000000000 4515 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2711/25000 : ℝ)) (X := (5571564728836743/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15551/100000 : ℝ) ^ (4515/1024 : ℝ) ≤ (218477740154207/800000000000000000 : ℝ) := by
    have hpowers : (15551/100000 : ℝ)^4515 ≤ (218477740154207/800000000000000000 : ℝ)^1024 := by
      have hnat : (15551 : ℕ)^4515*800000000000000000^1024 ≤ 218477740154207^1024*100000^4515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15551 100000 218477740154207 800000000000000000 4515 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15551/100000 : ℝ)) (X := (218477740154207/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005571564728836743/50000000000000000000 : ℝ) ≤ (10000252714795951/10000000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (50005571564728836743/50000000000000000000 : ℝ)^1024 ≤ (10000252714795951/10000000000000000 : ℝ)^4515 := by
      have hnat : (50005571564728836743 : ℕ)^1024*10000000000000000^4515 ≤ 10000252714795951^4515*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005571564728836743 50000000000000000000 10000252714795951 10000000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000252714795951/10000000000000000 : ℝ)) (X := (50005571564728836743/50000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50016440641124056309/50000000000000000000 : ℝ) ≤ (10000745651244701/10000000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (50016440641124056309/50000000000000000000 : ℝ)^1024 ≤ (10000745651244701/10000000000000000 : ℝ)^4515 := by
      have hnat : (50016440641124056309 : ℕ)^1024*10000000000000000^4515 ≤ 10000745651244701^4515*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016440641124056309 50000000000000000000 10000745651244701 10000000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000745651244701/10000000000000000 : ℝ)) (X := (50016440641124056309/50000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (400218477740154207/400000000000000000 : ℝ) ≤ (10001238587693451/10000000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (400218477740154207/400000000000000000 : ℝ)^1024 ≤ (10001238587693451/10000000000000000 : ℝ)^4515 := by
      have hnat : (400218477740154207 : ℕ)^1024*10000000000000000^4515 ≤ 10001238587693451^4515*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400218477740154207 400000000000000000 10001238587693451 10000000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001238587693451/10000000000000000 : ℝ)) (X := (400218477740154207/400000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5571564728836743/100000000000000000000 : ℝ) ≤ ((47060498722844051357/47070000000000000000 : ℝ)+2*(394349159/376560000000 : ℝ)*(2711/25000 : ℝ))^(4515/1024 : ℝ) := by
    rw [show (47060498722844051357/47070000000000000000 : ℝ)+2*(394349159/376560000000 : ℝ)*(2711/25000 : ℝ)=(10000252714795951/10000000000000000 : ℝ) by norm_num, show 1+2*(5571564728836743/100000000000000000000 : ℝ)=(50005571564728836743/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(218477740154207/800000000000000000 : ℝ)+(5571564728836743/100000000000000000000 : ℝ) ≤ ((47060498722844051357/47070000000000000000 : ℝ)+(394349159/376560000000 : ℝ)*((15551/100000 : ℝ)+(2711/25000 : ℝ)))^(4515/1024 : ℝ) := by
    rw [show (47060498722844051357/47070000000000000000 : ℝ)+(394349159/376560000000 : ℝ)*((15551/100000 : ℝ)+(2711/25000 : ℝ))=(10000745651244701/10000000000000000 : ℝ) by norm_num, show 1+(218477740154207/800000000000000000 : ℝ)+(5571564728836743/100000000000000000000 : ℝ)=(50016440641124056309/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(218477740154207/800000000000000000 : ℝ) ≤ ((47060498722844051357/47070000000000000000 : ℝ)+2*(394349159/376560000000 : ℝ)*(15551/100000 : ℝ))^(4515/1024 : ℝ) := by
    rw [show (47060498722844051357/47070000000000000000 : ℝ)+2*(394349159/376560000000 : ℝ)*(15551/100000 : ℝ)=(10001238587693451/10000000000000000 : ℝ) by norm_num, show 1+2*(218477740154207/800000000000000000 : ℝ)=(400218477740154207/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (47060498722844051357/47070000000000000000 : ℝ)*(X 1 0+X 2 0)+(394349159/376560000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (2711/25000 : ℝ)) (hi := (15551/100000 : ℝ)) (c := (47060498722844051357/47070000000000000000 : ℝ)) (alpha := (394349159/376560000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (47060498722844051357/47070000000000000000 : ℝ)*(X 0 1+X 2 1)+(394349159/376560000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (2711/25000 : ℝ)) (hi := (15551/100000 : ℝ)) (c := (47060498722844051357/47070000000000000000 : ℝ)) (alpha := (394349159/376560000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (47060498722844051357/47070000000000000000 : ℝ)*(X 0 2+X 1 2)+(394349159/376560000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (2711/25000 : ℝ)) (hi := (15551/100000 : ℝ)) (c := (47060498722844051357/47070000000000000000 : ℝ)) (alpha := (394349159/376560000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-935457193/5000000000 : ℝ)*X 0 0+(217355983/400000000 : ℝ)*X 0 1+(5217169729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351808273/10000000000 : ℝ)*X 1 0+(-1981927133/10000000000 : ℝ)*X 1 1+(5217169191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070361551/2000000000 : ℝ)*X 2 0+(2608584887/5000000000 : ℝ)*X 2 1+(-1981927053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4270665947/10000000000 : ℝ)*X 0 0+(4031281047/10000000000 : ℝ)*X 0 1+(2261020971/5000000000 : ℝ)*X 0 2+(4270665947/10000000000 : ℝ)*X 1 0+(4031281047/10000000000 : ℝ)*X 1 1+(2261020971/5000000000 : ℝ)*X 1 2+(4270665947/10000000000 : ℝ)*X 2 0+(4031281047/10000000000 : ℝ)*X 2 1+(2261020971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1870944169/10000000000 : ℝ)*X 0 0+(130457217/250000000 : ℝ)*X 0 1+(135819301/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058986143/2000000000 : ℝ)*X 1 0+(-883162337/5000000000 : ℝ)*X 1 1+(5432772021/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294930687/10000000000 : ℝ)*X 2 0+(5432772043/10000000000 : ℝ)*X 2 1+(-44158117/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2135366383/5000000000 : ℝ)*X 0 0+(2259753813/5000000000 : ℝ)*X 0 1+(806766751/2000000000 : ℝ)*X 0 2+(2135366383/5000000000 : ℝ)*X 1 0+(2259753813/5000000000 : ℝ)*X 1 1+(806766751/2000000000 : ℝ)*X 1 2+(2135366383/5000000000 : ℝ)*X 2 0+(2259753813/5000000000 : ℝ)*X 2 1+(806766751/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5707600095569069254931/523000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40929479/2000000000000 : ℝ)*(base19) + (1309203303/100000000000000 : ℝ)*(base23) + (7927399/5000000000000 : ℝ)*(lower2) + (104182519/50000000000000 : ℝ)*(upper3) + (2984821/100000000000000 : ℝ)*(lower4) + (831471226070219/25000000000000 : ℝ)*(major0) + (831471226070219/25000000000000 : ℝ)*(major1) + (831471226070219/25000000000000 : ℝ)*(major2) + (4614068900460707/100000000000000 : ℝ)*(sp0) + (576761384258907/12500000000000 : ℝ)*(sp1) + (4614091811341903/100000000000000 : ℝ)*(sp2) + (509415791499821/25000000000000 : ℝ)*(sp3) + (24220084499/100000000000000 : ℝ)*(sp4) + (3289561037/25000000000000 : ℝ)*(sp7) + (254709540530429/12500000000000 : ℝ)*(f.failure) + (2307046560272603/50000000000000 : ℝ)*(f.sum) + (21586947654319/4707000000000000000000000000 : ℝ)*base65 + (3649180931549170939/392250000000000000000000000000000 : ℝ)*base68 + (2358450059676670939/392250000000000000000000000000000 : ℝ)*base70 + (1009445871564079061/392250000000000000000000000000000 : ℝ)*base71 + (1198462571941/1176750000000000000000000000 : ℝ)*base73 + (2182656615504079061/392250000000000000000000000000000 : ℝ)*base75 + (1095914686560829061/392250000000000000000000000000000 : ℝ)*base77 + (1242558152002420939/392250000000000000000000000000000 : ℝ)*base80 + (21190546114837/4707000000000000000000000000 : ℝ)*base81 + (86121/125000000000000000000 : ℝ)*base89 + (86121/125000000000000000000 : ℝ)*base91 + (86121/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (643923966260525130833324687/98062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1307612007/100000000000000 : ℝ)*(base19) + (1295123057/100000000000000 : ℝ)*(base23) + (232239/160000000000 : ℝ)*(upper3) + (745783/10000000000000 : ℝ)*(lower4) + (3055449/2000000000000 : ℝ)*(upper5) + (840170150266691/25000000000000 : ℝ)*(major0) + (840170150266691/25000000000000 : ℝ)*(major1) + (840170150266691/25000000000000 : ℝ)*(major2) + (20556703359/100000000000000 : ℝ)*(sp1) + (10189122987/50000000000000 : ℝ)*(sp2) + (4662366312292169/100000000000000 : ℝ)*(sp4) + (4662344447976803/100000000000000 : ℝ)*(sp5) + (4662344638923139/100000000000000 : ℝ)*(sp6) + (514748667739797/25000000000000 : ℝ)*(sp7) + (514748667739797/25000000000000 : ℝ)*(f.failure) + (4662366312292169/100000000000000 : ℝ)*(f.sum) + (21590022029/4707000000000000000000000000 : ℝ)*base66 + (2299086911629516771/392250000000000000000000000000000 : ℝ)*base68 + (1423627967533483229/392250000000000000000000000000000 : ℝ)*base69 + (2601916680151516771/392250000000000000000000000000000 : ℝ)*base72 + (19171441254667/4707000000000000000000000000 : ℝ)*base73 + (4241358979558516771/392250000000000000000000000000000 : ℝ)*base76 + (4234030376291266771/392250000000000000000000000000000 : ℝ)*base78 + (2899090528848766771/392250000000000000000000000000000 : ℝ)*base80 + (7147035508907/2353500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1904353/250000000000000000000 : ℝ)*base89 + (1904353/250000000000000000000 : ℝ)*base91 + (1904353/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1510_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15551/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2711/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (109/1000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1510_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1510_s5_0 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-187096991/1000000000 : ℝ)*x 0 + (679192247/1250000000 : ℝ)*x 1 + (1304373639/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (187096991/1000000000 : ℝ)^4517 ≤ (2289272781831/20000000000000 : ℝ)^3493 := by
    have hnat : (187096991 : ℕ)^4517*20000000000000^3493 ≤ 2289272781831^3493*1000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187096991 1000000000 2289272781831 20000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679192247/1250000000 : ℝ)^4517 ≤ (45438098715551/100000000000000 : ℝ)^3493 := by
    have hnat : (679192247 : ℕ)^4517*100000000000000^3493 ≤ 45438098715551^3493*1250000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679192247 1250000000 45438098715551 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304373639/2500000000 : ℝ)^4517 ≤ (21557768682471/50000000000000 : ℝ)^3493 := by
    have hnat : (1304373639 : ℕ)^4517*50000000000000^3493 ≤ 21557768682471^3493*2500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304373639 2500000000 21557768682471 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-187096991/1000000000 : ℝ), (679192247/1250000000 : ℝ), (1304373639/2500000000 : ℝ)] ![(2289272781831/20000000000000 : ℝ), (45438098715551/100000000000000 : ℝ), (21557768682471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-187096991/1000000000 : ℝ)|^4517 ≤ (2289272781831/20000000000000 : ℝ)^3493
        have hw : |(-187096991/1000000000 : ℝ)|=(187096991/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679192247/1250000000 : ℝ)|^4517 ≤ (45438098715551/100000000000000 : ℝ)^3493
        have hw : |(679192247/1250000000 : ℝ)|=(679192247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304373639/2500000000 : ℝ)|^4517 ≤ (21557768682471/50000000000000 : ℝ)^3493
        have hw : |(1304373639/2500000000 : ℝ)|=(1304373639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s5_1 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334482053/625000000 : ℝ)*x 0 + (-247702879/1250000000 : ℝ)*x 1 + (52174943/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334482053/625000000 : ℝ)^4517 ≤ (22277598355921/50000000000000 : ℝ)^3493 := by
    have hnat : (334482053 : ℕ)^4517*50000000000000^3493 ≤ 22277598355921^3493*625000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334482053 625000000 22277598355921 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (247702879/1250000000 : ℝ)^4517 ≤ (6164634323333/50000000000000 : ℝ)^3493 := by
    have hnat : (247702879 : ℕ)^4517*50000000000000^3493 ≤ 6164634323333^3493*1250000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247702879 1250000000 6164634323333 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52174943/100000000 : ℝ)^4517 ≤ (21557767314637/50000000000000 : ℝ)^3493 := by
    have hnat : (52174943 : ℕ)^4517*50000000000000^3493 ≤ 21557767314637^3493*100000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52174943 100000000 21557767314637 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334482053/625000000 : ℝ), (-247702879/1250000000 : ℝ), (52174943/100000000 : ℝ)] ![(22277598355921/50000000000000 : ℝ), (6164634323333/50000000000000 : ℝ), (21557767314637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334482053/625000000 : ℝ)|^4517 ≤ (22277598355921/50000000000000 : ℝ)^3493
        have hw : |(334482053/625000000 : ℝ)|=(334482053/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-247702879/1250000000 : ℝ)|^4517 ≤ (6164634323333/50000000000000 : ℝ)^3493
        have hw : |(-247702879/1250000000 : ℝ)|=(247702879/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52174943/100000000 : ℝ)|^4517 ≤ (21557767314637/50000000000000 : ℝ)^3493
        have hw : |(52174943/100000000 : ℝ)|=(52174943/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s5_2 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351713083/10000000000 : ℝ)*x 0 + (5217494149/10000000000 : ℝ)*x 1 + (-990811459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351713083/10000000000 : ℝ)^4517 ≤ (11138799810467/25000000000000 : ℝ)^3493 := by
    have hnat : (5351713083 : ℕ)^4517*25000000000000^3493 ≤ 11138799810467^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351713083 10000000000 11138799810467 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217494149/10000000000 : ℝ)^4517 ≤ (21557766507829/50000000000000 : ℝ)^3493 := by
    have hnat : (5217494149 : ℕ)^4517*50000000000000^3493 ≤ 21557766507829^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217494149 10000000000 21557766507829 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (990811459/5000000000 : ℝ)^4517 ≤ (1541158466181/12500000000000 : ℝ)^3493 := by
    have hnat : (990811459 : ℕ)^4517*12500000000000^3493 ≤ 1541158466181^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990811459 5000000000 1541158466181 12500000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351713083/10000000000 : ℝ), (5217494149/10000000000 : ℝ), (-990811459/5000000000 : ℝ)] ![(11138799810467/25000000000000 : ℝ), (21557766507829/50000000000000 : ℝ), (1541158466181/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351713083/10000000000 : ℝ)|^4517 ≤ (11138799810467/25000000000000 : ℝ)^3493
        have hw : |(5351713083/10000000000 : ℝ)|=(5351713083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217494149/10000000000 : ℝ)|^4517 ≤ (21557766507829/50000000000000 : ℝ)^3493
        have hw : |(5217494149/10000000000 : ℝ)|=(5217494149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-990811459/5000000000 : ℝ)|^4517 ≤ (1541158466181/12500000000000 : ℝ)^3493
        have hw : |(-990811459/5000000000 : ℝ)|=(990811459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s5_3 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (17082803/40000000 : ℝ)*x 0 + (2016027131/5000000000 : ℝ)*x 1 + (1130315017/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17082803/40000000 : ℝ)^4517 ≤ (33279523784917/100000000000000 : ℝ)^3493 := by
    have hnat : (17082803 : ℕ)^4517*100000000000000^3493 ≤ 33279523784917^3493*40000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17082803 40000000 33279523784917 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2016027131/5000000000 : ℝ)^4517 ≤ (6178931259127/20000000000000 : ℝ)^3493 := by
    have hnat : (2016027131 : ℕ)^4517*20000000000000^3493 ≤ 6178931259127^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016027131 5000000000 6178931259127 20000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130315017/2500000000 : ℝ)^4517 ≤ (35825819900301/100000000000000 : ℝ)^3493 := by
    have hnat : (1130315017 : ℕ)^4517*100000000000000^3493 ≤ 35825819900301^3493*2500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130315017 2500000000 35825819900301 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17082803/40000000 : ℝ), (2016027131/5000000000 : ℝ), (1130315017/2500000000 : ℝ)] ![(33279523784917/100000000000000 : ℝ), (6178931259127/20000000000000 : ℝ), (35825819900301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17082803/40000000 : ℝ)|^4517 ≤ (33279523784917/100000000000000 : ℝ)^3493
        have hw : |(17082803/40000000 : ℝ)|=(17082803/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2016027131/5000000000 : ℝ)|^4517 ≤ (6178931259127/20000000000000 : ℝ)^3493
        have hw : |(2016027131/5000000000 : ℝ)|=(2016027131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130315017/2500000000 : ℝ)|^4517 ≤ (35825819900301/100000000000000 : ℝ)^3493
        have hw : |(1130315017/2500000000 : ℝ)|=(1130315017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s5_4 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-467749829/2500000000 : ℝ)*x 0 + (5218606449/10000000000 : ℝ)*x 1 + (339526103/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (467749829/2500000000 : ℝ)^4517 ≤ (2289319310347/20000000000000 : ℝ)^3493 := by
    have hnat : (467749829 : ℕ)^4517*20000000000000^3493 ≤ 2289319310347^3493*2500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467749829 2500000000 2289319310347 20000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218606449/10000000000 : ℝ)^4517 ≤ (5390927455901/12500000000000 : ℝ)^3493 := by
    have hnat : (5218606449 : ℕ)^4517*12500000000000^3493 ≤ 5390927455901^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218606449 10000000000 5390927455901 12500000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339526103/625000000 : ℝ)^4517 ≤ (2271299189133/5000000000000 : ℝ)^3493 := by
    have hnat : (339526103 : ℕ)^4517*5000000000000^3493 ≤ 2271299189133^3493*625000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339526103 625000000 2271299189133 5000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-467749829/2500000000 : ℝ), (5218606449/10000000000 : ℝ), (339526103/625000000 : ℝ)] ![(2289319310347/20000000000000 : ℝ), (5390927455901/12500000000000 : ℝ), (2271299189133/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-467749829/2500000000 : ℝ)|^4517 ≤ (2289319310347/20000000000000 : ℝ)^3493
        have hw : |(-467749829/2500000000 : ℝ)|=(467749829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218606449/10000000000 : ℝ)|^4517 ≤ (5390927455901/12500000000000 : ℝ)^3493
        have hw : |(5218606449/10000000000 : ℝ)|=(5218606449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339526103/625000000 : ℝ)|^4517 ≤ (2271299189133/5000000000000 : ℝ)^3493
        have hw : |(339526103/625000000 : ℝ)|=(339526103/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s5_5 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647508029/5000000000 : ℝ)*x 0 + (-883349759/5000000000 : ℝ)*x 1 + (5432417653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647508029/5000000000 : ℝ)^4517 ≤ (43945745542151/100000000000000 : ℝ)^3493 := by
    have hnat : (2647508029 : ℕ)^4517*100000000000000^3493 ≤ 43945745542151^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647508029 5000000000 43945745542151 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (883349759/5000000000 : ℝ)^4517 ≤ (10628270602011/100000000000000 : ℝ)^3493 := by
    have hnat : (883349759 : ℕ)^4517*100000000000000^3493 ≤ 10628270602011^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883349759 5000000000 10628270602011 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432417653/10000000000 : ℝ)^4517 ≤ (45425983836727/100000000000000 : ℝ)^3493 := by
    have hnat : (5432417653 : ℕ)^4517*100000000000000^3493 ≤ 45425983836727^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432417653 10000000000 45425983836727 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647508029/5000000000 : ℝ), (-883349759/5000000000 : ℝ), (5432417653/10000000000 : ℝ)] ![(43945745542151/100000000000000 : ℝ), (10628270602011/100000000000000 : ℝ), (45425983836727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647508029/5000000000 : ℝ)|^4517 ≤ (43945745542151/100000000000000 : ℝ)^3493
        have hw : |(2647508029/5000000000 : ℝ)|=(2647508029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-883349759/5000000000 : ℝ)|^4517 ≤ (10628270602011/100000000000000 : ℝ)^3493
        have hw : |(-883349759/5000000000 : ℝ)|=(883349759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432417653/10000000000 : ℝ)|^4517 ≤ (45425983836727/100000000000000 : ℝ)^3493
        have hw : |(5432417653/10000000000 : ℝ)|=(5432417653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s5_6 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295016073/10000000000 : ℝ)*x 0 + (2716208823/5000000000 : ℝ)*x 1 + (-1766699507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295016073/10000000000 : ℝ)^4517 ≤ (21972872851569/50000000000000 : ℝ)^3493 := by
    have hnat : (5295016073 : ℕ)^4517*50000000000000^3493 ≤ 21972872851569^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295016073 10000000000 21972872851569 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716208823/5000000000 : ℝ)^4517 ≤ (22712991880517/50000000000000 : ℝ)^3493 := by
    have hnat : (2716208823 : ℕ)^4517*50000000000000^3493 ≤ 22712991880517^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716208823 5000000000 22712991880517 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1766699507/10000000000 : ℝ)^4517 ≤ (10628270516437/100000000000000 : ℝ)^3493 := by
    have hnat : (1766699507 : ℕ)^4517*100000000000000^3493 ≤ 10628270516437^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1766699507 10000000000 10628270516437 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295016073/10000000000 : ℝ), (2716208823/5000000000 : ℝ), (-1766699507/10000000000 : ℝ)] ![(21972872851569/50000000000000 : ℝ), (22712991880517/50000000000000 : ℝ), (10628270516437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295016073/10000000000 : ℝ)|^4517 ≤ (21972872851569/50000000000000 : ℝ)^3493
        have hw : |(5295016073/10000000000 : ℝ)|=(5295016073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716208823/5000000000 : ℝ)|^4517 ≤ (22712991880517/50000000000000 : ℝ)^3493
        have hw : |(2716208823/5000000000 : ℝ)|=(2716208823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1766699507/10000000000 : ℝ)|^4517 ≤ (10628270516437/100000000000000 : ℝ)^3493
        have hw : |(-1766699507/10000000000 : ℝ)|=(1766699507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s5_7 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2135383111/5000000000 : ℝ)*x 0 + (2259371243/5000000000 : ℝ)*x 1 + (1008647691/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135383111/5000000000 : ℝ)^4517 ≤ (16640091772511/50000000000000 : ℝ)^3493 := by
    have hnat : (2135383111 : ℕ)^4517*50000000000000^3493 ≤ 16640091772511^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135383111 5000000000 16640091772511 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259371243/5000000000 : ℝ)^4517 ≤ (35800024853147/100000000000000 : ℝ)^3493 := by
    have hnat : (2259371243 : ℕ)^4517*100000000000000^3493 ≤ 35800024853147^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259371243 5000000000 35800024853147 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1008647691/2500000000 : ℝ)^4517 ≤ (7729947894273/25000000000000 : ℝ)^3493 := by
    have hnat : (1008647691 : ℕ)^4517*25000000000000^3493 ≤ 7729947894273^3493*2500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008647691 2500000000 7729947894273 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2135383111/5000000000 : ℝ), (2259371243/5000000000 : ℝ), (1008647691/2500000000 : ℝ)] ![(16640091772511/50000000000000 : ℝ), (35800024853147/100000000000000 : ℝ), (7729947894273/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2135383111/5000000000 : ℝ)|^4517 ≤ (16640091772511/50000000000000 : ℝ)^3493
        have hw : |(2135383111/5000000000 : ℝ)|=(2135383111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2259371243/5000000000 : ℝ)|^4517 ≤ (35800024853147/100000000000000 : ℝ)^3493
        have hw : |(2259371243/5000000000 : ℝ)|=(2259371243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1008647691/2500000000 : ℝ)|^4517 ≤ (7729947894273/25000000000000 : ℝ)^3493
        have hw : |(1008647691/2500000000 : ℝ)|=(1008647691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1510_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (109/1000 : ℝ)*pair X i i ≤ pair X i h) :
    (10907/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7741/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (109/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (109/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (109/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (109/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (109/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (109/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (109/1000 : ℝ) ^ (4515/1024 : ℝ) ≤ (5699548675576347/100000000000000000000 : ℝ) := by
    have hpowers : (109/1000 : ℝ)^4515 ≤ (5699548675576347/100000000000000000000 : ℝ)^1024 := by
      have hnat : (109 : ℕ)^4515*100000000000000000000^1024 ≤ 5699548675576347^1024*1000^4515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109 1000 5699548675576347 100000000000000000000 4515 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (109/1000 : ℝ)) (X := (5699548675576347/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4515/1024 : ℝ) ≤ (13420267348265709/50000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4515 ≤ (13420267348265709/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4515*50000000000000000000^1024 ≤ 13420267348265709^1024*10000^4515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 13420267348265709 50000000000000000000 4515 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (13420267348265709/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005699548675576347/50000000000000000000 : ℝ) ≤ (5000129259815281/5000000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (50005699548675576347/50000000000000000000 : ℝ)^1024 ≤ (5000129259815281/5000000000000000 : ℝ)^4515 := by
      have hnat : (50005699548675576347 : ℕ)^1024*5000000000000000^4515 ≤ 5000129259815281^4515*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005699548675576347 50000000000000000000 5000129259815281 5000000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000129259815281/5000000000000000 : ℝ)) (X := (50005699548675576347/50000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20006508016674421553/20000000000000000000 : ℝ) ≤ (2500184478706481/2500000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (20006508016674421553/20000000000000000000 : ℝ)^1024 ≤ (2500184478706481/2500000000000000 : ℝ)^4515 := by
      have hnat : (20006508016674421553 : ℕ)^1024*2500000000000000^4515 ≤ 2500184478706481^4515*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20006508016674421553 20000000000000000000 2500184478706481 2500000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500184478706481/2500000000000000 : ℝ)) (X := (20006508016674421553/20000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013420267348265709/25000000000000000000 : ℝ) ≤ (5000608655010643/5000000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (25013420267348265709/25000000000000000000 : ℝ)^1024 ≤ (5000608655010643/5000000000000000 : ℝ)^4515 := by
      have hnat : (25013420267348265709 : ℕ)^1024*5000000000000000^4515 ≤ 5000608655010643^4515*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013420267348265709 25000000000000000000 5000608655010643 5000000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000608655010643/5000000000000000 : ℝ)) (X := (25013420267348265709/25000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5699548675576347/100000000000000000000 : ℝ) ≤ ((84982844055269237/85000000000000000 : ℝ)+2*(8877688803/8500000000000 : ℝ)*(109/1000 : ℝ))^(4515/1024 : ℝ) := by
    rw [show (84982844055269237/85000000000000000 : ℝ)+2*(8877688803/8500000000000 : ℝ)*(109/1000 : ℝ)=(5000129259815281/5000000000000000 : ℝ) by norm_num, show 1+2*(5699548675576347/100000000000000000000 : ℝ)=(50005699548675576347/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13420267348265709/50000000000000000000 : ℝ)+(5699548675576347/100000000000000000000 : ℝ) ≤ ((84982844055269237/85000000000000000 : ℝ)+(8877688803/8500000000000 : ℝ)*((1549/10000 : ℝ)+(109/1000 : ℝ)))^(4515/1024 : ℝ) := by
    rw [show (84982844055269237/85000000000000000 : ℝ)+(8877688803/8500000000000 : ℝ)*((1549/10000 : ℝ)+(109/1000 : ℝ))=(2500184478706481/2500000000000000 : ℝ) by norm_num, show 1+(13420267348265709/50000000000000000000 : ℝ)+(5699548675576347/100000000000000000000 : ℝ)=(20006508016674421553/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13420267348265709/50000000000000000000 : ℝ) ≤ ((84982844055269237/85000000000000000 : ℝ)+2*(8877688803/8500000000000 : ℝ)*(1549/10000 : ℝ))^(4515/1024 : ℝ) := by
    rw [show (84982844055269237/85000000000000000 : ℝ)+2*(8877688803/8500000000000 : ℝ)*(1549/10000 : ℝ)=(5000608655010643/5000000000000000 : ℝ) by norm_num, show 1+2*(13420267348265709/50000000000000000000 : ℝ)=(25013420267348265709/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (84982844055269237/85000000000000000 : ℝ)*(X 1 0+X 2 0)+(8877688803/8500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (109/1000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (84982844055269237/85000000000000000 : ℝ)) (alpha := (8877688803/8500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (84982844055269237/85000000000000000 : ℝ)*(X 0 1+X 2 1)+(8877688803/8500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (109/1000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (84982844055269237/85000000000000000 : ℝ)) (alpha := (8877688803/8500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (84982844055269237/85000000000000000 : ℝ)*(X 0 2+X 1 2)+(8877688803/8500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (109/1000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (84982844055269237/85000000000000000 : ℝ)) (alpha := (8877688803/8500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-187096991/1000000000 : ℝ)*X 0 0+(679192247/1250000000 : ℝ)*X 0 1+(1304373639/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334482053/625000000 : ℝ)*X 1 0+(-247702879/1250000000 : ℝ)*X 1 1+(52174943/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351713083/10000000000 : ℝ)*X 2 0+(5217494149/10000000000 : ℝ)*X 2 1+(-990811459/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((17082803/40000000 : ℝ)*X 0 0+(2016027131/5000000000 : ℝ)*X 0 1+(1130315017/2500000000 : ℝ)*X 0 2+(17082803/40000000 : ℝ)*X 1 0+(2016027131/5000000000 : ℝ)*X 1 1+(1130315017/2500000000 : ℝ)*X 1 2+(17082803/40000000 : ℝ)*X 2 0+(2016027131/5000000000 : ℝ)*X 2 1+(1130315017/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-467749829/2500000000 : ℝ)*X 0 0+(5218606449/10000000000 : ℝ)*X 0 1+(339526103/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647508029/5000000000 : ℝ)*X 1 0+(-883349759/5000000000 : ℝ)*X 1 1+(5432417653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295016073/10000000000 : ℝ)*X 2 0+(2716208823/5000000000 : ℝ)*X 2 1+(-1766699507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2135383111/5000000000 : ℝ)*X 0 0+(2259371243/5000000000 : ℝ)*X 0 1+(1008647691/2500000000 : ℝ)*X 0 2+(2135383111/5000000000 : ℝ)*X 1 0+(2259371243/5000000000 : ℝ)*X 1 1+(1008647691/2500000000 : ℝ)*X 1 2+(2135383111/5000000000 : ℝ)*X 2 0+(2259371243/5000000000 : ℝ)*X 2 1+(1008647691/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22309484618086330650605757/2125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1773219633/100000000000000 : ℝ)*(base19) + (702944047/50000000000000 : ℝ)*(base23) + (305360579/100000000000000 : ℝ)*(lower2) + (167431041/50000000000000 : ℝ)*(upper3) + (59971771/100000000000000 : ℝ)*(upper5) + (1668220200350329/50000000000000 : ℝ)*(major0) + (1668220200350329/50000000000000 : ℝ)*(major1) + (1668220200350329/50000000000000 : ℝ)*(major2) + (462871870680199/10000000000000 : ℝ)*(sp0) + (36161994512647/781250000000 : ℝ)*(sp1) + (925747132990071/20000000000000 : ℝ)*(sp2) + (2044133765687563/100000000000000 : ℝ)*(sp3) + (18364036459/100000000000000 : ℝ)*(sp4) + (1922984519/20000000000000 : ℝ)*(sp7) + (1022071690305079/50000000000000 : ℝ)*(f.failure) + (4628737070838449/100000000000000 : ℝ)*(f.sum) + (750178394537/212500000000000000000000000 : ℝ)*base65 + (1523817017726531/250000000000000000000000000000 : ℝ)*base68 + (4863999699976531/250000000000000000000000000000 : ℝ)*base70 + (667265842976531/250000000000000000000000000000 : ℝ)*base72 + (578888696337/212500000000000000000000000 : ℝ)*base73 + (3531688181976531/250000000000000000000000000000 : ℝ)*base76 + (2668577467226531/250000000000000000000000000000 : ℝ)*base78 + (5224336158726531/250000000000000000000000000000 : ℝ)*base80 + (167523541447/53125000000000000000000000 : ℝ)*base82 + (3878971/500000000000000000000 : ℝ)*base89 + (3878971/500000000000000000000 : ℝ)*base91 + (3878971/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (860404554349847262620061/425000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (379879151/100000000000000 : ℝ)*(base19) + (442781479/100000000000000 : ℝ)*(base23) + (132659867/100000000000000 : ℝ)*(lower1) + (43191579/100000000000000 : ℝ)*(upper3) + (774321/3125000000000 : ℝ)*(lower4) + (75782593/100000000000000 : ℝ)*(upper5) + (674248298768851/20000000000000 : ℝ)*(major0) + (674248298768851/20000000000000 : ℝ)*(major1) + (674248298768851/20000000000000 : ℝ)*(major2) + (266872003/100000000000000 : ℝ)*(sp2) + (4677017886682979/100000000000000 : ℝ)*(sp4) + (1169254376700957/25000000000000 : ℝ)*(sp5) + (4677017177029497/100000000000000 : ℝ)*(sp6) + (2065465033522807/100000000000000 : ℝ)*(sp7) + (2065465033522807/100000000000000 : ℝ)*(f.failure) + (4677017886682979/100000000000000 : ℝ)*(f.sum) + (207535338203/85000000000000000000000000 : ℝ)*base65 + (2657085378025489/100000000000000000000000000000 : ℝ)*base68 + (150241194725489/100000000000000000000000000000 : ℝ)*base70 + (1512113918525489/100000000000000000000000000000 : ℝ)*base72 + (218173604977/85000000000000000000000000 : ℝ)*base74 + (6496322576074511/100000000000000000000000000000 : ℝ)*base75 + (455688969125489/100000000000000000000000000000 : ℝ)*base78 + (69263671825489/100000000000000000000000000000 : ℝ)*base80 + (46233914461/42500000000000000000000000 : ℝ)*base82 + (3809157/1000000000000000000000 : ℝ)*base90 + (3809157/1000000000000000000000 : ℝ)*base92 + (3809157/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1510_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (109/1000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10907/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1510_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1510_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4001/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2607/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10907/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1510_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1510_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1510_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4001/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2607/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10907/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1510_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1685_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:33:05.750928+00:00
-- url     : https://prove2.me/submissions/c7f67c21-888c-41d2-a729-6b028a4a9f34

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
theorem support_rectangle_w1685_s3_0 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1507789547/10000000000 : ℝ)*x 0 + (171457249/312500000 : ℝ)*x 1 + (5134366617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1507789547/10000000000 : ℝ)^5103 ≤ (4688563579351/50000000000000 : ℝ)^4079 := by
    have hnat : (1507789547 : ℕ)^5103*50000000000000^4079 ≤ 4688563579351^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507789547 10000000000 4688563579351 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171457249/312500000 : ℝ)^5103 ≤ (11797790303577/25000000000000 : ℝ)^4079 := by
    have hnat : (171457249 : ℕ)^5103*25000000000000^4079 ≤ 11797790303577^4079*312500000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171457249 312500000 11797790303577 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5134366617/10000000000 : ℝ)^5103 ≤ (21715855806457/50000000000000 : ℝ)^4079 := by
    have hnat : (5134366617 : ℕ)^5103*50000000000000^4079 ≤ 21715855806457^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134366617 10000000000 21715855806457 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1507789547/10000000000 : ℝ), (171457249/312500000 : ℝ), (5134366617/10000000000 : ℝ)] ![(4688563579351/50000000000000 : ℝ), (11797790303577/25000000000000 : ℝ), (21715855806457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1507789547/10000000000 : ℝ)|^5103 ≤ (4688563579351/50000000000000 : ℝ)^4079
        have hw : |(-1507789547/10000000000 : ℝ)|=(1507789547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(171457249/312500000 : ℝ)|^5103 ≤ (11797790303577/25000000000000 : ℝ)^4079
        have hw : |(171457249/312500000 : ℝ)|=(171457249/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5134366617/10000000000 : ℝ)|^5103 ≤ (21715855806457/50000000000000 : ℝ)^4079
        have hw : |(5134366617/10000000000 : ℝ)|=(5134366617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s3_1 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351885453/10000000000 : ℝ)*x 0 + (-1690857789/10000000000 : ℝ)*x 1 + (5134366663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351885453/10000000000 : ℝ)^5103 ≤ (4574573789051/10000000000000 : ℝ)^4079 := by
    have hnat : (5351885453 : ℕ)^5103*10000000000000^4079 ≤ 4574573789051^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351885453 10000000000 4574573789051 10000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1690857789/10000000000 : ℝ)^5103 ≤ (5411274998479/50000000000000 : ℝ)^4079 := by
    have hnat : (1690857789 : ℕ)^5103*50000000000000^4079 ≤ 5411274998479^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1690857789 10000000000 5411274998479 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5134366663/10000000000 : ℝ)^5103 ≤ (43431712099713/100000000000000 : ℝ)^4079 := by
    have hnat : (5134366663 : ℕ)^5103*100000000000000^4079 ≤ 43431712099713^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134366663 10000000000 43431712099713 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351885453/10000000000 : ℝ), (-1690857789/10000000000 : ℝ), (5134366663/10000000000 : ℝ)] ![(4574573789051/10000000000000 : ℝ), (5411274998479/50000000000000 : ℝ), (43431712099713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351885453/10000000000 : ℝ)|^5103 ≤ (4574573789051/10000000000000 : ℝ)^4079
        have hw : |(5351885453/10000000000 : ℝ)|=(5351885453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1690857789/10000000000 : ℝ)|^5103 ≤ (5411274998479/50000000000000 : ℝ)^4079
        have hw : |(-1690857789/10000000000 : ℝ)|=(1690857789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5134366663/10000000000 : ℝ)|^5103 ≤ (43431712099713/100000000000000 : ℝ)^4079
        have hw : |(5134366663/10000000000 : ℝ)|=(5134366663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s3_2 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167246407/312500000 : ℝ)*x 0 + (8214987/16000000 : ℝ)*x 1 + (-1690858083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167246407/312500000 : ℝ)^5103 ≤ (22872866651521/50000000000000 : ℝ)^4079 := by
    have hnat : (167246407 : ℕ)^5103*50000000000000^4079 ≤ 22872866651521^4079*312500000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167246407 312500000 22872866651521 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8214987/16000000 : ℝ)^5103 ≤ (21715857171611/50000000000000 : ℝ)^4079 := by
    have hnat : (8214987 : ℕ)^5103*50000000000000^4079 ≤ 21715857171611^4079*16000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8214987 16000000 21715857171611 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1690858083/10000000000 : ℝ)^5103 ≤ (10822552351149/100000000000000 : ℝ)^4079 := by
    have hnat : (1690858083 : ℕ)^5103*100000000000000^4079 ≤ 10822552351149^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1690858083 10000000000 10822552351149 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167246407/312500000 : ℝ), (8214987/16000000 : ℝ), (-1690858083/10000000000 : ℝ)] ![(22872866651521/50000000000000 : ℝ), (21715857171611/50000000000000 : ℝ), (10822552351149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167246407/312500000 : ℝ)|^5103 ≤ (22872866651521/50000000000000 : ℝ)^4079
        have hw : |(167246407/312500000 : ℝ)|=(167246407/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8214987/16000000 : ℝ)|^5103 ≤ (21715857171611/50000000000000 : ℝ)^4079
        have hw : |(8214987/16000000 : ℝ)|=(8214987/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1690858083/10000000000 : ℝ)|^5103 ≤ (10822552351149/100000000000000 : ℝ)^4079
        have hw : |(-1690858083/10000000000 : ℝ)|=(1690858083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s3_3 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1034538447/2500000000 : ℝ)*x 0 + (1837744957/5000000000 : ℝ)*x 1 + (4638748153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034538447/2500000000 : ℝ)^5103 ≤ (4144947541791/12500000000000 : ℝ)^4079 := by
    have hnat : (1034538447 : ℕ)^5103*12500000000000^4079 ≤ 4144947541791^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034538447 2500000000 4144947541791 12500000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1837744957/5000000000 : ℝ)^5103 ≤ (2858848468949/10000000000000 : ℝ)^4079 := by
    have hnat : (1837744957 : ℕ)^5103*10000000000000^4079 ≤ 2858848468949^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1837744957 5000000000 2858848468949 10000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4638748153/10000000000 : ℝ)^5103 ≤ (38251934960667/100000000000000 : ℝ)^4079 := by
    have hnat : (4638748153 : ℕ)^5103*100000000000000^4079 ≤ 38251934960667^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4638748153 10000000000 38251934960667 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034538447/2500000000 : ℝ), (1837744957/5000000000 : ℝ), (4638748153/10000000000 : ℝ)] ![(4144947541791/12500000000000 : ℝ), (2858848468949/10000000000000 : ℝ), (38251934960667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034538447/2500000000 : ℝ)|^5103 ≤ (4144947541791/12500000000000 : ℝ)^4079
        have hw : |(1034538447/2500000000 : ℝ)|=(1034538447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1837744957/5000000000 : ℝ)|^5103 ≤ (2858848468949/10000000000000 : ℝ)^4079
        have hw : |(1837744957/5000000000 : ℝ)|=(1837744957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4638748153/10000000000 : ℝ)|^5103 ≤ (38251934960667/100000000000000 : ℝ)^4079
        have hw : |(4638748153/10000000000 : ℝ)|=(4638748153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s3_4 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1507954309/10000000000 : ℝ)*x 0 + (40142061/78125000 : ℝ)*x 1 + (5482758011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1507954309/10000000000 : ℝ)^5103 ≤ (4689204543821/50000000000000 : ℝ)^4079 := by
    have hnat : (1507954309 : ℕ)^5103*50000000000000^4079 ≤ 4689204543821^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507954309 10000000000 4689204543821 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40142061/78125000 : ℝ)^5103 ≤ (21736055572819/50000000000000 : ℝ)^4079 := by
    have hnat : (40142061 : ℕ)^5103*50000000000000^4079 ≤ 21736055572819^4079*78125000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40142061 78125000 21736055572819 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5482758011/10000000000 : ℝ)^5103 ≤ (23574739873709/50000000000000 : ℝ)^4079 := by
    have hnat : (5482758011 : ℕ)^5103*50000000000000^4079 ≤ 23574739873709^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482758011 10000000000 23574739873709 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1507954309/10000000000 : ℝ), (40142061/78125000 : ℝ), (5482758011/10000000000 : ℝ)] ![(4689204543821/50000000000000 : ℝ), (21736055572819/50000000000000 : ℝ), (23574739873709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1507954309/10000000000 : ℝ)|^5103 ≤ (4689204543821/50000000000000 : ℝ)^4079
        have hw : |(-1507954309/10000000000 : ℝ)|=(1507954309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40142061/78125000 : ℝ)|^5103 ≤ (21736055572819/50000000000000 : ℝ)^4079
        have hw : |(40142061/78125000 : ℝ)|=(40142061/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5482758011/10000000000 : ℝ)|^5103 ≤ (23574739873709/50000000000000 : ℝ)^4079
        have hw : |(5482758011/10000000000 : ℝ)|=(5482758011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s3_5 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051552211/2000000000 : ℝ)*x 0 + (-335616539/2500000000 : ℝ)*x 1 + (1370689501/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051552211/2000000000 : ℝ)^5103 ≤ (22370730046261/50000000000000 : ℝ)^4079 := by
    have hnat : (1051552211 : ℕ)^5103*50000000000000^4079 ≤ 22370730046261^4079*2000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051552211 2000000000 22370730046261 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (335616539/2500000000 : ℝ)^5103 ≤ (4054530109249/50000000000000 : ℝ)^4079 := by
    have hnat : (335616539 : ℕ)^5103*50000000000000^4079 ≤ 4054530109249^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335616539 2500000000 4054530109249 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370689501/2500000000 : ℝ)^5103 ≤ (47149479672109/100000000000000 : ℝ)^4079 := by
    have hnat : (1370689501 : ℕ)^5103*100000000000000^4079 ≤ 47149479672109^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370689501 2500000000 47149479672109 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051552211/2000000000 : ℝ), (-335616539/2500000000 : ℝ), (1370689501/2500000000 : ℝ)] ![(22370730046261/50000000000000 : ℝ), (4054530109249/50000000000000 : ℝ), (47149479672109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051552211/2000000000 : ℝ)|^5103 ≤ (22370730046261/50000000000000 : ℝ)^4079
        have hw : |(1051552211/2000000000 : ℝ)|=(1051552211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-335616539/2500000000 : ℝ)|^5103 ≤ (4054530109249/50000000000000 : ℝ)^4079
        have hw : |(-335616539/2500000000 : ℝ)|=(335616539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1370689501/2500000000 : ℝ)|^5103 ≤ (47149479672109/100000000000000 : ℝ)^4079
        have hw : |(1370689501/2500000000 : ℝ)|=(1370689501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s3_6 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314440271/2500000000 : ℝ)*x 0 + (5482757939/10000000000 : ℝ)*x 1 + (-1342466207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314440271/2500000000 : ℝ)^5103 ≤ (11185365100313/25000000000000 : ℝ)^4079 := by
    have hnat : (1314440271 : ℕ)^5103*25000000000000^4079 ≤ 11185365100313^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314440271 2500000000 11185365100313 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5482757939/10000000000 : ℝ)^5103 ≤ (4714947897281/10000000000000 : ℝ)^4079 := by
    have hnat : (5482757939 : ℕ)^5103*10000000000000^4079 ≤ 4714947897281^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482757939 10000000000 4714947897281 10000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1342466207/10000000000 : ℝ)^5103 ≤ (1013632575487/12500000000000 : ℝ)^4079 := by
    have hnat : (1342466207 : ℕ)^5103*12500000000000^4079 ≤ 1013632575487^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342466207 10000000000 1013632575487 12500000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314440271/2500000000 : ℝ), (5482757939/10000000000 : ℝ), (-1342466207/10000000000 : ℝ)] ![(11185365100313/25000000000000 : ℝ), (4714947897281/10000000000000 : ℝ), (1013632575487/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314440271/2500000000 : ℝ)|^5103 ≤ (11185365100313/25000000000000 : ℝ)^4079
        have hw : |(1314440271/2500000000 : ℝ)|=(1314440271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5482757939/10000000000 : ℝ)|^5103 ≤ (4714947897281/10000000000000 : ℝ)^4079
        have hw : |(5482757939/10000000000 : ℝ)|=(5482757939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1342466207/10000000000 : ℝ)|^5103 ≤ (1013632575487/12500000000000 : ℝ)^4079
        have hw : |(-1342466207/10000000000 : ℝ)|=(1342466207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s3_7 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2069302731/5000000000 : ℝ)*x 0 + (4628310289/10000000000 : ℝ)*x 1 + (921520893/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2069302731/5000000000 : ℝ)^5103 ≤ (16582054161353/50000000000000 : ℝ)^4079 := by
    have hnat : (2069302731 : ℕ)^5103*50000000000000^4079 ≤ 16582054161353^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069302731 5000000000 16582054161353 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4628310289/10000000000 : ℝ)^5103 ≤ (38144285127159/100000000000000 : ℝ)^4079 := by
    have hnat : (4628310289 : ℕ)^5103*100000000000000^4079 ≤ 38144285127159^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4628310289 10000000000 38144285127159 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (921520893/2500000000 : ℝ)^5103 ≤ (1147664261537/4000000000000 : ℝ)^4079 := by
    have hnat : (921520893 : ℕ)^5103*4000000000000^4079 ≤ 1147664261537^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921520893 2500000000 1147664261537 4000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2069302731/5000000000 : ℝ), (4628310289/10000000000 : ℝ), (921520893/2500000000 : ℝ)] ![(16582054161353/50000000000000 : ℝ), (38144285127159/100000000000000 : ℝ), (1147664261537/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2069302731/5000000000 : ℝ)|^5103 ≤ (16582054161353/50000000000000 : ℝ)^4079
        have hw : |(2069302731/5000000000 : ℝ)|=(2069302731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4628310289/10000000000 : ℝ)|^5103 ≤ (38144285127159/100000000000000 : ℝ)^4079
        have hw : |(4628310289/10000000000 : ℝ)|=(4628310289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(921520893/2500000000 : ℝ)|^5103 ≤ (1147664261537/4000000000000 : ℝ)^4079
        have hw : |(921520893/2500000000 : ℝ)|=(921520893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1685_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186723319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8649/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2439/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (9779/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17271/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8649/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2439/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8649/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2439/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8649/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2439/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8649/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2439/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8649/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2439/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8649/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2439/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2439/25000 : ℝ) ^ (5095/1024 : ℝ) ≤ (935480932428227/100000000000000000000 : ℝ) := by
    have hpowers : (2439/25000 : ℝ)^5095 ≤ (935480932428227/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2439 : ℕ)^5095*100000000000000000000^1024 ≤ 935480932428227^1024*25000^5095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2439 25000 935480932428227 100000000000000000000 5095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2439/25000 : ℝ)) (X := (935480932428227/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8649/50000 : ℝ) ^ (5095/1024 : ℝ) ≤ (8082637176700097/50000000000000000000 : ℝ) := by
    have hpowers : (8649/50000 : ℝ)^5095 ≤ (8082637176700097/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8649 : ℕ)^5095*50000000000000000000^1024 ≤ 8082637176700097^1024*50000^5095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8649 50000 8082637176700097 50000000000000000000 5095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8649/50000 : ℝ)) (X := (8082637176700097/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000935480932428227/50000000000000000000 : ℝ) ≤ (10000037602563873/10000000000000000 : ℝ) ^ (5095/1024 : ℝ) := by
    have hpowers : (50000935480932428227/50000000000000000000 : ℝ)^1024 ≤ (10000037602563873/10000000000000000 : ℝ)^5095 := by
      have hnat : (50000935480932428227 : ℕ)^1024*10000000000000000^5095 ≤ 10000037602563873^5095*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000935480932428227 50000000000000000000 10000037602563873 10000000000000000 1024 5095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000037602563873/10000000000000000 : ℝ)) (X := (50000935480932428227/50000000000000000000 : ℝ)) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100017100755285828421/100000000000000000000 : ℝ) ≤ (1250042958727153/1250000000000000 : ℝ) ^ (5095/1024 : ℝ) := by
    have hpowers : (100017100755285828421/100000000000000000000 : ℝ)^1024 ≤ (1250042958727153/1250000000000000 : ℝ)^5095 := by
      have hnat : (100017100755285828421 : ℕ)^1024*1250000000000000^5095 ≤ 1250042958727153^5095*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100017100755285828421 100000000000000000000 1250042958727153 1250000000000000 1024 5095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250042958727153/1250000000000000 : ℝ)) (X := (100017100755285828421/100000000000000000000 : ℝ)) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25008082637176700097/25000000000000000000 : ℝ) ≤ (400025989482823/400000000000000 : ℝ) ^ (5095/1024 : ℝ) := by
    have hpowers : (25008082637176700097/25000000000000000000 : ℝ)^1024 ≤ (400025989482823/400000000000000 : ℝ)^5095 := by
      have hnat : (25008082637176700097 : ℕ)^1024*400000000000000^5095 ≤ 400025989482823^5095*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008082637176700097 25000000000000000000 400025989482823 400000000000000 1024 5095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400025989482823/400000000000000 : ℝ)) (X := (25008082637176700097/25000000000000000000 : ℝ)) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(935480932428227/100000000000000000000 : ℝ) ≤ ((4189683978571630303/4190000000000000000 : ℝ)+2*(306067253351/754200000000000 : ℝ)*(2439/25000 : ℝ))^(5095/1024 : ℝ) := by
    rw [show (4189683978571630303/4190000000000000000 : ℝ)+2*(306067253351/754200000000000 : ℝ)*(2439/25000 : ℝ)=(10000037602563873/10000000000000000 : ℝ) by norm_num, show 1+2*(935480932428227/100000000000000000000 : ℝ)=(50000935480932428227/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8082637176700097/50000000000000000000 : ℝ)+(935480932428227/100000000000000000000 : ℝ) ≤ ((4189683978571630303/4190000000000000000 : ℝ)+(306067253351/754200000000000 : ℝ)*((8649/50000 : ℝ)+(2439/25000 : ℝ)))^(5095/1024 : ℝ) := by
    rw [show (4189683978571630303/4190000000000000000 : ℝ)+(306067253351/754200000000000 : ℝ)*((8649/50000 : ℝ)+(2439/25000 : ℝ))=(1250042958727153/1250000000000000 : ℝ) by norm_num, show 1+(8082637176700097/50000000000000000000 : ℝ)+(935480932428227/100000000000000000000 : ℝ)=(100017100755285828421/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8082637176700097/50000000000000000000 : ℝ) ≤ ((4189683978571630303/4190000000000000000 : ℝ)+2*(306067253351/754200000000000 : ℝ)*(8649/50000 : ℝ))^(5095/1024 : ℝ) := by
    rw [show (4189683978571630303/4190000000000000000 : ℝ)+2*(306067253351/754200000000000 : ℝ)*(8649/50000 : ℝ)=(400025989482823/400000000000000 : ℝ) by norm_num, show 1+2*(8082637176700097/50000000000000000000 : ℝ)=(25008082637176700097/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4189683978571630303/4190000000000000000 : ℝ)*(X 1 0+X 2 0)+(306067253351/754200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5095/1024 : ℝ)) (lo := (2439/25000 : ℝ)) (hi := (8649/50000 : ℝ)) (c := (4189683978571630303/4190000000000000000 : ℝ)) (alpha := (306067253351/754200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4189683978571630303/4190000000000000000 : ℝ)*(X 0 1+X 2 1)+(306067253351/754200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5095/1024 : ℝ)) (lo := (2439/25000 : ℝ)) (hi := (8649/50000 : ℝ)) (c := (4189683978571630303/4190000000000000000 : ℝ)) (alpha := (306067253351/754200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4189683978571630303/4190000000000000000 : ℝ)*(X 0 2+X 1 2)+(306067253351/754200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5095/1024 : ℝ)) (lo := (2439/25000 : ℝ)) (hi := (8649/50000 : ℝ)) (c := (4189683978571630303/4190000000000000000 : ℝ)) (alpha := (306067253351/754200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1507789547/10000000000 : ℝ)*X 0 0+(171457249/312500000 : ℝ)*X 0 1+(5134366617/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351885453/10000000000 : ℝ)*X 1 0+(-1690857789/10000000000 : ℝ)*X 1 1+(5134366663/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167246407/312500000 : ℝ)*X 2 0+(8214987/16000000 : ℝ)*X 2 1+(-1690858083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1034538447/2500000000 : ℝ)*X 0 0+(1837744957/5000000000 : ℝ)*X 0 1+(4638748153/10000000000 : ℝ)*X 0 2+(1034538447/2500000000 : ℝ)*X 1 0+(1837744957/5000000000 : ℝ)*X 1 1+(4638748153/10000000000 : ℝ)*X 1 2+(1034538447/2500000000 : ℝ)*X 2 0+(1837744957/5000000000 : ℝ)*X 2 1+(4638748153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1507954309/10000000000 : ℝ)*X 0 0+(40142061/78125000 : ℝ)*X 0 1+(5482758011/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1051552211/2000000000 : ℝ)*X 1 0+(-335616539/2500000000 : ℝ)*X 1 1+(1370689501/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1314440271/2500000000 : ℝ)*X 2 0+(5482757939/10000000000 : ℝ)*X 2 1+(-1342466207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2069302731/5000000000 : ℝ)*X 0 0+(4628310289/10000000000 : ℝ)*X 0 1+(921520893/2500000000 : ℝ)*X 0 2+(2069302731/5000000000 : ℝ)*X 1 0+(4628310289/10000000000 : ℝ)*X 1 1+(921520893/2500000000 : ℝ)*X 1 2+(2069302731/5000000000 : ℝ)*X 2 0+(4628310289/10000000000 : ℝ)*X 2 1+(921520893/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1380674847379347635711534159/157125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (153453421/12500000000000 : ℝ)*(base19) + (215439439/25000000000000 : ℝ)*(base23) + (77530269/20000000000000 : ℝ)*(upper3) + (740253/1000000000000 : ℝ)*(upper4) + (84931657/100000000000000 : ℝ)*(upper5) + (484617210558583/25000000000000 : ℝ)*(major0) + (484617210558583/25000000000000 : ℝ)*(major1) + (484617210558583/25000000000000 : ℝ)*(major2) + (709695155119291/25000000000000 : ℝ)*(sp0) + (141939289290943/5000000000000 : ℝ)*(sp1) + (354848268961059/12500000000000 : ℝ)*(sp2) + (519072964165361/50000000000000 : ℝ)*(sp3) + (799121133/12500000000000 : ℝ)*(sp4) + (2224894001/50000000000000 : ℝ)*(sp7) + (41526015124749/4000000000000 : ℝ)*(f.failure) + (709696753361557/25000000000000 : ℝ)*(f.sum) + (9542621916893/9427500000000000000000000000 : ℝ)*base65 + (1611358209134984159/942750000000000000000000000000000 : ℝ)*base68 + (799460425467015841/942750000000000000000000000000000 : ℝ)*base69 + (187429071082484159/942750000000000000000000000000000 : ℝ)*base72 + (6033890922859/4713750000000000000000000000 : ℝ)*base73 + (4790066224455015841/942750000000000000000000000000000 : ℝ)*base75 + (4447884366490515841/942750000000000000000000000000000 : ℝ)*base77 + (5129237793051015841/942750000000000000000000000000000 : ℝ)*base79 + (9767885685049/4713750000000000000000000000 : ℝ)*base81 + (4321931/400000000000000000000 : ℝ)*base89 + (4321931/400000000000000000000 : ℝ)*base91 + (4321931/400000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5426964611590621399789711021/628500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (252987003/20000000000000 : ℝ)*(base19) + (343400261/25000000000000 : ℝ)*(base23) + (74663247/20000000000000 : ℝ)*(lower1) + (98027019/50000000000000 : ℝ)*(upper3) + (10810163/25000000000000 : ℝ)*(lower4) + (11138321/6250000000000 : ℝ)*(upper5) + (1981716434307077/100000000000000 : ℝ)*(major0) + (1981716434307077/100000000000000 : ℝ)*(major1) + (1981716434307077/100000000000000 : ℝ)*(major2) + (9092403/1562500000000 : ℝ)*(sp2) + (1451060439555321/50000000000000 : ℝ)*(sp4) + (1451059807087813/50000000000000 : ℝ)*(sp5) + (580423784719161/20000000000000 : ℝ)*(sp6) + (33165990677413/3125000000000 : ℝ)*(sp7) + (33165990677413/3125000000000 : ℝ)*(f.failure) + (1451060439555321/50000000000000 : ℝ)*(f.sum) + (163375810216913/37710000000000000000000000000 : ℝ)*base66 + (7432093339923661021/3771000000000000000000000000000000 : ℝ)*base68 + (13076910800042338979/3771000000000000000000000000000000 : ℝ)*base69 + (19783774042725661021/3771000000000000000000000000000000 : ℝ)*base72 + (224377933006253/37710000000000000000000000000 : ℝ)*base74 + (49533590886260338979/3771000000000000000000000000000000 : ℝ)*base75 + (20847023092616338979/3771000000000000000000000000000000 : ℝ)*base77 + (45827997889487338979/3771000000000000000000000000000000 : ℝ)*base79 + (117579118190483/37710000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1931253/312500000000000000000 : ℝ)*base90 + (1931253/312500000000000000000 : ℝ)*base92 + (1931253/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1685_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186723319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8649/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2439/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9779/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17271/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1685_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1685_s4_0 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-753903291/5000000000 : ℝ)*x 0 + (5486567119/10000000000 : ℝ)*x 1 + (5134420031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (753903291/5000000000 : ℝ)^5103 ≤ (1172157462213/12500000000000 : ℝ)^4079 := by
    have hnat : (753903291 : ℕ)^5103*12500000000000^4079 ≤ 1172157462213^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753903291 5000000000 1172157462213 12500000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5486567119/10000000000 : ℝ)^5103 ≤ (11797615854231/25000000000000 : ℝ)^4079 := by
    have hnat : (5486567119 : ℕ)^5103*25000000000000^4079 ≤ 11797615854231^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486567119 10000000000 11797615854231 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5134420031/10000000000 : ℝ)^5103 ≤ (339314663063/781250000000 : ℝ)^4079 := by
    have hnat : (5134420031 : ℕ)^5103*781250000000^4079 ≤ 339314663063^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134420031 10000000000 339314663063 781250000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-753903291/5000000000 : ℝ), (5486567119/10000000000 : ℝ), (5134420031/10000000000 : ℝ)] ![(1172157462213/12500000000000 : ℝ), (11797615854231/25000000000000 : ℝ), (339314663063/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-753903291/5000000000 : ℝ)|^5103 ≤ (1172157462213/12500000000000 : ℝ)^4079
        have hw : |(-753903291/5000000000 : ℝ)|=(753903291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5486567119/10000000000 : ℝ)|^5103 ≤ (11797615854231/25000000000000 : ℝ)^4079
        have hw : |(5486567119/10000000000 : ℝ)|=(5486567119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5134420031/10000000000 : ℝ)|^5103 ≤ (339314663063/781250000000 : ℝ)^4079
        have hw : |(5134420031/10000000000 : ℝ)|=(5134420031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s4_1 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675934111/5000000000 : ℝ)*x 0 + (-422702763/2500000000 : ℝ)*x 1 + (2567209719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675934111/5000000000 : ℝ)^5103 ≤ (2287277681633/5000000000000 : ℝ)^4079 := by
    have hnat : (2675934111 : ℕ)^5103*5000000000000^4079 ≤ 2287277681633^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675934111 5000000000 2287277681633 5000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422702763/2500000000 : ℝ)^5103 ≤ (541108787697/5000000000000 : ℝ)^4079 := by
    have hnat : (422702763 : ℕ)^5103*5000000000000^4079 ≤ 541108787697^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422702763 2500000000 541108787697 5000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2567209719/5000000000 : ℝ)^5103 ≤ (10858067649143/25000000000000 : ℝ)^4079 := by
    have hnat : (2567209719 : ℕ)^5103*25000000000000^4079 ≤ 10858067649143^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567209719 5000000000 10858067649143 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675934111/5000000000 : ℝ), (-422702763/2500000000 : ℝ), (2567209719/5000000000 : ℝ)] ![(2287277681633/5000000000000 : ℝ), (541108787697/5000000000000 : ℝ), (10858067649143/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675934111/5000000000 : ℝ)|^5103 ≤ (2287277681633/5000000000000 : ℝ)^4079
        have hw : |(2675934111/5000000000 : ℝ)|=(2675934111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-422702763/2500000000 : ℝ)|^5103 ≤ (541108787697/5000000000000 : ℝ)^4079
        have hw : |(-422702763/2500000000 : ℝ)|=(422702763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2567209719/5000000000 : ℝ)|^5103 ≤ (10858067649143/25000000000000 : ℝ)^4079
        have hw : |(2567209719/5000000000 : ℝ)|=(2567209719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s4_2 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675933841/5000000000 : ℝ)*x 0 + (1283604939/2500000000 : ℝ)*x 1 + (-1690811353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675933841/5000000000 : ℝ)^5103 ≤ (45745547858231/100000000000000 : ℝ)^4079 := by
    have hnat : (2675933841 : ℕ)^5103*100000000000000^4079 ≤ 45745547858231^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675933841 5000000000 45745547858231 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283604939/2500000000 : ℝ)^5103 ≤ (10858068490461/25000000000000 : ℝ)^4079 := by
    have hnat : (1283604939 : ℕ)^5103*25000000000000^4079 ≤ 10858068490461^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283604939 2500000000 10858068490461 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1690811353/10000000000 : ℝ)^5103 ≤ (10822178164167/100000000000000 : ℝ)^4079 := by
    have hnat : (1690811353 : ℕ)^5103*100000000000000^4079 ≤ 10822178164167^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1690811353 10000000000 10822178164167 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675933841/5000000000 : ℝ), (1283604939/2500000000 : ℝ), (-1690811353/10000000000 : ℝ)] ![(45745547858231/100000000000000 : ℝ), (10858068490461/25000000000000 : ℝ), (10822178164167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675933841/5000000000 : ℝ)|^5103 ≤ (45745547858231/100000000000000 : ℝ)^4079
        have hw : |(2675933841/5000000000 : ℝ)|=(2675933841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1283604939/2500000000 : ℝ)|^5103 ≤ (10858068490461/25000000000000 : ℝ)^4079
        have hw : |(1283604939/2500000000 : ℝ)|=(1283604939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1690811353/10000000000 : ℝ)|^5103 ≤ (10822178164167/100000000000000 : ℝ)^4079
        have hw : |(-1690811353/10000000000 : ℝ)|=(1690811353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s4_3 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4138165301/10000000000 : ℝ)*x 0 + (735130033/2000000000 : ℝ)*x 1 + (4638585809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4138165301/10000000000 : ℝ)^5103 ≤ (259060123043/781250000000 : ℝ)^4079 := by
    have hnat : (4138165301 : ℕ)^5103*781250000000^4079 ≤ 259060123043^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4138165301 10000000000 259060123043 781250000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (735130033/2000000000 : ℝ)^5103 ≤ (14295022032823/50000000000000 : ℝ)^4079 := by
    have hnat : (735130033 : ℕ)^5103*50000000000000^4079 ≤ 14295022032823^4079*2000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735130033 2000000000 14295022032823 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4638585809/10000000000 : ℝ)^5103 ≤ (19125130088317/50000000000000 : ℝ)^4079 := by
    have hnat : (4638585809 : ℕ)^5103*50000000000000^4079 ≤ 19125130088317^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4638585809 10000000000 19125130088317 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4138165301/10000000000 : ℝ), (735130033/2000000000 : ℝ), (4638585809/10000000000 : ℝ)] ![(259060123043/781250000000 : ℝ), (14295022032823/50000000000000 : ℝ), (19125130088317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4138165301/10000000000 : ℝ)|^5103 ≤ (259060123043/781250000000 : ℝ)^4079
        have hw : |(4138165301/10000000000 : ℝ)|=(4138165301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(735130033/2000000000 : ℝ)|^5103 ≤ (14295022032823/50000000000000 : ℝ)^4079
        have hw : |(735130033/2000000000 : ℝ)|=(735130033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4638585809/10000000000 : ℝ)|^5103 ≤ (19125130088317/50000000000000 : ℝ)^4079
        have hw : |(4638585809/10000000000 : ℝ)|=(4638585809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s4_4 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-94248203/625000000 : ℝ)*x 0 + (5138234219/10000000000 : ℝ)*x 1 + (1096539233/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94248203/625000000 : ℝ)^5103 ≤ (468927044167/5000000000000 : ℝ)^4079 := by
    have hnat : (94248203 : ℕ)^5103*5000000000000^4079 ≤ 468927044167^4079*625000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94248203 625000000 468927044167 5000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138234219/10000000000 : ℝ)^5103 ≤ (10868161181183/25000000000000 : ℝ)^4079 := by
    have hnat : (5138234219 : ℕ)^5103*25000000000000^4079 ≤ 10868161181183^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138234219 10000000000 10868161181183 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1096539233/2000000000 : ℝ)^5103 ≤ (23574407190643/50000000000000 : ℝ)^4079 := by
    have hnat : (1096539233 : ℕ)^5103*50000000000000^4079 ≤ 23574407190643^4079*2000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096539233 2000000000 23574407190643 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-94248203/625000000 : ℝ), (5138234219/10000000000 : ℝ), (1096539233/2000000000 : ℝ)] ![(468927044167/5000000000000 : ℝ), (10868161181183/25000000000000 : ℝ), (23574407190643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-94248203/625000000 : ℝ)|^5103 ≤ (468927044167/5000000000000 : ℝ)^4079
        have hw : |(-94248203/625000000 : ℝ)|=(94248203/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138234219/10000000000 : ℝ)|^5103 ≤ (10868161181183/25000000000000 : ℝ)^4079
        have hw : |(5138234219/10000000000 : ℝ)|=(5138234219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1096539233/2000000000 : ℝ)|^5103 ≤ (23574407190643/50000000000000 : ℝ)^4079
        have hw : |(1096539233/2000000000 : ℝ)|=(1096539233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s4_5 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262888751/500000000 : ℝ)*x 0 + (-1342535111/10000000000 : ℝ)*x 1 + (5482695751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262888751/500000000 : ℝ)^5103 ≤ (894832175243/2000000000000 : ℝ)^4079 := by
    have hnat : (262888751 : ℕ)^5103*2000000000000^4079 ≤ 894832175243^4079*500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262888751 500000000 894832175243 2000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1342535111/10000000000 : ℝ)^5103 ≤ (8109581302339/100000000000000 : ℝ)^4079 := by
    have hnat : (1342535111 : ℕ)^5103*100000000000000^4079 ≤ 8109581302339^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342535111 10000000000 8109581302339 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5482695751/10000000000 : ℝ)^5103 ≤ (471488099273/1000000000000 : ℝ)^4079 := by
    have hnat : (5482695751 : ℕ)^5103*1000000000000^4079 ≤ 471488099273^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482695751 10000000000 471488099273 1000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262888751/500000000 : ℝ), (-1342535111/10000000000 : ℝ), (5482695751/10000000000 : ℝ)] ![(894832175243/2000000000000 : ℝ), (8109581302339/100000000000000 : ℝ), (471488099273/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262888751/500000000 : ℝ)|^5103 ≤ (894832175243/2000000000000 : ℝ)^4079
        have hw : |(262888751/500000000 : ℝ)|=(262888751/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1342535111/10000000000 : ℝ)|^5103 ≤ (8109581302339/100000000000000 : ℝ)^4079
        have hw : |(-1342535111/10000000000 : ℝ)|=(1342535111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5482695751/10000000000 : ℝ)|^5103 ≤ (471488099273/1000000000000 : ℝ)^4079
        have hw : |(5482695751/10000000000 : ℝ)|=(5482695751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s4_6 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257775009/10000000000 : ℝ)*x 0 + (2741347899/5000000000 : ℝ)*x 1 + (-671267529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257775009/10000000000 : ℝ)^5103 ≤ (22370804322523/50000000000000 : ℝ)^4079 := by
    have hnat : (5257775009 : ℕ)^5103*50000000000000^4079 ≤ 22370804322523^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257775009 10000000000 22370804322523 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2741347899/5000000000 : ℝ)^5103 ≤ (23574405216473/50000000000000 : ℝ)^4079 := by
    have hnat : (2741347899 : ℕ)^5103*50000000000000^4079 ≤ 23574405216473^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741347899 5000000000 23574405216473 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (671267529/5000000000 : ℝ)^5103 ≤ (8109580901823/100000000000000 : ℝ)^4079 := by
    have hnat : (671267529 : ℕ)^5103*100000000000000^4079 ≤ 8109580901823^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671267529 5000000000 8109580901823 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257775009/10000000000 : ℝ), (2741347899/5000000000 : ℝ), (-671267529/5000000000 : ℝ)] ![(22370804322523/50000000000000 : ℝ), (23574405216473/50000000000000 : ℝ), (8109580901823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257775009/10000000000 : ℝ)|^5103 ≤ (22370804322523/50000000000000 : ℝ)^4079
        have hw : |(5257775009/10000000000 : ℝ)|=(5257775009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2741347899/5000000000 : ℝ)|^5103 ≤ (23574405216473/50000000000000 : ℝ)^4079
        have hw : |(2741347899/5000000000 : ℝ)|=(2741347899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-671267529/5000000000 : ℝ)|^5103 ≤ (8109580901823/100000000000000 : ℝ)^4079
        have hw : |(-671267529/5000000000 : ℝ)|=(671267529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s4_7 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2069308119/5000000000 : ℝ)*x 0 + (4628154889/10000000000 : ℝ)*x 1 + (737247403/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2069308119/5000000000 : ℝ)^5103 ≤ (6632843270517/20000000000000 : ℝ)^4079 := by
    have hnat : (2069308119 : ℕ)^5103*20000000000000^4079 ≤ 6632843270517^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069308119 5000000000 6632843270517 20000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4628154889/10000000000 : ℝ)^5103 ≤ (762853657707/2000000000000 : ℝ)^4079 := by
    have hnat : (4628154889 : ℕ)^5103*2000000000000^4079 ≤ 762853657707^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4628154889 10000000000 762853657707 2000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (737247403/2000000000 : ℝ)^5103 ≤ (28693100745891/100000000000000 : ℝ)^4079 := by
    have hnat : (737247403 : ℕ)^5103*100000000000000^4079 ≤ 28693100745891^4079*2000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737247403 2000000000 28693100745891 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2069308119/5000000000 : ℝ), (4628154889/10000000000 : ℝ), (737247403/2000000000 : ℝ)] ![(6632843270517/20000000000000 : ℝ), (762853657707/2000000000000 : ℝ), (28693100745891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2069308119/5000000000 : ℝ)|^5103 ≤ (6632843270517/20000000000000 : ℝ)^4079
        have hw : |(2069308119/5000000000 : ℝ)|=(2069308119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4628154889/10000000000 : ℝ)|^5103 ≤ (762853657707/2000000000000 : ℝ)^4079
        have hw : |(4628154889/10000000000 : ℝ)|=(4628154889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(737247403/2000000000 : ℝ)|^5103 ≤ (28693100745891/100000000000000 : ℝ)^4079
        have hw : |(737247403/2000000000 : ℝ)|=(737247403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1685_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186723319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17271/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9779/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (489/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1727/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17271/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9779/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17271/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9779/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17271/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9779/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17271/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9779/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17271/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9779/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17271/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9779/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9779/100000 : ℝ) ^ (5095/1024 : ℝ) ≤ (189301144989317/20000000000000000000 : ℝ) := by
    have hpowers : (9779/100000 : ℝ)^5095 ≤ (189301144989317/20000000000000000000 : ℝ)^1024 := by
      have hnat : (9779 : ℕ)^5095*20000000000000000000^1024 ≤ 189301144989317^1024*100000^5095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9779 100000 189301144989317 20000000000000000000 5095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9779/100000 : ℝ)) (X := (189301144989317/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17271/100000 : ℝ) ^ (5095/1024 : ℝ) ≤ (4010029874989493/25000000000000000000 : ℝ) := by
    have hpowers : (17271/100000 : ℝ)^5095 ≤ (4010029874989493/25000000000000000000 : ℝ)^1024 := by
      have hnat : (17271 : ℕ)^5095*25000000000000000000^1024 ≤ 4010029874989493^1024*100000^5095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17271 100000 4010029874989493 25000000000000000000 5095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17271/100000 : ℝ)) (X := (4010029874989493/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000189301144989317/10000000000000000000 : ℝ) ≤ (2500009511428189/2500000000000000 : ℝ) ^ (5095/1024 : ℝ) := by
    have hpowers : (10000189301144989317/10000000000000000000 : ℝ)^1024 ≤ (2500009511428189/2500000000000000 : ℝ)^5095 := by
      have hnat : (10000189301144989317 : ℕ)^1024*2500000000000000^5095 ≤ 2500009511428189^5095*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000189301144989317 10000000000000000000 2500009511428189 2500000000000000 1024 5095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500009511428189/2500000000000000 : ℝ)) (X := (10000189301144989317/10000000000000000000 : ℝ)) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100016986625224904557/100000000000000000000 : ℝ) ≤ (10000341376328131/10000000000000000 : ℝ) ^ (5095/1024 : ℝ) := by
    have hpowers : (100016986625224904557/100000000000000000000 : ℝ)^1024 ≤ (10000341376328131/10000000000000000 : ℝ)^5095 := by
      have hnat : (100016986625224904557 : ℕ)^1024*10000000000000000^5095 ≤ 10000341376328131^5095*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100016986625224904557 100000000000000000000 10000341376328131 10000000000000000 1024 5095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000341376328131/10000000000000000 : ℝ)) (X := (100016986625224904557/100000000000000000000 : ℝ)) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12504010029874989493/12500000000000000000 : ℝ) ≤ (5000322353471753/5000000000000000 : ℝ) ^ (5095/1024 : ℝ) := by
    have hpowers : (12504010029874989493/12500000000000000000 : ℝ)^1024 ≤ (5000322353471753/5000000000000000 : ℝ)^5095 := by
      have hnat : (12504010029874989493 : ℕ)^1024*5000000000000000^5095 ≤ 5000322353471753^5095*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504010029874989493 12500000000000000000 5000322353471753 5000000000000000 1024 5095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000322353471753/5000000000000000 : ℝ)) (X := (12504010029874989493/12500000000000000000 : ℝ)) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(189301144989317/20000000000000000000 : ℝ) ≤ ((37457176249152231851/37460000000000000000 : ℝ)+2*(2426644923/5993600000000 : ℝ)*(9779/100000 : ℝ))^(5095/1024 : ℝ) := by
    rw [show (37457176249152231851/37460000000000000000 : ℝ)+2*(2426644923/5993600000000 : ℝ)*(9779/100000 : ℝ)=(2500009511428189/2500000000000000 : ℝ) by norm_num, show 1+2*(189301144989317/20000000000000000000 : ℝ)=(10000189301144989317/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4010029874989493/25000000000000000000 : ℝ)+(189301144989317/20000000000000000000 : ℝ) ≤ ((37457176249152231851/37460000000000000000 : ℝ)+(2426644923/5993600000000 : ℝ)*((17271/100000 : ℝ)+(9779/100000 : ℝ)))^(5095/1024 : ℝ) := by
    rw [show (37457176249152231851/37460000000000000000 : ℝ)+(2426644923/5993600000000 : ℝ)*((17271/100000 : ℝ)+(9779/100000 : ℝ))=(10000341376328131/10000000000000000 : ℝ) by norm_num, show 1+(4010029874989493/25000000000000000000 : ℝ)+(189301144989317/20000000000000000000 : ℝ)=(100016986625224904557/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4010029874989493/25000000000000000000 : ℝ) ≤ ((37457176249152231851/37460000000000000000 : ℝ)+2*(2426644923/5993600000000 : ℝ)*(17271/100000 : ℝ))^(5095/1024 : ℝ) := by
    rw [show (37457176249152231851/37460000000000000000 : ℝ)+2*(2426644923/5993600000000 : ℝ)*(17271/100000 : ℝ)=(5000322353471753/5000000000000000 : ℝ) by norm_num, show 1+2*(4010029874989493/25000000000000000000 : ℝ)=(12504010029874989493/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37457176249152231851/37460000000000000000 : ℝ)*(X 1 0+X 2 0)+(2426644923/5993600000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5095/1024 : ℝ)) (lo := (9779/100000 : ℝ)) (hi := (17271/100000 : ℝ)) (c := (37457176249152231851/37460000000000000000 : ℝ)) (alpha := (2426644923/5993600000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37457176249152231851/37460000000000000000 : ℝ)*(X 0 1+X 2 1)+(2426644923/5993600000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5095/1024 : ℝ)) (lo := (9779/100000 : ℝ)) (hi := (17271/100000 : ℝ)) (c := (37457176249152231851/37460000000000000000 : ℝ)) (alpha := (2426644923/5993600000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37457176249152231851/37460000000000000000 : ℝ)*(X 0 2+X 1 2)+(2426644923/5993600000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5095/1024 : ℝ)) (lo := (9779/100000 : ℝ)) (hi := (17271/100000 : ℝ)) (c := (37457176249152231851/37460000000000000000 : ℝ)) (alpha := (2426644923/5993600000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-753903291/5000000000 : ℝ)*X 0 0+(5486567119/10000000000 : ℝ)*X 0 1+(5134420031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675934111/5000000000 : ℝ)*X 1 0+(-422702763/2500000000 : ℝ)*X 1 1+(2567209719/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675933841/5000000000 : ℝ)*X 2 0+(1283604939/2500000000 : ℝ)*X 2 1+(-1690811353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4138165301/10000000000 : ℝ)*X 0 0+(735130033/2000000000 : ℝ)*X 0 1+(4638585809/10000000000 : ℝ)*X 0 2+(4138165301/10000000000 : ℝ)*X 1 0+(735130033/2000000000 : ℝ)*X 1 1+(4638585809/10000000000 : ℝ)*X 1 2+(4138165301/10000000000 : ℝ)*X 2 0+(735130033/2000000000 : ℝ)*X 2 1+(4638585809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-94248203/625000000 : ℝ)*X 0 0+(5138234219/10000000000 : ℝ)*X 0 1+(1096539233/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((262888751/500000000 : ℝ)*X 1 0+(-1342535111/10000000000 : ℝ)*X 1 1+(5482695751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5257775009/10000000000 : ℝ)*X 2 0+(2741347899/5000000000 : ℝ)*X 2 1+(-671267529/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2069308119/5000000000 : ℝ)*X 0 0+(4628154889/10000000000 : ℝ)*X 0 1+(737247403/2000000000 : ℝ)*X 0 2+(2069308119/5000000000 : ℝ)*X 1 0+(4628154889/10000000000 : ℝ)*X 1 1+(737247403/2000000000 : ℝ)*X 1 2+(2069308119/5000000000 : ℝ)*X 2 0+(4628154889/10000000000 : ℝ)*X 2 1+(737247403/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (559008090609686970055602063/58531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1832513769/100000000000000 : ℝ)*(base19) + (1453614883/100000000000000 : ℝ)*(base23) + (2972849/800000000000 : ℝ)*(upper3) + (24717693/50000000000000 : ℝ)*(upper4) + (21869791/25000000000000 : ℝ)*(upper5) + (60597655106421/3125000000000 : ℝ)*(major0) + (60597655106421/3125000000000 : ℝ)*(major1) + (60597655106421/3125000000000 : ℝ)*(major2) + (2839737747453257/100000000000000 : ℝ)*(sp0) + (88742062843277/3125000000000 : ℝ)*(sp1) + (2271797111907/80000000000 : ℝ)*(sp2) + (1038495616614719/100000000000000 : ℝ)*(sp3) + (157750709/1562500000000 : ℝ)*(sp4) + (6148344521/100000000000000 : ℝ)*(sp7) + (25962544123981/2500000000000 : ℝ)*(f.failure) + (2839747843498633/100000000000000 : ℝ)*(f.sum) + (459756525567/374600000000000000000000000 : ℝ)*base66 + (558964526420622229/117062500000000000000000000000000 : ℝ)*base68 + (127563516690252771/117062500000000000000000000000000 : ℝ)*base69 + (511064833436997229/117062500000000000000000000000000 : ℝ)*base72 + (936683006537/468250000000000000000000000 : ℝ)*base74 + (56481712188690271/117062500000000000000000000000000 : ℝ)*base75 + (136157625381747229/117062500000000000000000000000000 : ℝ)*base78 + (694497975653684729/117062500000000000000000000000000 : ℝ)*base80 + (432385598067/117062500000000000000000000 : ℝ)*base81 + (187061/250000000000000000000 : ℝ)*base90 + (187061/250000000000000000000 : ℝ)*base92 + (187061/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6063921490463733049027045581/468250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1869967289/100000000000000 : ℝ)*(base19) + (1913781221/100000000000000 : ℝ)*(base23) + (256326007/50000000000000 : ℝ)*(lower1) + (176465959/100000000000000 : ℝ)*(upper3) + (3579809/10000000000000 : ℝ)*(lower4) + (323979667/100000000000000 : ℝ)*(upper5) + (495590425965359/25000000000000 : ℝ)*(major0) + (495590425965359/25000000000000 : ℝ)*(major1) + (495590425965359/25000000000000 : ℝ)*(major2) + (1016900201/100000000000000 : ℝ)*(sp1) + (2903065699134829/100000000000000 : ℝ)*(sp4) + (2903062812267339/100000000000000 : ℝ)*(sp5) + (362882973169201/12500000000000 : ℝ)*(sp6) + (106165727691539/10000000000000 : ℝ)*(sp7) + (106165727691539/10000000000000 : ℝ)*(f.failure) + (2903065699134829/100000000000000 : ℝ)*(f.sum) + (6332203793881/1873000000000000000000000000 : ℝ)*base65 + (6291136736132800491/936500000000000000000000000000000 : ℝ)*base68 + (13231759600383800491/936500000000000000000000000000000 : ℝ)*base70 + (3470990567609300491/936500000000000000000000000000000 : ℝ)*base72 + (484523355101/234125000000000000000000000 : ℝ)*base73 + (11317228486916800491/936500000000000000000000000000000 : ℝ)*base76 + (8281789260164300491/936500000000000000000000000000000 : ℝ)*base78 + (9534447541437300491/936500000000000000000000000000000 : ℝ)*base80 + (2987217421653/1873000000000000000000000000 : ℝ)*base82 + (10297941/1000000000000000000000 : ℝ)*base89 + (10297941/1000000000000000000000 : ℝ)*base91 + (10297941/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1685_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186723319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17271/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9779/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (489/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1727/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1685_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1685_box_0 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-292121441/2500000000 : ℝ)*x 0 + (1357714601/2500000000 : ℝ)*x 1 + (5430857093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (292121441/2500000000 : ℝ)^5103 ≤ (6816443171007/100000000000000 : ℝ)^4079 := by
    have hnat : (292121441 : ℕ)^5103*100000000000000^4079 ≤ 6816443171007^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292121441 2500000000 6816443171007 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357714601/2500000000 : ℝ)^5103 ≤ (23295892722549/50000000000000 : ℝ)^4079 := by
    have hnat : (1357714601 : ℕ)^5103*50000000000000^4079 ≤ 23295892722549^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357714601 2500000000 23295892722549 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430857093/10000000000 : ℝ)^5103 ≤ (46591771374407/100000000000000 : ℝ)^4079 := by
    have hnat : (5430857093 : ℕ)^5103*100000000000000^4079 ≤ 46591771374407^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430857093 10000000000 46591771374407 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-292121441/2500000000 : ℝ), (1357714601/2500000000 : ℝ), (5430857093/10000000000 : ℝ)] ![(6816443171007/100000000000000 : ℝ), (23295892722549/50000000000000 : ℝ), (46591771374407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-292121441/2500000000 : ℝ)|^5103 ≤ (6816443171007/100000000000000 : ℝ)^4079
        have hw : |(-292121441/2500000000 : ℝ)|=(292121441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357714601/2500000000 : ℝ)|^5103 ≤ (23295892722549/50000000000000 : ℝ)^4079
        have hw : |(1357714601/2500000000 : ℝ)|=(1357714601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430857093/10000000000 : ℝ)|^5103 ≤ (46591771374407/100000000000000 : ℝ)^4079
        have hw : |(5430857093/10000000000 : ℝ)|=(5430857093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_box_1 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (653261169/1250000000 : ℝ)*x 0 + (-729797961/5000000000 : ℝ)*x 1 + (33942861/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653261169/1250000000 : ℝ)^5103 ≤ (44404542575639/100000000000000 : ℝ)^4079 := by
    have hnat : (653261169 : ℕ)^5103*100000000000000^4079 ≤ 44404542575639^4079*1250000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653261169 1250000000 44404542575639 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (729797961/5000000000 : ℝ)^5103 ≤ (1800735775567/20000000000000 : ℝ)^4079 := by
    have hnat : (729797961 : ℕ)^5103*20000000000000^4079 ≤ 1800735775567^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729797961 5000000000 1800735775567 20000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33942861/62500000 : ℝ)^5103 ≤ (46591778533179/100000000000000 : ℝ)^4079 := by
    have hnat : (33942861 : ℕ)^5103*100000000000000^4079 ≤ 46591778533179^4079*62500000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33942861 62500000 46591778533179 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653261169/1250000000 : ℝ), (-729797961/5000000000 : ℝ), (33942861/62500000 : ℝ)] ![(44404542575639/100000000000000 : ℝ), (1800735775567/20000000000000 : ℝ), (46591778533179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653261169/1250000000 : ℝ)|^5103 ≤ (44404542575639/100000000000000 : ℝ)^4079
        have hw : |(653261169/1250000000 : ℝ)|=(653261169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-729797961/5000000000 : ℝ)|^5103 ≤ (1800735775567/20000000000000 : ℝ)^4079
        have hw : |(-729797961/5000000000 : ℝ)|=(729797961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33942861/62500000 : ℝ)|^5103 ≤ (46591778533179/100000000000000 : ℝ)^4079
        have hw : |(33942861/62500000 : ℝ)|=(33942861/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_box_2 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226089481/10000000000 : ℝ)*x 0 + (1357714469/2500000000 : ℝ)*x 1 + (-729797791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226089481/10000000000 : ℝ)^5103 ≤ (14209454063/32000000000 : ℝ)^4079 := by
    have hnat : (5226089481 : ℕ)^5103*32000000000^4079 ≤ 14209454063^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226089481 10000000000 14209454063 32000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357714469/2500000000 : ℝ)^5103 ≤ (46591779778183/100000000000000 : ℝ)^4079 := by
    have hnat : (1357714469 : ℕ)^5103*100000000000000^4079 ≤ 46591779778183^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357714469 2500000000 46591779778183 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (729797791/5000000000 : ℝ)^5103 ≤ (900367625399/10000000000000 : ℝ)^4079 := by
    have hnat : (729797791 : ℕ)^5103*10000000000000^4079 ≤ 900367625399^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729797791 5000000000 900367625399 10000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226089481/10000000000 : ℝ), (1357714469/2500000000 : ℝ), (-729797791/5000000000 : ℝ)] ![(14209454063/32000000000 : ℝ), (46591779778183/100000000000000 : ℝ), (900367625399/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226089481/10000000000 : ℝ)|^5103 ≤ (14209454063/32000000000 : ℝ)^4079
        have hw : |(5226089481/10000000000 : ℝ)|=(5226089481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357714469/2500000000 : ℝ)|^5103 ≤ (46591779778183/100000000000000 : ℝ)^4079
        have hw : |(1357714469/2500000000 : ℝ)|=(1357714469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-729797791/5000000000 : ℝ)|^5103 ≤ (900367625399/10000000000000 : ℝ)^4079
        have hw : |(-729797791/5000000000 : ℝ)|=(729797791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_box_3 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4523188921/10000000000 : ℝ)*x 0 + (3968554959/10000000000 : ℝ)*x 1 + (3968555007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4523188921/10000000000 : ℝ)^5103 ≤ (37063541055137/100000000000000 : ℝ)^4079 := by
    have hnat : (4523188921 : ℕ)^5103*100000000000000^4079 ≤ 37063541055137^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523188921 10000000000 37063541055137 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3968554959/10000000000 : ℝ)^5103 ≤ (31468229226741/100000000000000 : ℝ)^4079 := by
    have hnat : (3968554959 : ℕ)^5103*100000000000000^4079 ≤ 31468229226741^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3968554959 10000000000 31468229226741 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3968555007/10000000000 : ℝ)^5103 ≤ (31468229702901/100000000000000 : ℝ)^4079 := by
    have hnat : (3968555007 : ℕ)^5103*100000000000000^4079 ≤ 31468229702901^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3968555007 10000000000 31468229702901 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4523188921/10000000000 : ℝ), (3968554959/10000000000 : ℝ), (3968555007/10000000000 : ℝ)] ![(37063541055137/100000000000000 : ℝ), (31468229226741/100000000000000 : ℝ), (31468229702901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4523188921/10000000000 : ℝ)|^5103 ≤ (37063541055137/100000000000000 : ℝ)^4079
        have hw : |(4523188921/10000000000 : ℝ)|=(4523188921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3968554959/10000000000 : ℝ)|^5103 ≤ (31468229226741/100000000000000 : ℝ)^4079
        have hw : |(3968554959/10000000000 : ℝ)|=(3968554959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3968555007/10000000000 : ℝ)|^5103 ≤ (31468229702901/100000000000000 : ℝ)^4079
        have hw : |(3968555007/10000000000 : ℝ)|=(3968555007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_box_4 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-934081513/5000000000 : ℝ)*x 0 + (1035143239/2000000000 : ℝ)*x 1 + (646964407/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (934081513/5000000000 : ℝ)^5103 ≤ (6130266301419/50000000000000 : ℝ)^4079 := by
    have hnat : (934081513 : ℕ)^5103*50000000000000^4079 ≤ 6130266301419^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934081513 5000000000 6130266301419 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035143239/2000000000 : ℝ)^5103 ≤ (43869738665693/100000000000000 : ℝ)^4079 := by
    have hnat : (1035143239 : ℕ)^5103*100000000000000^4079 ≤ 43869738665693^4079*2000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035143239 2000000000 43869738665693 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (646964407/1250000000 : ℝ)^5103 ≤ (10967432177153/25000000000000 : ℝ)^4079 := by
    have hnat : (646964407 : ℕ)^5103*25000000000000^4079 ≤ 10967432177153^4079*1250000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646964407 1250000000 10967432177153 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-934081513/5000000000 : ℝ), (1035143239/2000000000 : ℝ), (646964407/1250000000 : ℝ)] ![(6130266301419/50000000000000 : ℝ), (43869738665693/100000000000000 : ℝ), (10967432177153/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-934081513/5000000000 : ℝ)|^5103 ≤ (6130266301419/50000000000000 : ℝ)^4079
        have hw : |(-934081513/5000000000 : ℝ)|=(934081513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035143239/2000000000 : ℝ)|^5103 ≤ (43869738665693/100000000000000 : ℝ)^4079
        have hw : |(1035143239/2000000000 : ℝ)|=(1035143239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(646964407/1250000000 : ℝ)|^5103 ≤ (10967432177153/25000000000000 : ℝ)^4079
        have hw : |(646964407/1250000000 : ℝ)|=(646964407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_box_5 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540018993/1000000000 : ℝ)*x 0 + (-196310067/1250000000 : ℝ)*x 1 + (646964453/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540018993/1000000000 : ℝ)^5103 ≤ (11565715180161/25000000000000 : ℝ)^4079 := by
    have hnat : (540018993 : ℕ)^5103*25000000000000^4079 ≤ 11565715180161^4079*1000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540018993 1000000000 11565715180161 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196310067/1250000000 : ℝ)^5103 ≤ (2466851662333/25000000000000 : ℝ)^4079 := by
    have hnat : (196310067 : ℕ)^5103*25000000000000^4079 ≤ 2466851662333^4079*1250000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196310067 1250000000 2466851662333 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (646964453/1250000000 : ℝ)^5103 ≤ (21934866305427/50000000000000 : ℝ)^4079 := by
    have hnat : (646964453 : ℕ)^5103*50000000000000^4079 ≤ 21934866305427^4079*1250000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646964453 1250000000 21934866305427 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540018993/1000000000 : ℝ), (-196310067/1250000000 : ℝ), (646964453/1250000000 : ℝ)] ![(11565715180161/25000000000000 : ℝ), (2466851662333/25000000000000 : ℝ), (21934866305427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540018993/1000000000 : ℝ)|^5103 ≤ (11565715180161/25000000000000 : ℝ)^4079
        have hw : |(540018993/1000000000 : ℝ)|=(540018993/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-196310067/1250000000 : ℝ)|^5103 ≤ (2466851662333/25000000000000 : ℝ)^4079
        have hw : |(-196310067/1250000000 : ℝ)|=(196310067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(646964453/1250000000 : ℝ)|^5103 ≤ (21934866305427/50000000000000 : ℝ)^4079
        have hw : |(646964453/1250000000 : ℝ)|=(646964453/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_box_6 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5400190201/10000000000 : ℝ)*x 0 + (5175715541/10000000000 : ℝ)*x 1 + (-1570480279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400190201/10000000000 : ℝ)^5103 ≤ (46262863625099/100000000000000 : ℝ)^4079 := by
    have hnat : (5400190201 : ℕ)^5103*100000000000000^4079 ≤ 46262863625099^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400190201 10000000000 46262863625099 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5175715541/10000000000 : ℝ)^5103 ≤ (43869731730729/100000000000000 : ℝ)^4079 := by
    have hnat : (5175715541 : ℕ)^5103*100000000000000^4079 ≤ 43869731730729^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175715541 10000000000 43869731730729 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1570480279/10000000000 : ℝ)^5103 ≤ (493370231461/5000000000000 : ℝ)^4079 := by
    have hnat : (1570480279 : ℕ)^5103*5000000000000^4079 ≤ 493370231461^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1570480279 10000000000 493370231461 5000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400190201/10000000000 : ℝ), (5175715541/10000000000 : ℝ), (-1570480279/10000000000 : ℝ)] ![(46262863625099/100000000000000 : ℝ), (43869731730729/100000000000000 : ℝ), (493370231461/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400190201/10000000000 : ℝ)|^5103 ≤ (46262863625099/100000000000000 : ℝ)^4079
        have hw : |(5400190201/10000000000 : ℝ)|=(5400190201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5175715541/10000000000 : ℝ)|^5103 ≤ (43869731730729/100000000000000 : ℝ)^4079
        have hw : |(5175715541/10000000000 : ℝ)|=(5175715541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1570480279/10000000000 : ℝ)|^5103 ≤ (493370231461/5000000000000 : ℝ)^4079
        have hw : |(-1570480279/10000000000 : ℝ)|=(1570480279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_box_7 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (934711881/2500000000 : ℝ)*x 0 + (4359855063/10000000000 : ℝ)*x 1 + (272490937/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (934711881/2500000000 : ℝ)^5103 ≤ (14603166041723/50000000000000 : ℝ)^4079 := by
    have hnat : (934711881 : ℕ)^5103*50000000000000^4079 ≤ 14603166041723^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934711881 2500000000 14603166041723 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4359855063/10000000000 : ℝ)^5103 ≤ (8849208578769/25000000000000 : ℝ)^4079 := by
    have hnat : (4359855063 : ℕ)^5103*25000000000000^4079 ≤ 8849208578769^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359855063 10000000000 8849208578769 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272490937/625000000 : ℝ)^5103 ≤ (35396833593931/100000000000000 : ℝ)^4079 := by
    have hnat : (272490937 : ℕ)^5103*100000000000000^4079 ≤ 35396833593931^4079*625000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272490937 625000000 35396833593931 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(934711881/2500000000 : ℝ), (4359855063/10000000000 : ℝ), (272490937/625000000 : ℝ)] ![(14603166041723/50000000000000 : ℝ), (8849208578769/25000000000000 : ℝ), (35396833593931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(934711881/2500000000 : ℝ)|^5103 ≤ (14603166041723/50000000000000 : ℝ)^4079
        have hw : |(934711881/2500000000 : ℝ)|=(934711881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4359855063/10000000000 : ℝ)|^5103 ≤ (8849208578769/25000000000000 : ℝ)^4079
        have hw : |(4359855063/10000000000 : ℝ)|=(4359855063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(272490937/625000000 : ℝ)|^5103 ≤ (35396833593931/100000000000000 : ℝ)^4079
        have hw : |(272490937/625000000 : ℝ)|=(272490937/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_box_8 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-859069189/5000000000 : ℝ)*x 0 + (38974719/78125000 : ℝ)*x 1 + (5474641783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859069189/5000000000 : ℝ)^5103 ≤ (11041438649071/100000000000000 : ℝ)^4079 := by
    have hnat : (859069189 : ℕ)^5103*100000000000000^4079 ≤ 11041438649071^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859069189 5000000000 11041438649071 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38974719/78125000 : ℝ)^5103 ≤ (20948191696879/50000000000000 : ℝ)^4079 := by
    have hnat : (38974719 : ℕ)^5103*50000000000000^4079 ≤ 20948191696879^4079*78125000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38974719 78125000 20948191696879 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5474641783/10000000000 : ℝ)^5103 ≤ (9412435589627/20000000000000 : ℝ)^4079 := by
    have hnat : (5474641783 : ℕ)^5103*20000000000000^4079 ≤ 9412435589627^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474641783 10000000000 9412435589627 20000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-859069189/5000000000 : ℝ), (38974719/78125000 : ℝ), (5474641783/10000000000 : ℝ)] ![(11041438649071/100000000000000 : ℝ), (20948191696879/50000000000000 : ℝ), (9412435589627/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-859069189/5000000000 : ℝ)|^5103 ≤ (11041438649071/100000000000000 : ℝ)^4079
        have hw : |(-859069189/5000000000 : ℝ)|=(859069189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38974719/78125000 : ℝ)|^5103 ≤ (20948191696879/50000000000000 : ℝ)^4079
        have hw : |(38974719/78125000 : ℝ)|=(38974719/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5474641783/10000000000 : ℝ)|^5103 ≤ (9412435589627/20000000000000 : ℝ)^4079
        have hw : |(5474641783/10000000000 : ℝ)|=(5474641783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_box_9 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598110297/5000000000 : ℝ)*x 0 + (-287943519/2000000000 : ℝ)*x 1 + (5474642821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598110297/5000000000 : ℝ)^5103 ≤ (44087273692419/100000000000000 : ℝ)^4079 := by
    have hnat : (2598110297 : ℕ)^5103*100000000000000^4079 ≤ 44087273692419^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598110297 5000000000 44087273692419 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (287943519/2000000000 : ℝ)^5103 ≤ (354021487257/4000000000000 : ℝ)^4079 := by
    have hnat : (287943519 : ℕ)^5103*4000000000000^4079 ≤ 354021487257^4079*2000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287943519 2000000000 354021487257 4000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5474642821/10000000000 : ℝ)^5103 ≤ (23531094555627/50000000000000 : ℝ)^4079 := by
    have hnat : (5474642821 : ℕ)^5103*50000000000000^4079 ≤ 23531094555627^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474642821 10000000000 23531094555627 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598110297/5000000000 : ℝ), (-287943519/2000000000 : ℝ), (5474642821/10000000000 : ℝ)] ![(44087273692419/100000000000000 : ℝ), (354021487257/4000000000000 : ℝ), (23531094555627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598110297/5000000000 : ℝ)|^5103 ≤ (44087273692419/100000000000000 : ℝ)^4079
        have hw : |(2598110297/5000000000 : ℝ)|=(2598110297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-287943519/2000000000 : ℝ)|^5103 ≤ (354021487257/4000000000000 : ℝ)^4079
        have hw : |(-287943519/2000000000 : ℝ)|=(287943519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5474642821/10000000000 : ℝ)|^5103 ≤ (23531094555627/50000000000000 : ℝ)^4079
        have hw : |(5474642821/10000000000 : ℝ)|=(5474642821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_box_10 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598110377/5000000000 : ℝ)*x 0 + (342165187/625000000 : ℝ)*x 1 + (-89982321/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598110377/5000000000 : ℝ)^5103 ≤ (44087275390731/100000000000000 : ℝ)^4079 := by
    have hnat : (2598110377 : ℕ)^5103*100000000000000^4079 ≤ 44087275390731^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598110377 5000000000 44087275390731 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342165187/625000000 : ℝ)^5103 ≤ (9412438190053/20000000000000 : ℝ)^4079 := by
    have hnat : (342165187 : ℕ)^5103*20000000000000^4079 ≤ 9412438190053^4079*625000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342165187 625000000 9412438190053 20000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89982321/625000000 : ℝ)^5103 ≤ (553158353213/6250000000000 : ℝ)^4079 := by
    have hnat : (89982321 : ℕ)^5103*6250000000000^4079 ≤ 553158353213^4079*625000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89982321 625000000 553158353213 6250000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598110377/5000000000 : ℝ), (342165187/625000000 : ℝ), (-89982321/625000000 : ℝ)] ![(44087275390731/100000000000000 : ℝ), (9412438190053/20000000000000 : ℝ), (553158353213/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598110377/5000000000 : ℝ)|^5103 ≤ (44087275390731/100000000000000 : ℝ)^4079
        have hw : |(2598110377/5000000000 : ℝ)|=(2598110377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(342165187/625000000 : ℝ)|^5103 ≤ (9412438190053/20000000000000 : ℝ)^4079
        have hw : |(342165187/625000000 : ℝ)|=(342165187/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-89982321/625000000 : ℝ)|^5103 ≤ (553158353213/6250000000000 : ℝ)^4079
        have hw : |(-89982321/625000000 : ℝ)|=(89982321/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_box_11 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4652748679/10000000000 : ℝ)*x 0 + (3901230721/10000000000 : ℝ)*x 1 + (3901228179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4652748679/10000000000 : ℝ)^5103 ≤ (38396423434689/100000000000000 : ℝ)^4079 := by
    have hnat : (4652748679 : ℕ)^5103*100000000000000^4079 ≤ 38396423434689^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4652748679 10000000000 38396423434689 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3901230721/10000000000 : ℝ)^5103 ≤ (30801800832363/100000000000000 : ℝ)^4079 := by
    have hnat : (3901230721 : ℕ)^5103*100000000000000^4079 ≤ 30801800832363^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3901230721 10000000000 30801800832363 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3901228179/10000000000 : ℝ)^5103 ≤ (30801775723801/100000000000000 : ℝ)^4079 := by
    have hnat : (3901228179 : ℕ)^5103*100000000000000^4079 ≤ 30801775723801^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3901228179 10000000000 30801775723801 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4652748679/10000000000 : ℝ), (3901230721/10000000000 : ℝ), (3901228179/10000000000 : ℝ)] ![(38396423434689/100000000000000 : ℝ), (30801800832363/100000000000000 : ℝ), (30801775723801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4652748679/10000000000 : ℝ)|^5103 ≤ (38396423434689/100000000000000 : ℝ)^4079
        have hw : |(4652748679/10000000000 : ℝ)|=(4652748679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3901230721/10000000000 : ℝ)|^5103 ≤ (30801800832363/100000000000000 : ℝ)^4079
        have hw : |(3901230721/10000000000 : ℝ)|=(3901230721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3901228179/10000000000 : ℝ)|^5103 ≤ (30801775723801/100000000000000 : ℝ)^4079
        have hw : |(3901228179/10000000000 : ℝ)|=(3901228179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_box_12 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1313880599/10000000000 : ℝ)*x 0 + (5608411333/10000000000 : ℝ)*x 1 + (643796943/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313880599/10000000000 : ℝ)^5103 ≤ (61668943619/781250000000 : ℝ)^4079 := by
    have hnat : (1313880599 : ℕ)^5103*781250000000^4079 ≤ 61668943619^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313880599 10000000000 61668943619 781250000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5608411333/10000000000 : ℝ)^5103 ≤ (48505181443367/100000000000000 : ℝ)^4079 := by
    have hnat : (5608411333 : ℕ)^5103*100000000000000^4079 ≤ 48505181443367^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5608411333 10000000000 48505181443367 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (643796943/1250000000 : ℝ)^5103 ≤ (4360119376197/10000000000000 : ℝ)^4079 := by
    have hnat : (643796943 : ℕ)^5103*10000000000000^4079 ≤ 4360119376197^4079*1250000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643796943 1250000000 4360119376197 10000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1313880599/10000000000 : ℝ), (5608411333/10000000000 : ℝ), (643796943/1250000000 : ℝ)] ![(61668943619/781250000000 : ℝ), (48505181443367/100000000000000 : ℝ), (4360119376197/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1313880599/10000000000 : ℝ)|^5103 ≤ (61668943619/781250000000 : ℝ)^4079
        have hw : |(-1313880599/10000000000 : ℝ)|=(1313880599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5608411333/10000000000 : ℝ)|^5103 ≤ (48505181443367/100000000000000 : ℝ)^4079
        have hw : |(5608411333/10000000000 : ℝ)|=(5608411333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(643796943/1250000000 : ℝ)|^5103 ≤ (4360119376197/10000000000000 : ℝ)^4079
        have hw : |(643796943/1250000000 : ℝ)|=(643796943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_box_13 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5417508129/10000000000 : ℝ)*x 0 + (-1581012769/10000000000 : ℝ)*x 1 + (5150375443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417508129/10000000000 : ℝ)^5103 ≤ (46448543951797/100000000000000 : ℝ)^4079 := by
    have hnat : (5417508129 : ℕ)^5103*100000000000000^4079 ≤ 46448543951797^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417508129 10000000000 46448543951797 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1581012769/10000000000 : ℝ)^5103 ≤ (1990052669051/20000000000000 : ℝ)^4079 := by
    have hnat : (1581012769 : ℕ)^5103*20000000000000^4079 ≤ 1990052669051^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1581012769 10000000000 1990052669051 20000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5150375443/10000000000 : ℝ)^5103 ≤ (43601192692293/100000000000000 : ℝ)^4079 := by
    have hnat : (5150375443 : ℕ)^5103*100000000000000^4079 ≤ 43601192692293^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150375443 10000000000 43601192692293 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417508129/10000000000 : ℝ), (-1581012769/10000000000 : ℝ), (5150375443/10000000000 : ℝ)] ![(46448543951797/100000000000000 : ℝ), (1990052669051/20000000000000 : ℝ), (43601192692293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417508129/10000000000 : ℝ)|^5103 ≤ (46448543951797/100000000000000 : ℝ)^4079
        have hw : |(5417508129/10000000000 : ℝ)|=(5417508129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1581012769/10000000000 : ℝ)|^5103 ≤ (1990052669051/20000000000000 : ℝ)^4079
        have hw : |(-1581012769/10000000000 : ℝ)|=(1581012769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5150375443/10000000000 : ℝ)|^5103 ≤ (43601192692293/100000000000000 : ℝ)^4079
        have hw : |(5150375443/10000000000 : ℝ)|=(5150375443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_box_14 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5417508099/10000000000 : ℝ)*x 0 + (5150375749/10000000000 : ℝ)*x 1 + (-790506199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417508099/10000000000 : ℝ)^5103 ≤ (11612135907503/25000000000000 : ℝ)^4079 := by
    have hnat : (5417508099 : ℕ)^5103*25000000000000^4079 ≤ 11612135907503^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417508099 10000000000 11612135907503 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5150375749/10000000000 : ℝ)^5103 ≤ (43601195933097/100000000000000 : ℝ)^4079 := by
    have hnat : (5150375749 : ℕ)^5103*100000000000000^4079 ≤ 43601195933097^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150375749 10000000000 43601195933097 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (790506199/5000000000 : ℝ)^5103 ≤ (1990052084833/20000000000000 : ℝ)^4079 := by
    have hnat : (790506199 : ℕ)^5103*20000000000000^4079 ≤ 1990052084833^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      790506199 5000000000 1990052084833 20000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417508099/10000000000 : ℝ), (5150375749/10000000000 : ℝ), (-790506199/5000000000 : ℝ)] ![(11612135907503/25000000000000 : ℝ), (43601195933097/100000000000000 : ℝ), (1990052084833/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417508099/10000000000 : ℝ)|^5103 ≤ (11612135907503/25000000000000 : ℝ)^4079
        have hw : |(5417508099/10000000000 : ℝ)|=(5417508099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5150375749/10000000000 : ℝ)|^5103 ≤ (43601195933097/100000000000000 : ℝ)^4079
        have hw : |(5150375749/10000000000 : ℝ)|=(5150375749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-790506199/5000000000 : ℝ)|^5103 ≤ (1990052084833/20000000000000 : ℝ)^4079
        have hw : |(-790506199/5000000000 : ℝ)|=(790506199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_box_15 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (365796769/1000000000 : ℝ)*x 0 + (1099653847/2500000000 : ℝ)*x 1 + (879723033/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (365796769/1000000000 : ℝ)^5103 ≤ (28418081890841/100000000000000 : ℝ)^4079 := by
    have hnat : (365796769 : ℕ)^5103*100000000000000^4079 ≤ 28418081890841^4079*1000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365796769 1000000000 28418081890841 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099653847/2500000000 : ℝ)^5103 ≤ (35790960182593/100000000000000 : ℝ)^4079 := by
    have hnat : (1099653847 : ℕ)^5103*100000000000000^4079 ≤ 35790960182593^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099653847 2500000000 35790960182593 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (879723033/2000000000 : ℝ)^5103 ≤ (715819158251/2000000000000 : ℝ)^4079 := by
    have hnat : (879723033 : ℕ)^5103*2000000000000^4079 ≤ 715819158251^4079*2000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879723033 2000000000 715819158251 2000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(365796769/1000000000 : ℝ), (1099653847/2500000000 : ℝ), (879723033/2000000000 : ℝ)] ![(28418081890841/100000000000000 : ℝ), (35790960182593/100000000000000 : ℝ), (715819158251/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(365796769/1000000000 : ℝ)|^5103 ≤ (28418081890841/100000000000000 : ℝ)^4079
        have hw : |(365796769/1000000000 : ℝ)|=(365796769/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1099653847/2500000000 : ℝ)|^5103 ≤ (35790960182593/100000000000000 : ℝ)^4079
        have hw : |(1099653847/2500000000 : ℝ)|=(1099653847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(879723033/2000000000 : ℝ)|^5103 ≤ (715819158251/2000000000000 : ℝ)^4079
        have hw : |(879723033/2000000000 : ℝ)|=(879723033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1685_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186723319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1727/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (489/5000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66533/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(57811/100000 : ℝ) ∧ (80627/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (90057/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1727/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (489/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1727/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (489/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1727/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (489/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1727/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (489/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1727/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (489/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1727/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (489/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (489/5000 : ℝ) ^ (5095/1024 : ℝ) ≤ (946987407937009/100000000000000000000 : ℝ) := by
    have hpowers : (489/5000 : ℝ)^5095 ≤ (946987407937009/100000000000000000000 : ℝ)^1024 := by
      have hnat : (489 : ℕ)^5095*100000000000000000000^1024 ≤ 946987407937009^1024*5000^5095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        489 5000 946987407937009 100000000000000000000 5095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (489/5000 : ℝ)) (X := (946987407937009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1727/10000 : ℝ) ^ (5095/1024 : ℝ) ≤ (1603549904902923/10000000000000000000 : ℝ) := by
    have hpowers : (1727/10000 : ℝ)^5095 ≤ (1603549904902923/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1727 : ℕ)^5095*10000000000000000000^1024 ≤ 1603549904902923^1024*10000^5095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1727 10000 1603549904902923 10000000000000000000 5095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1727/10000 : ℝ)) (X := (1603549904902923/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000946987407937009/50000000000000000000 : ℝ) ≤ (10000038065074323/10000000000000000 : ℝ) ^ (5095/1024 : ℝ) := by
    have hpowers : (50000946987407937009/50000000000000000000 : ℝ)^1024 ≤ (10000038065074323/10000000000000000 : ℝ)^5095 := by
      have hnat : (50000946987407937009 : ℕ)^1024*10000000000000000^5095 ≤ 10000038065074323^5095*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000946987407937009 50000000000000000000 10000038065074323 10000000000000000 1024 5095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000038065074323/10000000000000000 : ℝ)) (X := (50000946987407937009/50000000000000000000 : ℝ)) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100016982486456966239/100000000000000000000 : ℝ) ≤ (10000341293157899/10000000000000000 : ℝ) ^ (5095/1024 : ℝ) := by
    have hpowers : (100016982486456966239/100000000000000000000 : ℝ)^1024 ≤ (10000341293157899/10000000000000000 : ℝ)^5095 := by
      have hnat : (100016982486456966239 : ℕ)^1024*10000000000000000^5095 ≤ 10000341293157899^5095*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100016982486456966239 100000000000000000000 10000341293157899 10000000000000000 1024 5095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000341293157899/10000000000000000 : ℝ)) (X := (100016982486456966239/100000000000000000000 : ℝ)) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5001603549904902923/5000000000000000000 : ℝ) ≤ (400025780849659/400000000000000 : ℝ) ^ (5095/1024 : ℝ) := by
    have hpowers : (5001603549904902923/5000000000000000000 : ℝ)^1024 ≤ (400025780849659/400000000000000 : ℝ)^5095 := by
      have hnat : (5001603549904902923 : ℕ)^1024*400000000000000^5095 ≤ 400025780849659^5095*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001603549904902923 5000000000000000000 400025780849659 400000000000000 1024 5095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400025780849659/400000000000000 : ℝ)) (X := (5001603549904902923/5000000000000000000 : ℝ)) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(946987407937009/100000000000000000000 : ℝ) ≤ ((7489435396609193271/7490000000000000000 : ℝ)+2*(37903510447/93625000000000 : ℝ)*(489/5000 : ℝ))^(5095/1024 : ℝ) := by
    rw [show (7489435396609193271/7490000000000000000 : ℝ)+2*(37903510447/93625000000000 : ℝ)*(489/5000 : ℝ)=(10000038065074323/10000000000000000 : ℝ) by norm_num, show 1+2*(946987407937009/100000000000000000000 : ℝ)=(50000946987407937009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1603549904902923/10000000000000000000 : ℝ)+(946987407937009/100000000000000000000 : ℝ) ≤ ((7489435396609193271/7490000000000000000 : ℝ)+(37903510447/93625000000000 : ℝ)*((1727/10000 : ℝ)+(489/5000 : ℝ)))^(5095/1024 : ℝ) := by
    rw [show (7489435396609193271/7490000000000000000 : ℝ)+(37903510447/93625000000000 : ℝ)*((1727/10000 : ℝ)+(489/5000 : ℝ))=(10000341293157899/10000000000000000 : ℝ) by norm_num, show 1+(1603549904902923/10000000000000000000 : ℝ)+(946987407937009/100000000000000000000 : ℝ)=(100016982486456966239/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1603549904902923/10000000000000000000 : ℝ) ≤ ((7489435396609193271/7490000000000000000 : ℝ)+2*(37903510447/93625000000000 : ℝ)*(1727/10000 : ℝ))^(5095/1024 : ℝ) := by
    rw [show (7489435396609193271/7490000000000000000 : ℝ)+2*(37903510447/93625000000000 : ℝ)*(1727/10000 : ℝ)=(400025780849659/400000000000000 : ℝ) by norm_num, show 1+2*(1603549904902923/10000000000000000000 : ℝ)=(5001603549904902923/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7489435396609193271/7490000000000000000 : ℝ)*(X 1 0+X 2 0)+(37903510447/93625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5095/1024 : ℝ)) (lo := (489/5000 : ℝ)) (hi := (1727/10000 : ℝ)) (c := (7489435396609193271/7490000000000000000 : ℝ)) (alpha := (37903510447/93625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7489435396609193271/7490000000000000000 : ℝ)*(X 0 1+X 2 1)+(37903510447/93625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5095/1024 : ℝ)) (lo := (489/5000 : ℝ)) (hi := (1727/10000 : ℝ)) (c := (7489435396609193271/7490000000000000000 : ℝ)) (alpha := (37903510447/93625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7489435396609193271/7490000000000000000 : ℝ)*(X 0 2+X 1 2)+(37903510447/93625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5095/1024 : ℝ)) (lo := (489/5000 : ℝ)) (hi := (1727/10000 : ℝ)) (c := (7489435396609193271/7490000000000000000 : ℝ)) (alpha := (37903510447/93625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-292121441/2500000000 : ℝ)*X 0 0+(1357714601/2500000000 : ℝ)*X 0 1+(5430857093/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((653261169/1250000000 : ℝ)*X 1 0+(-729797961/5000000000 : ℝ)*X 1 1+(33942861/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5226089481/10000000000 : ℝ)*X 2 0+(1357714469/2500000000 : ℝ)*X 2 1+(-729797791/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4523188921/10000000000 : ℝ)*X 0 0+(3968554959/10000000000 : ℝ)*X 0 1+(3968555007/10000000000 : ℝ)*X 0 2+(4523188921/10000000000 : ℝ)*X 1 0+(3968554959/10000000000 : ℝ)*X 1 1+(3968555007/10000000000 : ℝ)*X 1 2+(4523188921/10000000000 : ℝ)*X 2 0+(3968554959/10000000000 : ℝ)*X 2 1+(3968555007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-934081513/5000000000 : ℝ)*X 0 0+(1035143239/2000000000 : ℝ)*X 0 1+(646964407/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((540018993/1000000000 : ℝ)*X 1 0+(-196310067/1250000000 : ℝ)*X 1 1+(646964453/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5400190201/10000000000 : ℝ)*X 2 0+(5175715541/10000000000 : ℝ)*X 2 1+(-1570480279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((934711881/2500000000 : ℝ)*X 0 0+(4359855063/10000000000 : ℝ)*X 0 1+(272490937/625000000 : ℝ)*X 0 2+(934711881/2500000000 : ℝ)*X 1 0+(4359855063/10000000000 : ℝ)*X 1 1+(272490937/625000000 : ℝ)*X 1 2+(934711881/2500000000 : ℝ)*X 2 0+(4359855063/10000000000 : ℝ)*X 2 1+(272490937/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-859069189/5000000000 : ℝ)*X 0 0+(38974719/78125000 : ℝ)*X 0 1+(5474641783/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2598110297/5000000000 : ℝ)*X 1 0+(-287943519/2000000000 : ℝ)*X 1 1+(5474642821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2598110377/5000000000 : ℝ)*X 2 0+(342165187/625000000 : ℝ)*X 2 1+(-89982321/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4652748679/10000000000 : ℝ)*X 0 0+(3901230721/10000000000 : ℝ)*X 0 1+(3901228179/10000000000 : ℝ)*X 0 2+(4652748679/10000000000 : ℝ)*X 1 0+(3901230721/10000000000 : ℝ)*X 1 1+(3901228179/10000000000 : ℝ)*X 1 2+(4652748679/10000000000 : ℝ)*X 2 0+(3901230721/10000000000 : ℝ)*X 2 1+(3901228179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1313880599/10000000000 : ℝ)*X 0 0+(5608411333/10000000000 : ℝ)*X 0 1+(643796943/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5417508129/10000000000 : ℝ)*X 1 0+(-1581012769/10000000000 : ℝ)*X 1 1+(5150375443/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5417508099/10000000000 : ℝ)*X 2 0+(5150375749/10000000000 : ℝ)*X 2 1+(-790506199/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((365796769/1000000000 : ℝ)*X 0 0+(1099653847/2500000000 : ℝ)*X 0 1+(879723033/2000000000 : ℝ)*X 0 2+(365796769/1000000000 : ℝ)*X 1 0+(1099653847/2500000000 : ℝ)*X 1 1+(879723033/2000000000 : ℝ)*X 1 2+(365796769/1000000000 : ℝ)*X 2 0+(1099653847/2500000000 : ℝ)*X 2 1+(879723033/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66533/100000 : ℝ) ≤ (-6228952860710024434939561329429/9362500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1767919/20000000000000 : ℝ)*(upper1) + (2520819/50000000000000 : ℝ)*(lower2) + (45392337/100000000000000 : ℝ)*(upper4) + (54077361/100000000000000 : ℝ)*(upper5) + (64630437763733/5000000000000 : ℝ)*(major0) + (64630437763733/5000000000000 : ℝ)*(major1) + (64630437763733/5000000000000 : ℝ)*(major2) + (615238097/20000000000000 : ℝ)*(sp1) + (1580201771/50000000000000 : ℝ)*(sp2) + (478782577400267/25000000000000 : ℝ)*(sp4) + (957566256202811/50000000000000 : ℝ)*(sp5) + (478783107048141/25000000000000 : ℝ)*(sp6) + (138451775835739/20000000000000 : ℝ)*(sp7) + (2639497519/50000000000000 : ℝ)*(sp8) + (138451775835739/20000000000000 : ℝ)*(f.failure) + (1915135588596107/100000000000000 : ℝ)*(f.sum) + (1182561084207/468125000000000000000000000 : ℝ)*base65 + (26723378749070643/37450000000000000000000000000000 : ℝ)*base67 + (211857103928620643/37450000000000000000000000000000 : ℝ)*base69 + (258462065091520643/37450000000000000000000000000000 : ℝ)*base71 + (8294879051719/3745000000000000000000000000 : ℝ)*base74 + (166585840518079357/37450000000000000000000000000000 : ℝ)*base76 + (317138542110820643/37450000000000000000000000000000 : ℝ)*base77 + (209229795471070643/37450000000000000000000000000000 : ℝ)*base79 + (249604975131/58515625000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (15102259/2000000000000000000000 : ℝ)*base90 + (15102259/2000000000000000000000 : ℝ)*base92 + (15102259/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (57811/100000 : ℝ) ≤ (21651029494992932033506917317127/37450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33104699/50000000000000 : ℝ)*(lower1) + (88360187/100000000000000 : ℝ)*(lower2) + (4222263/12500000000000 : ℝ)*(lower5) + (139021828056379/10000000000000 : ℝ)*(major0) + (139021828056379/10000000000000 : ℝ)*(major1) + (139021828056379/10000000000000 : ℝ)*(major2) + (2016626893309479/100000000000000 : ℝ)*(sp0) + (252078727434161/12500000000000 : ℝ)*(sp1) + (403325247693001/20000000000000 : ℝ)*(sp2) + (93066436955411/12500000000000 : ℝ)*(sp3) + (185623413/10000000000000 : ℝ)*(sp5) + (1359310603/25000000000000 : ℝ)*(sp6) + (291935839/12500000000000 : ℝ)*(sp7) + (2391198969/50000000000000 : ℝ)*(sp8) + (74453383113/10000000000 : ℝ)*(f.failure) + (2016631675707417/100000000000000 : ℝ)*(f.sum) + (74086577497/29257812500000000000000000 : ℝ)*base66 + (264846876466465709/74900000000000000000000000000000 : ℝ)*base67 + (197366396934434291/74900000000000000000000000000000 : ℝ)*base70 + (449848027130334291/74900000000000000000000000000000 : ℝ)*base72 + (1973910328183/468125000000000000000000000 : ℝ)*base73 + (280612803459534291/74900000000000000000000000000000 : ℝ)*base76 + (56441540011234291/74900000000000000000000000000000 : ℝ)*base78 + (16030818640465709/74900000000000000000000000000000 : ℝ)*base79 + (1092256879443/1872500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (12047/1000000000000000000 : ℝ)*base89 + (12047/1000000000000000000 : ℝ)*base91 + (12047/1000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80627/100000 : ℝ) ≤ (4718065287216877071057846921297/5851562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (210303/625000000000 : ℝ)*(upper1) + (36358153/25000000000000 : ℝ)*(upper3) + (21024843/12500000000000 : ℝ)*(upper4) + (10298887/100000000000000 : ℝ)*(lower5) + (22246092725453/1562500000000 : ℝ)*(major0) + (22246092725453/1562500000000 : ℝ)*(major1) + (22246092725453/1562500000000 : ℝ)*(major2) + (11630672327/50000000000000 : ℝ)*(sp1) + (68549082707/100000000000000 : ℝ)*(sp2) + (1888210059/20000000000000 : ℝ)*(sp3) + (514532929374359/25000000000000 : ℝ)*(sp8) + (1029054228076391/50000000000000 : ℝ)*(sp9) + (205806316841473/10000000000000 : ℝ)*(sp10) + (190620581485397/25000000000000 : ℝ)*(sp11) + (190622941747971/25000000000000 : ℝ)*(f.failure) + (514532929374359/25000000000000 : ℝ)*(f.sum) + (27721228989921/18725000000000000000000000000 : ℝ)*base65 + (15117869184083069/5851562500000000000000000000000 : ℝ)*base67 + (51977774800489319/5851562500000000000000000000000 : ℝ)*base69 + (8601958130704361/1462890625000000000000000000000 : ℝ)*base71 + (14251653124179/18725000000000000000000000000 : ℝ)*base74 + (2158619506393097/2925781250000000000000000000000 : ℝ)*base75 + (30819190303775513/11703125000000000000000000000000 : ℝ)*base77 + (16839857413260681/5851562500000000000000000000000 : ℝ)*base80 + (90458358299479/18725000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (6635749/2500000000000000000000 : ℝ)*base89 + (6635749/2500000000000000000000 : ℝ)*base91 + (6635749/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-90057/100000 : ℝ) ≤ (-24089564016545452208126521321851/26750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1540027/4000000000000 : ℝ)*(lower0) + (14147507/25000000000000 : ℝ)*(lower1) + (68018069/100000000000000 : ℝ)*(lower2) + (1470328054169289/100000000000000 : ℝ)*(major0) + (1470328054169289/100000000000000 : ℝ)*(major1) + (1470328054169289/100000000000000 : ℝ)*(major2) + (502693981/20000000000000 : ℝ)*(sp0) + (11770943521/20000000000000 : ℝ)*(sp5) + (493672597/3125000000000 : ℝ)*(sp6) + (6716644613/100000000000000 : ℝ)*(sp7) + (1091617491354651/50000000000000 : ℝ)*(sp12) + (1091589320730801/50000000000000 : ℝ)*(sp13) + (272902712332013/12500000000000 : ℝ)*(sp14) + (787430043821973/100000000000000 : ℝ)*(sp15) + (393718380233293/50000000000000 : ℝ)*(f.failure) + (272904687022401/12500000000000 : ℝ)*(f.sum) + (709415028381/668750000000000000000000000 : ℝ)*base66 + (425244006272470617/107000000000000000000000000000000 : ℝ)*base67 + (403236485417470617/107000000000000000000000000000000 : ℝ)*base69 + (980528685245470617/107000000000000000000000000000000 : ℝ)*base71 + (12083363356699/2675000000000000000000000000 : ℝ)*base74 + (683447683846470617/107000000000000000000000000000000 : ℝ)*base75 + (88511426801470617/107000000000000000000000000000000 : ℝ)*base77 + (372989900945529383/107000000000000000000000000000000 : ℝ)*base80 + (4376477855599/2675000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (13259467/5000000000000000000000 : ℝ)*base89 + (13259467/5000000000000000000000 : ℝ)*base91 + (13259467/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1685_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186723319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1727/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (489/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66533/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57811/100000 : ℝ) else (80627/100000 : ℝ) ≤ X j i ∧ X j i ≤ (90057/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1685_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1685_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186723319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8649/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2439/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66533/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57811/100000 : ℝ) else (80627/100000 : ℝ) ≤ X j i ∧ X j i ≤ (90057/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1685_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1685_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1685_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186723319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8649/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2439/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66533/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57811/100000 : ℝ) else (80627/100000 : ℝ) ≤ X j i ∧ X j i ≤ (90057/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1685_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

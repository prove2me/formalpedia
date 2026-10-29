-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1460_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:07:52.516019+00:00
-- url     : https://prove2.me/submissions/b137c191-1601-48a8-b409-7018a73832e2

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
theorem support_rectangle_w1460_s6_0 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-194625337/1000000000 : ℝ)*x 0 + (5406622481/10000000000 : ℝ)*x 1 + (5247556107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (194625337/1000000000 : ℝ)^1105 ≤ (11881487174709/100000000000000 : ℝ)^849 := by
    have hnat : (194625337 : ℕ)^1105*100000000000000^849 ≤ 11881487174709^849*1000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194625337 1000000000 11881487174709 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406622481/10000000000 : ℝ)^1105 ≤ (44915362851057/100000000000000 : ℝ)^849 := by
    have hnat : (5406622481 : ℕ)^1105*100000000000000^849 ≤ 44915362851057^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406622481 10000000000 44915362851057 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247556107/10000000000 : ℝ)^1105 ≤ (43203149963519/100000000000000 : ℝ)^849 := by
    have hnat : (5247556107 : ℕ)^1105*100000000000000^849 ≤ 43203149963519^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247556107 10000000000 43203149963519 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-194625337/1000000000 : ℝ), (5406622481/10000000000 : ℝ), (5247556107/10000000000 : ℝ)] ![(11881487174709/100000000000000 : ℝ), (44915362851057/100000000000000 : ℝ), (43203149963519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-194625337/1000000000 : ℝ)|^1105 ≤ (11881487174709/100000000000000 : ℝ)^849
        have hw : |(-194625337/1000000000 : ℝ)|=(194625337/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406622481/10000000000 : ℝ)|^1105 ≤ (44915362851057/100000000000000 : ℝ)^849
        have hw : |(5406622481/10000000000 : ℝ)|=(5406622481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247556107/10000000000 : ℝ)|^1105 ≤ (43203149963519/100000000000000 : ℝ)^849
        have hw : |(5247556107/10000000000 : ℝ)|=(5247556107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s6_1 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336664113/2500000000 : ℝ)*x 0 + (-506803993/2500000000 : ℝ)*x 1 + (2623778057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336664113/2500000000 : ℝ)^1105 ≤ (11067017789497/25000000000000 : ℝ)^849 := by
    have hnat : (1336664113 : ℕ)^1105*25000000000000^849 ≤ 11067017789497^849*2500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336664113 2500000000 11067017789497 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506803993/2500000000 : ℝ)^1105 ≤ (12528778786407/100000000000000 : ℝ)^849 := by
    have hnat : (506803993 : ℕ)^1105*100000000000000^849 ≤ 12528778786407^849*2500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506803993 2500000000 12528778786407 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623778057/5000000000 : ℝ)^1105 ≤ (84381152419/195312500000 : ℝ)^849 := by
    have hnat : (2623778057 : ℕ)^1105*195312500000^849 ≤ 84381152419^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623778057 5000000000 84381152419 195312500000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336664113/2500000000 : ℝ), (-506803993/2500000000 : ℝ), (2623778057/5000000000 : ℝ)] ![(11067017789497/25000000000000 : ℝ), (12528778786407/100000000000000 : ℝ), (84381152419/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336664113/2500000000 : ℝ)|^1105 ≤ (11067017789497/25000000000000 : ℝ)^849
        have hw : |(1336664113/2500000000 : ℝ)|=(1336664113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-506803993/2500000000 : ℝ)|^1105 ≤ (12528778786407/100000000000000 : ℝ)^849
        have hw : |(-506803993/2500000000 : ℝ)|=(506803993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623778057/5000000000 : ℝ)|^1105 ≤ (84381152419/195312500000 : ℝ)^849
        have hw : |(2623778057/5000000000 : ℝ)|=(2623778057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s6_2 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5346656463/10000000000 : ℝ)*x 0 + (5247556097/10000000000 : ℝ)*x 1 + (-101360799/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346656463/10000000000 : ℝ)^1105 ≤ (1770722851061/4000000000000 : ℝ)^849 := by
    have hnat : (5346656463 : ℕ)^1105*4000000000000^849 ≤ 1770722851061^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346656463 10000000000 1770722851061 4000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247556097/10000000000 : ℝ)^1105 ≤ (10800787464091/25000000000000 : ℝ)^849 := by
    have hnat : (5247556097 : ℕ)^1105*25000000000000^849 ≤ 10800787464091^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247556097 10000000000 10800787464091 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101360799/500000000 : ℝ)^1105 ≤ (6264389425379/50000000000000 : ℝ)^849 := by
    have hnat : (101360799 : ℕ)^1105*50000000000000^849 ≤ 6264389425379^849*500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101360799 500000000 6264389425379 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346656463/10000000000 : ℝ), (5247556097/10000000000 : ℝ), (-101360799/500000000 : ℝ)] ![(1770722851061/4000000000000 : ℝ), (10800787464091/25000000000000 : ℝ), (6264389425379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346656463/10000000000 : ℝ)|^1105 ≤ (1770722851061/4000000000000 : ℝ)^849
        have hw : |(5346656463/10000000000 : ℝ)|=(5346656463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247556097/10000000000 : ℝ)|^1105 ≤ (10800787464091/25000000000000 : ℝ)^849
        have hw : |(5247556097/10000000000 : ℝ)|=(5247556097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-101360799/500000000 : ℝ)|^1105 ≤ (6264389425379/50000000000000 : ℝ)^849
        have hw : |(-101360799/500000000 : ℝ)|=(101360799/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s6_3 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1074170507/2500000000 : ℝ)*x 0 + (1031449121/2500000000 : ℝ)*x 1 + (2236911261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074170507/2500000000 : ℝ)^1105 ≤ (16652576329223/50000000000000 : ℝ)^849 := by
    have hnat : (1074170507 : ℕ)^1105*50000000000000^849 ≤ 16652576329223^849*2500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074170507 2500000000 16652576329223 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031449121/2500000000 : ℝ)^1105 ≤ (31591584027247/100000000000000 : ℝ)^849 := by
    have hnat : (1031449121 : ℕ)^1105*100000000000000^849 ≤ 31591584027247^849*2500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031449121 2500000000 31591584027247 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2236911261/5000000000 : ℝ)^1105 ≤ (35103263303339/100000000000000 : ℝ)^849 := by
    have hnat : (2236911261 : ℕ)^1105*100000000000000^849 ≤ 35103263303339^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236911261 5000000000 35103263303339 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074170507/2500000000 : ℝ), (1031449121/2500000000 : ℝ), (2236911261/5000000000 : ℝ)] ![(16652576329223/50000000000000 : ℝ), (31591584027247/100000000000000 : ℝ), (35103263303339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074170507/2500000000 : ℝ)|^1105 ≤ (16652576329223/50000000000000 : ℝ)^849
        have hw : |(1074170507/2500000000 : ℝ)|=(1074170507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031449121/2500000000 : ℝ)|^1105 ≤ (31591584027247/100000000000000 : ℝ)^849
        have hw : |(1031449121/2500000000 : ℝ)|=(1031449121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2236911261/5000000000 : ℝ)|^1105 ≤ (35103263303339/100000000000000 : ℝ)^849
        have hw : |(2236911261/5000000000 : ℝ)|=(2236911261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s6_4 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1946264391/10000000000 : ℝ)*x 0 + (1312032867/2500000000 : ℝ)*x 1 + (5406044159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1946264391/10000000000 : ℝ)^1105 ≤ (185649605361/1562500000000 : ℝ)^849 := by
    have hnat : (1946264391 : ℕ)^1105*1562500000000^849 ≤ 185649605361^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946264391 10000000000 185649605361 1562500000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1312032867/2500000000 : ℝ)^1105 ≤ (8641863070577/20000000000000 : ℝ)^849 := by
    have hnat : (1312032867 : ℕ)^1105*20000000000000^849 ≤ 8641863070577^849*2500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312032867 2500000000 8641863070577 20000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406044159/10000000000 : ℝ)^1105 ≤ (44909109883663/100000000000000 : ℝ)^849 := by
    have hnat : (5406044159 : ℕ)^1105*100000000000000^849 ≤ 44909109883663^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406044159 10000000000 44909109883663 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1946264391/10000000000 : ℝ), (1312032867/2500000000 : ℝ), (5406044159/10000000000 : ℝ)] ![(185649605361/1562500000000 : ℝ), (8641863070577/20000000000000 : ℝ), (44909109883663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1946264391/10000000000 : ℝ)|^1105 ≤ (185649605361/1562500000000 : ℝ)^849
        have hw : |(-1946264391/10000000000 : ℝ)|=(1946264391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1312032867/2500000000 : ℝ)|^1105 ≤ (8641863070577/20000000000000 : ℝ)^849
        have hw : |(1312032867/2500000000 : ℝ)|=(1312032867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406044159/10000000000 : ℝ)|^1105 ≤ (44909109883663/100000000000000 : ℝ)^849
        have hw : |(5406044159/10000000000 : ℝ)|=(5406044159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s6_5 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1061036349/2000000000 : ℝ)*x 0 + (-93436389/500000000 : ℝ)*x 1 + (5406043901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061036349/2000000000 : ℝ)^1105 ≤ (2738853617441/6250000000000 : ℝ)^849 := by
    have hnat : (1061036349 : ℕ)^1105*6250000000000^849 ≤ 2738853617441^849*2000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061036349 2000000000 2738853617441 6250000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93436389/500000000 : ℝ)^1105 ≤ (2817308753437/25000000000000 : ℝ)^849 := by
    have hnat : (93436389 : ℕ)^1105*25000000000000^849 ≤ 2817308753437^849*500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93436389 500000000 2817308753437 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406043901/10000000000 : ℝ)^1105 ≤ (22454553547073/50000000000000 : ℝ)^849 := by
    have hnat : (5406043901 : ℕ)^1105*50000000000000^849 ≤ 22454553547073^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406043901 10000000000 22454553547073 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061036349/2000000000 : ℝ), (-93436389/500000000 : ℝ), (5406043901/10000000000 : ℝ)] ![(2738853617441/6250000000000 : ℝ), (2817308753437/25000000000000 : ℝ), (22454553547073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061036349/2000000000 : ℝ)|^1105 ≤ (2738853617441/6250000000000 : ℝ)^849
        have hw : |(1061036349/2000000000 : ℝ)|=(1061036349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-93436389/500000000 : ℝ)|^1105 ≤ (2817308753437/25000000000000 : ℝ)^849
        have hw : |(-93436389/500000000 : ℝ)|=(93436389/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406043901/10000000000 : ℝ)|^1105 ≤ (22454553547073/50000000000000 : ℝ)^849
        have hw : |(5406043901/10000000000 : ℝ)|=(5406043901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s6_6 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652590641/5000000000 : ℝ)*x 0 + (5406044053/10000000000 : ℝ)*x 1 + (-467182051/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652590641/5000000000 : ℝ)^1105 ≤ (43821652901409/100000000000000 : ℝ)^849 := by
    have hnat : (2652590641 : ℕ)^1105*100000000000000^849 ≤ 43821652901409^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652590641 5000000000 43821652901409 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406044053/10000000000 : ℝ)^1105 ≤ (22454554368791/50000000000000 : ℝ)^849 := by
    have hnat : (5406044053 : ℕ)^1105*50000000000000^849 ≤ 22454554368791^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406044053 10000000000 22454554368791 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467182051/2500000000 : ℝ)^1105 ≤ (11269238341637/100000000000000 : ℝ)^849 := by
    have hnat : (467182051 : ℕ)^1105*100000000000000^849 ≤ 11269238341637^849*2500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467182051 2500000000 11269238341637 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652590641/5000000000 : ℝ), (5406044053/10000000000 : ℝ), (-467182051/2500000000 : ℝ)] ![(43821652901409/100000000000000 : ℝ), (22454554368791/50000000000000 : ℝ), (11269238341637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652590641/5000000000 : ℝ)|^1105 ≤ (43821652901409/100000000000000 : ℝ)^849
        have hw : |(2652590641/5000000000 : ℝ)|=(2652590641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406044053/10000000000 : ℝ)|^1105 ≤ (22454554368791/50000000000000 : ℝ)^849
        have hw : |(5406044053/10000000000 : ℝ)|=(5406044053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-467182051/2500000000 : ℝ)|^1105 ≤ (11269238341637/100000000000000 : ℝ)^849
        have hw : |(-467182051/2500000000 : ℝ)|=(467182051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s6_7 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4296705973/10000000000 : ℝ)*x 0 + (894512829/2000000000 : ℝ)*x 1 + (2063530807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4296705973/10000000000 : ℝ)^1105 ≤ (520396784863/1562500000000 : ℝ)^849 := by
    have hnat : (4296705973 : ℕ)^1105*1562500000000^849 ≤ 520396784863^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296705973 10000000000 520396784863 1562500000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (894512829/2000000000 : ℝ)^1105 ≤ (35090412931897/100000000000000 : ℝ)^849 := by
    have hnat : (894512829 : ℕ)^1105*100000000000000^849 ≤ 35090412931897^849*2000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894512829 2000000000 35090412931897 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063530807/5000000000 : ℝ)^1105 ≤ (6320838563491/20000000000000 : ℝ)^849 := by
    have hnat : (2063530807 : ℕ)^1105*20000000000000^849 ≤ 6320838563491^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063530807 5000000000 6320838563491 20000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4296705973/10000000000 : ℝ), (894512829/2000000000 : ℝ), (2063530807/5000000000 : ℝ)] ![(520396784863/1562500000000 : ℝ), (35090412931897/100000000000000 : ℝ), (6320838563491/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4296705973/10000000000 : ℝ)|^1105 ≤ (520396784863/1562500000000 : ℝ)^849
        have hw : |(4296705973/10000000000 : ℝ)|=(4296705973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(894512829/2000000000 : ℝ)|^1105 ≤ (35090412931897/100000000000000 : ℝ)^849
        have hw : |(894512829/2000000000 : ℝ)|=(894512829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2063530807/5000000000 : ℝ)|^1105 ≤ (6320838563491/20000000000000 : ℝ)^849
        have hw : |(2063530807/5000000000 : ℝ)|=(2063530807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1460_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (591/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5701/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3693/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (591/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (591/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (591/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (591/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (591/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (591/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11399/100000 : ℝ) ^ (4419/1024 : ℝ) ≤ (1702177263179421/20000000000000000000 : ℝ) := by
    have hpowers : (11399/100000 : ℝ)^4419 ≤ (1702177263179421/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11399 : ℕ)^4419*20000000000000000000^1024 ≤ 1702177263179421^1024*100000^4419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11399 100000 1702177263179421 20000000000000000000 4419 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11399/100000 : ℝ)) (X := (1702177263179421/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (591/4000 : ℝ) ^ (4419/1024 : ℝ) ≤ (13035397471979811/50000000000000000000 : ℝ) := by
    have hpowers : (591/4000 : ℝ)^4419 ≤ (13035397471979811/50000000000000000000 : ℝ)^1024 := by
      have hnat : (591 : ℕ)^4419*50000000000000000000^1024 ≤ 13035397471979811^1024*4000^4419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        591 4000 13035397471979811 50000000000000000000 4419 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (591/4000 : ℝ)) (X := (13035397471979811/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001702177263179421/10000000000000000000 : ℝ) ≤ (10000394414020747/10000000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (10001702177263179421/10000000000000000000 : ℝ)^1024 ≤ (10000394414020747/10000000000000000 : ℝ)^4419 := by
      have hnat : (10001702177263179421 : ℕ)^1024*10000000000000000^4419 ≤ 10000394414020747^4419*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001702177263179421 10000000000000000000 10000394414020747 10000000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000394414020747/10000000000000000 : ℝ)) (X := (10001702177263179421/10000000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034581681259856727/100000000000000000000 : ℝ) ≤ (10000801243232713/10000000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (100034581681259856727/100000000000000000000 : ℝ)^1024 ≤ (10000801243232713/10000000000000000 : ℝ)^4419 := by
      have hnat : (100034581681259856727 : ℕ)^1024*10000000000000000^4419 ≤ 10000801243232713^4419*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034581681259856727 100000000000000000000 10000801243232713 10000000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000801243232713/10000000000000000 : ℝ)) (X := (100034581681259856727/100000000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013035397471979811/25000000000000000000 : ℝ) ≤ (10001208072444679/10000000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (25013035397471979811/25000000000000000000 : ℝ)^1024 ≤ (10001208072444679/10000000000000000 : ℝ)^4419 := by
      have hnat : (25013035397471979811 : ℕ)^1024*10000000000000000^4419 ≤ 10001208072444679^4419*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013035397471979811 25000000000000000000 10001208072444679 10000000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001208072444679/10000000000000000 : ℝ)) (X := (25013035397471979811/25000000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1702177263179421/20000000000000000000 : ℝ) ≤ ((8438014162339910251/8440000000000000000 : ℝ)+2*(203414605983/168800000000000 : ℝ)*(11399/100000 : ℝ))^(4419/1024 : ℝ) := by
    rw [show (8438014162339910251/8440000000000000000 : ℝ)+2*(203414605983/168800000000000 : ℝ)*(11399/100000 : ℝ)=(10000394414020747/10000000000000000 : ℝ) by norm_num, show 1+2*(1702177263179421/20000000000000000000 : ℝ)=(10001702177263179421/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13035397471979811/50000000000000000000 : ℝ)+(1702177263179421/20000000000000000000 : ℝ) ≤ ((8438014162339910251/8440000000000000000 : ℝ)+(203414605983/168800000000000 : ℝ)*((591/4000 : ℝ)+(11399/100000 : ℝ)))^(4419/1024 : ℝ) := by
    rw [show (8438014162339910251/8440000000000000000 : ℝ)+(203414605983/168800000000000 : ℝ)*((591/4000 : ℝ)+(11399/100000 : ℝ))=(10000801243232713/10000000000000000 : ℝ) by norm_num, show 1+(13035397471979811/50000000000000000000 : ℝ)+(1702177263179421/20000000000000000000 : ℝ)=(100034581681259856727/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13035397471979811/50000000000000000000 : ℝ) ≤ ((8438014162339910251/8440000000000000000 : ℝ)+2*(203414605983/168800000000000 : ℝ)*(591/4000 : ℝ))^(4419/1024 : ℝ) := by
    rw [show (8438014162339910251/8440000000000000000 : ℝ)+2*(203414605983/168800000000000 : ℝ)*(591/4000 : ℝ)=(10001208072444679/10000000000000000 : ℝ) by norm_num, show 1+2*(13035397471979811/50000000000000000000 : ℝ)=(25013035397471979811/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8438014162339910251/8440000000000000000 : ℝ)*(X 1 0+X 2 0)+(203414605983/168800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (11399/100000 : ℝ)) (hi := (591/4000 : ℝ)) (c := (8438014162339910251/8440000000000000000 : ℝ)) (alpha := (203414605983/168800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8438014162339910251/8440000000000000000 : ℝ)*(X 0 1+X 2 1)+(203414605983/168800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (11399/100000 : ℝ)) (hi := (591/4000 : ℝ)) (c := (8438014162339910251/8440000000000000000 : ℝ)) (alpha := (203414605983/168800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8438014162339910251/8440000000000000000 : ℝ)*(X 0 2+X 1 2)+(203414605983/168800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (11399/100000 : ℝ)) (hi := (591/4000 : ℝ)) (c := (8438014162339910251/8440000000000000000 : ℝ)) (alpha := (203414605983/168800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-194625337/1000000000 : ℝ)*X 0 0+(5406622481/10000000000 : ℝ)*X 0 1+(5247556107/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336664113/2500000000 : ℝ)*X 1 0+(-506803993/2500000000 : ℝ)*X 1 1+(2623778057/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346656463/10000000000 : ℝ)*X 2 0+(5247556097/10000000000 : ℝ)*X 2 1+(-101360799/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1074170507/2500000000 : ℝ)*X 0 0+(1031449121/2500000000 : ℝ)*X 0 1+(2236911261/5000000000 : ℝ)*X 0 2+(1074170507/2500000000 : ℝ)*X 1 0+(1031449121/2500000000 : ℝ)*X 1 1+(2236911261/5000000000 : ℝ)*X 1 2+(1074170507/2500000000 : ℝ)*X 2 0+(1031449121/2500000000 : ℝ)*X 2 1+(2236911261/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1946264391/10000000000 : ℝ)*X 0 0+(1312032867/2500000000 : ℝ)*X 0 1+(5406044159/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061036349/2000000000 : ℝ)*X 1 0+(-93436389/500000000 : ℝ)*X 1 1+(5406043901/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652590641/5000000000 : ℝ)*X 2 0+(5406044053/10000000000 : ℝ)*X 2 1+(-467182051/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4296705973/10000000000 : ℝ)*X 0 0+(894512829/2000000000 : ℝ)*X 0 1+(2063530807/5000000000 : ℝ)*X 0 2+(4296705973/10000000000 : ℝ)*X 1 0+(894512829/2000000000 : ℝ)*X 1 1+(2063530807/5000000000 : ℝ)*X 1 2+(4296705973/10000000000 : ℝ)*X 2 0+(894512829/2000000000 : ℝ)*X 2 1+(2063530807/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54276264221520427779363/8440000000000000000000000000 : ℝ) := by norm_num
    linear_combination (561162417/50000000000000 : ℝ)*(base19) + (264511607/25000000000000 : ℝ)*(base23) + (2064143/5000000000000 : ℝ)*(lower2) + (19809561/12500000000000 : ℝ)*(upper3) + (11802877/12500000000000 : ℝ)*(upper5) + (4580051972981749/100000000000000 : ℝ)*(major0) + (4580051972981749/100000000000000 : ℝ)*(major1) + (4580051972981749/100000000000000 : ℝ)*(major2) + (785838626898399/12500000000000 : ℝ)*(sp0) + (1257346365088581/20000000000000 : ℝ)*(sp1) + (6286731889721311/100000000000000 : ℝ)*(sp2) + (1436679401149247/50000000000000 : ℝ)*(sp3) + (23932580547/100000000000000 : ℝ)*(sp4) + (11981536021/100000000000000 : ℝ)*(sp7) + (1436685391917257/50000000000000 : ℝ)*(f.failure) + (6286732947767739/100000000000000 : ℝ)*(f.sum) + (23957924932853/8440000000000000000000000000 : ℝ)*base66 + (6433059374981641001/844000000000000000000000000000000 : ℝ)*base68 + (7776165349741641001/844000000000000000000000000000000 : ℝ)*base70 + (4514959347434358999/844000000000000000000000000000000 : ℝ)*base71 + (22217623375373/8440000000000000000000000000 : ℝ)*base74 + (12600936283126358999/844000000000000000000000000000000 : ℝ)*base75 + (336222563982358999/844000000000000000000000000000000 : ℝ)*base77 + (2485727770217641001/844000000000000000000000000000000 : ℝ)*base80 + (49405787843813/8440000000000000000000000000 : ℝ)*base82 + (57192869/5000000000000000000000 : ℝ)*base90 + (57192869/5000000000000000000000 : ℝ)*base92 + (57192869/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (159234706995519317545326741/42200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1040926503/100000000000000 : ℝ)*(base19) + (401781633/100000000000000 : ℝ)*(base23) + (16643/125000000000 : ℝ)*(upper1) + (12321147/50000000000000 : ℝ)*(upper2) + (58648897/100000000000000 : ℝ)*(upper3) + (4613471510720029/100000000000000 : ℝ)*(major0) + (4613471510720029/100000000000000 : ℝ)*(major1) + (461347151072003/10000000000000 : ℝ)*(major2) + (8501643673/50000000000000 : ℝ)*(sp1) + (1804478269/100000000000000 : ℝ)*(sp3) + (1266521163253513/20000000000000 : ℝ)*(sp4) + (1583146943013429/25000000000000 : ℝ)*(sp5) + (1583151353621483/25000000000000 : ℝ)*(sp6) + (1447167637458203/50000000000000 : ℝ)*(sp7) + (115773483175787/4000000000000 : ℝ)*(f.failure) + (1266521163253513/20000000000000 : ℝ)*(f.sum) + (54727573896597/16880000000000000000000000000 : ℝ)*base65 + (11339033896961382721/844000000000000000000000000000000 : ℝ)*base68 + (468614976403537753/84400000000000000000000000000000 : ℝ)*base69 + (9249297405185382721/844000000000000000000000000000000 : ℝ)*base72 + (33173061592123/16880000000000000000000000000 : ℝ)*base74 + (191958804813537753/84400000000000000000000000000000 : ℝ)*base75 + (16807257478387467279/844000000000000000000000000000000 : ℝ)*base77 + (15189086604995467279/844000000000000000000000000000000 : ℝ)*base79 + (39866182208947/8440000000000000000000000000 : ℝ)*base81 + (2557121/400000000000000000000 : ℝ)*base89 + (2557121/400000000000000000000 : ℝ)*base91 + (1442879/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1460_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (591/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5701/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1460_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1460_box_0 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-893897939/5000000000 : ℝ)*x 0 + (1346231191/2500000000 : ℝ)*x 1 + (2692462059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (893897939/5000000000 : ℝ)^1105 ≤ (10638207338471/100000000000000 : ℝ)^849 := by
    have hnat : (893897939 : ℕ)^1105*100000000000000^849 ≤ 10638207338471^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893897939 5000000000 10638207338471 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346231191/2500000000 : ℝ)^1105 ≤ (44680899806579/100000000000000 : ℝ)^849 := by
    have hnat : (1346231191 : ℕ)^1105*100000000000000^849 ≤ 44680899806579^849*2500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346231191 2500000000 44680899806579 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692462059/5000000000 : ℝ)^1105 ≤ (44680892830211/100000000000000 : ℝ)^849 := by
    have hnat : (2692462059 : ℕ)^1105*100000000000000^849 ≤ 44680892830211^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692462059 5000000000 44680892830211 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-893897939/5000000000 : ℝ), (1346231191/2500000000 : ℝ), (2692462059/5000000000 : ℝ)] ![(10638207338471/100000000000000 : ℝ), (44680899806579/100000000000000 : ℝ), (44680892830211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-893897939/5000000000 : ℝ)|^1105 ≤ (10638207338471/100000000000000 : ℝ)^849
        have hw : |(-893897939/5000000000 : ℝ)|=(893897939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346231191/2500000000 : ℝ)|^1105 ≤ (44680899806579/100000000000000 : ℝ)^849
        have hw : |(1346231191/2500000000 : ℝ)|=(1346231191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692462059/5000000000 : ℝ)|^1105 ≤ (44680892830211/100000000000000 : ℝ)^849
        have hw : |(2692462059/5000000000 : ℝ)|=(2692462059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_box_1 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1321562961/2500000000 : ℝ)*x 0 + (-1923479379/10000000000 : ℝ)*x 1 + (2692461959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321562961/2500000000 : ℝ)^1105 ≤ (21809127387267/50000000000000 : ℝ)^849 := by
    have hnat : (1321562961 : ℕ)^1105*50000000000000^849 ≤ 21809127387267^849*2500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321562961 2500000000 21809127387267 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1923479379/10000000000 : ℝ)^1105 ≤ (1462606817937/12500000000000 : ℝ)^849 := by
    have hnat : (1923479379 : ℕ)^1105*12500000000000^849 ≤ 1462606817937^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923479379 10000000000 1462606817937 12500000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692461959/5000000000 : ℝ)^1105 ≤ (8936178134069/20000000000000 : ℝ)^849 := by
    have hnat : (2692461959 : ℕ)^1105*20000000000000^849 ≤ 8936178134069^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692461959 5000000000 8936178134069 20000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321562961/2500000000 : ℝ), (-1923479379/10000000000 : ℝ), (2692461959/5000000000 : ℝ)] ![(21809127387267/50000000000000 : ℝ), (1462606817937/12500000000000 : ℝ), (8936178134069/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321562961/2500000000 : ℝ)|^1105 ≤ (21809127387267/50000000000000 : ℝ)^849
        have hw : |(1321562961/2500000000 : ℝ)|=(1321562961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1923479379/10000000000 : ℝ)|^1105 ≤ (1462606817937/12500000000000 : ℝ)^849
        have hw : |(-1923479379/10000000000 : ℝ)|=(1923479379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692461959/5000000000 : ℝ)|^1105 ≤ (8936178134069/20000000000000 : ℝ)^849
        have hw : |(2692461959/5000000000 : ℝ)|=(2692461959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_box_2 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2643125871/5000000000 : ℝ)*x 0 + (673115567/1250000000 : ℝ)*x 1 + (-76939147/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643125871/5000000000 : ℝ)^1105 ≤ (5452281709891/12500000000000 : ℝ)^849 := by
    have hnat : (2643125871 : ℕ)^1105*12500000000000^849 ≤ 5452281709891^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643125871 5000000000 5452281709891 12500000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673115567/1250000000 : ℝ)^1105 ≤ (11170224336083/25000000000000 : ℝ)^849 := by
    have hnat : (673115567 : ℕ)^1105*25000000000000^849 ≤ 11170224336083^849*1250000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673115567 1250000000 11170224336083 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (76939147/400000000 : ℝ)^1105 ≤ (11700848969621/100000000000000 : ℝ)^849 := by
    have hnat : (76939147 : ℕ)^1105*100000000000000^849 ≤ 11700848969621^849*400000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76939147 400000000 11700848969621 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643125871/5000000000 : ℝ), (673115567/1250000000 : ℝ), (-76939147/400000000 : ℝ)] ![(5452281709891/12500000000000 : ℝ), (11170224336083/25000000000000 : ℝ), (11700848969621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643125871/5000000000 : ℝ)|^1105 ≤ (5452281709891/12500000000000 : ℝ)^849
        have hw : |(2643125871/5000000000 : ℝ)|=(2643125871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673115567/1250000000 : ℝ)|^1105 ≤ (11170224336083/25000000000000 : ℝ)^849
        have hw : |(673115567/1250000000 : ℝ)|=(673115567/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-76939147/400000000 : ℝ)|^1105 ≤ (11700848969621/100000000000000 : ℝ)^849
        have hw : |(-76939147/400000000 : ℝ)|=(76939147/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_box_3 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2221190119/5000000000 : ℝ)*x 0 + (4227484473/10000000000 : ℝ)*x 1 + (169099397/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2221190119/5000000000 : ℝ)^1105 ≤ (34782506231499/100000000000000 : ℝ)^849 := by
    have hnat : (2221190119 : ℕ)^1105*100000000000000^849 ≤ 34782506231499^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221190119 5000000000 34782506231499 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227484473/10000000000 : ℝ)^1105 ≤ (32608744607119/100000000000000 : ℝ)^849 := by
    have hnat : (4227484473 : ℕ)^1105*100000000000000^849 ≤ 32608744607119^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227484473 10000000000 32608744607119 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169099397/400000000 : ℝ)^1105 ≤ (32608749144917/100000000000000 : ℝ)^849 := by
    have hnat : (169099397 : ℕ)^1105*100000000000000^849 ≤ 32608749144917^849*400000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169099397 400000000 32608749144917 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2221190119/5000000000 : ℝ), (4227484473/10000000000 : ℝ), (169099397/400000000 : ℝ)] ![(34782506231499/100000000000000 : ℝ), (32608744607119/100000000000000 : ℝ), (32608749144917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2221190119/5000000000 : ℝ)|^1105 ≤ (34782506231499/100000000000000 : ℝ)^849
        have hw : |(2221190119/5000000000 : ℝ)|=(2221190119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227484473/10000000000 : ℝ)|^1105 ≤ (32608744607119/100000000000000 : ℝ)^849
        have hw : |(4227484473/10000000000 : ℝ)|=(4227484473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169099397/400000000 : ℝ)|^1105 ≤ (32608749144917/100000000000000 : ℝ)^849
        have hw : |(169099397/400000000 : ℝ)|=(169099397/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_box_4 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2107443511/10000000000 : ℝ)*x 0 + (526694589/1000000000 : ℝ)*x 1 + (105338907/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2107443511/10000000000 : ℝ)^1105 ≤ (13177931669319/100000000000000 : ℝ)^849 := by
    have hnat : (2107443511 : ℕ)^1105*100000000000000^849 ≤ 13177931669319^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107443511 10000000000 13177931669319 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526694589/1000000000 : ℝ)^1105 ≤ (43411037053671/100000000000000 : ℝ)^849 := by
    have hnat : (526694589 : ℕ)^1105*100000000000000^849 ≤ 43411037053671^849*1000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526694589 1000000000 43411037053671 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105338907/200000000 : ℝ)^1105 ≤ (5426378907607/12500000000000 : ℝ)^849 := by
    have hnat : (105338907 : ℕ)^1105*12500000000000^849 ≤ 5426378907607^849*200000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105338907 200000000 5426378907607 12500000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2107443511/10000000000 : ℝ), (526694589/1000000000 : ℝ), (105338907/200000000 : ℝ)] ![(13177931669319/100000000000000 : ℝ), (43411037053671/100000000000000 : ℝ), (5426378907607/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2107443511/10000000000 : ℝ)|^1105 ≤ (13177931669319/100000000000000 : ℝ)^849
        have hw : |(-2107443511/10000000000 : ℝ)|=(2107443511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526694589/1000000000 : ℝ)|^1105 ≤ (43411037053671/100000000000000 : ℝ)^849
        have hw : |(526694589/1000000000 : ℝ)|=(526694589/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105338907/200000000 : ℝ)|^1105 ≤ (5426378907607/12500000000000 : ℝ)^849
        have hw : |(105338907/200000000 : ℝ)|=(105338907/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_box_5 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5368715449/10000000000 : ℝ)*x 0 + (-1971569793/10000000000 : ℝ)*x 1 + (2633472901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368715449/10000000000 : ℝ)^1105 ≤ (44505929543717/100000000000000 : ℝ)^849 := by
    have hnat : (5368715449 : ℕ)^1105*100000000000000^849 ≤ 44505929543717^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368715449 10000000000 44505929543717 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1971569793/10000000000 : ℝ)^1105 ≤ (120830343281/1000000000000 : ℝ)^849 := by
    have hnat : (1971569793 : ℕ)^1105*1000000000000^849 ≤ 120830343281^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971569793 10000000000 120830343281 1000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633472901/5000000000 : ℝ)^1105 ≤ (43411036109657/100000000000000 : ℝ)^849 := by
    have hnat : (2633472901 : ℕ)^1105*100000000000000^849 ≤ 43411036109657^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633472901 5000000000 43411036109657 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368715449/10000000000 : ℝ), (-1971569793/10000000000 : ℝ), (2633472901/5000000000 : ℝ)] ![(44505929543717/100000000000000 : ℝ), (120830343281/1000000000000 : ℝ), (43411036109657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368715449/10000000000 : ℝ)|^1105 ≤ (44505929543717/100000000000000 : ℝ)^849
        have hw : |(5368715449/10000000000 : ℝ)|=(5368715449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1971569793/10000000000 : ℝ)|^1105 ≤ (120830343281/1000000000000 : ℝ)^849
        have hw : |(-1971569793/10000000000 : ℝ)|=(1971569793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633472901/5000000000 : ℝ)|^1105 ≤ (43411036109657/100000000000000 : ℝ)^849
        have hw : |(2633472901/5000000000 : ℝ)|=(2633472901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_box_6 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2684357531/5000000000 : ℝ)*x 0 + (2633472847/5000000000 : ℝ)*x 1 + (-985785231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684357531/5000000000 : ℝ)^1105 ≤ (44505925368173/100000000000000 : ℝ)^849 := by
    have hnat : (2684357531 : ℕ)^1105*100000000000000^849 ≤ 44505925368173^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684357531 5000000000 44505925368173 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633472847/5000000000 : ℝ)^1105 ≤ (21705517475547/50000000000000 : ℝ)^849 := by
    have hnat : (2633472847 : ℕ)^1105*50000000000000^849 ≤ 21705517475547^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633472847 5000000000 21705517475547 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (985785231/5000000000 : ℝ)^1105 ≤ (6041519832227/50000000000000 : ℝ)^849 := by
    have hnat : (985785231 : ℕ)^1105*50000000000000^849 ≤ 6041519832227^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985785231 5000000000 6041519832227 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684357531/5000000000 : ℝ), (2633472847/5000000000 : ℝ), (-985785231/5000000000 : ℝ)] ![(44505925368173/100000000000000 : ℝ), (21705517475547/50000000000000 : ℝ), (6041519832227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684357531/5000000000 : ℝ)|^1105 ≤ (44505925368173/100000000000000 : ℝ)^849
        have hw : |(2684357531/5000000000 : ℝ)|=(2684357531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633472847/5000000000 : ℝ)|^1105 ≤ (21705517475547/50000000000000 : ℝ)^849
        have hw : |(2633472847/5000000000 : ℝ)|=(2633472847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-985785231/5000000000 : ℝ)|^1105 ≤ (6041519832227/50000000000000 : ℝ)^849
        have hw : |(-985785231/5000000000 : ℝ)|=(985785231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_box_7 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1037474197/2500000000 : ℝ)*x 0 + (4373676407/10000000000 : ℝ)*x 1 + (4373676383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037474197/2500000000 : ℝ)^1105 ≤ (31831977403023/100000000000000 : ℝ)^849 := by
    have hnat : (1037474197 : ℕ)^1105*100000000000000^849 ≤ 31831977403023^849*2500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037474197 2500000000 31831977403023 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4373676407/10000000000 : ℝ)^1105 ≤ (8521002852137/25000000000000 : ℝ)^849 := by
    have hnat : (4373676407 : ℕ)^1105*25000000000000^849 ≤ 8521002852137^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373676407 10000000000 8521002852137 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4373676383/10000000000 : ℝ)^1105 ≤ (34084011165121/100000000000000 : ℝ)^849 := by
    have hnat : (4373676383 : ℕ)^1105*100000000000000^849 ≤ 34084011165121^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373676383 10000000000 34084011165121 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037474197/2500000000 : ℝ), (4373676407/10000000000 : ℝ), (4373676383/10000000000 : ℝ)] ![(31831977403023/100000000000000 : ℝ), (8521002852137/25000000000000 : ℝ), (34084011165121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037474197/2500000000 : ℝ)|^1105 ≤ (31831977403023/100000000000000 : ℝ)^849
        have hw : |(1037474197/2500000000 : ℝ)|=(1037474197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4373676407/10000000000 : ℝ)|^1105 ≤ (8521002852137/25000000000000 : ℝ)^849
        have hw : |(4373676407/10000000000 : ℝ)|=(4373676407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4373676383/10000000000 : ℝ)|^1105 ≤ (34084011165121/100000000000000 : ℝ)^849
        have hw : |(4373676383/10000000000 : ℝ)|=(4373676383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_box_8 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-408010157/2000000000 : ℝ)*x 0 + (103704121/200000000 : ℝ)*x 1 + (2699439001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (408010157/2000000000 : ℝ)^1105 ≤ (631605917199/5000000000000 : ℝ)^849 := by
    have hnat : (408010157 : ℕ)^1105*5000000000000^849 ≤ 631605917199^849*2000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408010157 2000000000 631605917199 5000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103704121/200000000 : ℝ)^1105 ≤ (10634059340523/25000000000000 : ℝ)^849 := by
    have hnat : (103704121 : ℕ)^1105*25000000000000^849 ≤ 10634059340523^849*200000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103704121 200000000 10634059340523 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699439001/5000000000 : ℝ)^1105 ≤ (11207911068881/25000000000000 : ℝ)^849 := by
    have hnat : (2699439001 : ℕ)^1105*25000000000000^849 ≤ 11207911068881^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699439001 5000000000 11207911068881 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-408010157/2000000000 : ℝ), (103704121/200000000 : ℝ), (2699439001/5000000000 : ℝ)] ![(631605917199/5000000000000 : ℝ), (10634059340523/25000000000000 : ℝ), (11207911068881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-408010157/2000000000 : ℝ)|^1105 ≤ (631605917199/5000000000000 : ℝ)^849
        have hw : |(-408010157/2000000000 : ℝ)|=(408010157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103704121/200000000 : ℝ)|^1105 ≤ (10634059340523/25000000000000 : ℝ)^849
        have hw : |(103704121/200000000 : ℝ)|=(103704121/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699439001/5000000000 : ℝ)|^1105 ≤ (11207911068881/25000000000000 : ℝ)^849
        have hw : |(2699439001/5000000000 : ℝ)|=(2699439001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_box_9 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5276493577/10000000000 : ℝ)*x 0 + (-95883341/500000000 : ℝ)*x 1 + (1079775851/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276493577/10000000000 : ℝ)^1105 ≤ (43513487225741/100000000000000 : ℝ)^849 := by
    have hnat : (5276493577 : ℕ)^1105*100000000000000^849 ≤ 43513487225741^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276493577 10000000000 43513487225741 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (95883341/500000000 : ℝ)^1105 ≤ (5827427476821/50000000000000 : ℝ)^849 := by
    have hnat : (95883341 : ℕ)^1105*50000000000000^849 ≤ 5827427476821^849*500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95883341 500000000 5827427476821 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079775851/2000000000 : ℝ)^1105 ≤ (44831657817649/100000000000000 : ℝ)^849 := by
    have hnat : (1079775851 : ℕ)^1105*100000000000000^849 ≤ 44831657817649^849*2000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079775851 2000000000 44831657817649 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276493577/10000000000 : ℝ), (-95883341/500000000 : ℝ), (1079775851/2000000000 : ℝ)] ![(43513487225741/100000000000000 : ℝ), (5827427476821/50000000000000 : ℝ), (44831657817649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276493577/10000000000 : ℝ)|^1105 ≤ (43513487225741/100000000000000 : ℝ)^849
        have hw : |(5276493577/10000000000 : ℝ)|=(5276493577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-95883341/500000000 : ℝ)|^1105 ≤ (5827427476821/50000000000000 : ℝ)^849
        have hw : |(-95883341/500000000 : ℝ)|=(95883341/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079775851/2000000000 : ℝ)|^1105 ≤ (44831657817649/100000000000000 : ℝ)^849
        have hw : |(1079775851/2000000000 : ℝ)|=(1079775851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_box_10 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5276493409/10000000000 : ℝ)*x 0 + (5398879379/10000000000 : ℝ)*x 1 + (-1917666877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276493409/10000000000 : ℝ)^1105 ≤ (10878371355637/25000000000000 : ℝ)^849 := by
    have hnat : (5276493409 : ℕ)^1105*25000000000000^849 ≤ 10878371355637^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276493409 10000000000 10878371355637 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398879379/10000000000 : ℝ)^1105 ≤ (11207914789453/25000000000000 : ℝ)^849 := by
    have hnat : (5398879379 : ℕ)^1105*25000000000000^849 ≤ 11207914789453^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398879379 10000000000 11207914789453 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1917666877/10000000000 : ℝ)^1105 ≤ (2913713851131/25000000000000 : ℝ)^849 := by
    have hnat : (1917666877 : ℕ)^1105*25000000000000^849 ≤ 2913713851131^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917666877 10000000000 2913713851131 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276493409/10000000000 : ℝ), (5398879379/10000000000 : ℝ), (-1917666877/10000000000 : ℝ)] ![(10878371355637/25000000000000 : ℝ), (11207914789453/25000000000000 : ℝ), (2913713851131/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276493409/10000000000 : ℝ)|^1105 ≤ (10878371355637/25000000000000 : ℝ)^849
        have hw : |(5276493409/10000000000 : ℝ)|=(5276493409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398879379/10000000000 : ℝ)|^1105 ≤ (11207914789453/25000000000000 : ℝ)^849
        have hw : |(5398879379/10000000000 : ℝ)|=(5398879379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1917666877/10000000000 : ℝ)|^1105 ≤ (2913713851131/25000000000000 : ℝ)^849
        have hw : |(-1917666877/10000000000 : ℝ)|=(1917666877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_box_11 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1119104963/2500000000 : ℝ)*x 0 + (2105089291/5000000000 : ℝ)*x 1 + (4210177227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1119104963/2500000000 : ℝ)^1105 ≤ (35129790323421/100000000000000 : ℝ)^849 := by
    have hnat : (1119104963 : ℕ)^1105*100000000000000^849 ≤ 35129790323421^849*2500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119104963 2500000000 35129790323421 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2105089291/5000000000 : ℝ)^1105 ≤ (6487022324393/20000000000000 : ℝ)^849 := by
    have hnat : (2105089291 : ℕ)^1105*20000000000000^849 ≤ 6487022324393^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105089291 5000000000 6487022324393 20000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4210177227/10000000000 : ℝ)^1105 ≤ (32435098035429/100000000000000 : ℝ)^849 := by
    have hnat : (4210177227 : ℕ)^1105*100000000000000^849 ≤ 32435098035429^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4210177227 10000000000 32435098035429 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1119104963/2500000000 : ℝ), (2105089291/5000000000 : ℝ), (4210177227/10000000000 : ℝ)] ![(35129790323421/100000000000000 : ℝ), (6487022324393/20000000000000 : ℝ), (32435098035429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1119104963/2500000000 : ℝ)|^1105 ≤ (35129790323421/100000000000000 : ℝ)^849
        have hw : |(1119104963/2500000000 : ℝ)|=(1119104963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2105089291/5000000000 : ℝ)|^1105 ≤ (6487022324393/20000000000000 : ℝ)^849
        have hw : |(2105089291/5000000000 : ℝ)|=(2105089291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4210177227/10000000000 : ℝ)|^1105 ≤ (32435098035429/100000000000000 : ℝ)^849
        have hw : |(4210177227/10000000000 : ℝ)|=(4210177227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_box_12 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-115957371/625000000 : ℝ)*x 0 + (2732350131/5000000000 : ℝ)*x 1 + (5255805051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (115957371/625000000 : ℝ)^1105 ≤ (5582048979161/50000000000000 : ℝ)^849 := by
    have hnat : (115957371 : ℕ)^1105*50000000000000^849 ≤ 5582048979161^849*625000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115957371 625000000 5582048979161 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732350131/5000000000 : ℝ)^1105 ≤ (11386084867067/25000000000000 : ℝ)^849 := by
    have hnat : (2732350131 : ℕ)^1105*25000000000000^849 ≤ 11386084867067^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732350131 5000000000 11386084867067 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255805051/10000000000 : ℝ)^1105 ≤ (43291562559331/100000000000000 : ℝ)^849 := by
    have hnat : (5255805051 : ℕ)^1105*100000000000000^849 ≤ 43291562559331^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255805051 10000000000 43291562559331 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-115957371/625000000 : ℝ), (2732350131/5000000000 : ℝ), (5255805051/10000000000 : ℝ)] ![(5582048979161/50000000000000 : ℝ), (11386084867067/25000000000000 : ℝ), (43291562559331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-115957371/625000000 : ℝ)|^1105 ≤ (5582048979161/50000000000000 : ℝ)^849
        have hw : |(-115957371/625000000 : ℝ)|=(115957371/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732350131/5000000000 : ℝ)|^1105 ≤ (11386084867067/25000000000000 : ℝ)^849
        have hw : |(2732350131/5000000000 : ℝ)|=(2732350131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255805051/10000000000 : ℝ)|^1105 ≤ (43291562559331/100000000000000 : ℝ)^849
        have hw : |(5255805051/10000000000 : ℝ)|=(5255805051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_box_13 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2688250317/5000000000 : ℝ)*x 0 + (-988006349/5000000000 : ℝ)*x 1 + (2627902779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688250317/5000000000 : ℝ)^1105 ≤ (44589946301929/100000000000000 : ℝ)^849 := by
    have hnat : (2688250317 : ℕ)^1105*100000000000000^849 ≤ 44589946301929^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688250317 5000000000 44589946301929 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (988006349/5000000000 : ℝ)^1105 ≤ (3029621422363/25000000000000 : ℝ)^849 := by
    have hnat : (988006349 : ℕ)^1105*25000000000000^849 ≤ 3029621422363^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988006349 5000000000 3029621422363 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627902779/5000000000 : ℝ)^1105 ≤ (43291567994669/100000000000000 : ℝ)^849 := by
    have hnat : (2627902779 : ℕ)^1105*100000000000000^849 ≤ 43291567994669^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627902779 5000000000 43291567994669 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688250317/5000000000 : ℝ), (-988006349/5000000000 : ℝ), (2627902779/5000000000 : ℝ)] ![(44589946301929/100000000000000 : ℝ), (3029621422363/25000000000000 : ℝ), (43291567994669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688250317/5000000000 : ℝ)|^1105 ≤ (44589946301929/100000000000000 : ℝ)^849
        have hw : |(2688250317/5000000000 : ℝ)|=(2688250317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-988006349/5000000000 : ℝ)|^1105 ≤ (3029621422363/25000000000000 : ℝ)^849
        have hw : |(-988006349/5000000000 : ℝ)|=(988006349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627902779/5000000000 : ℝ)|^1105 ≤ (43291567994669/100000000000000 : ℝ)^849
        have hw : |(2627902779/5000000000 : ℝ)|=(2627902779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_box_14 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2688250449/5000000000 : ℝ)*x 0 + (5255805099/10000000000 : ℝ)*x 1 + (-1976012957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688250449/5000000000 : ℝ)^1105 ≤ (44589949151607/100000000000000 : ℝ)^849 := by
    have hnat : (2688250449 : ℕ)^1105*100000000000000^849 ≤ 44589949151607^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688250449 5000000000 44589949151607 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255805099/10000000000 : ℝ)^1105 ≤ (43291563073919/100000000000000 : ℝ)^849 := by
    have hnat : (5255805099 : ℕ)^1105*100000000000000^849 ≤ 43291563073919^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255805099 10000000000 43291563073919 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1976012957/10000000000 : ℝ)^1105 ≤ (6059243878399/50000000000000 : ℝ)^849 := by
    have hnat : (1976012957 : ℕ)^1105*50000000000000^849 ≤ 6059243878399^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976012957 10000000000 6059243878399 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688250449/5000000000 : ℝ), (5255805099/10000000000 : ℝ), (-1976012957/10000000000 : ℝ)] ![(44589949151607/100000000000000 : ℝ), (43291563073919/100000000000000 : ℝ), (6059243878399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688250449/5000000000 : ℝ)|^1105 ≤ (44589949151607/100000000000000 : ℝ)^849
        have hw : |(2688250449/5000000000 : ℝ)|=(2688250449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255805099/10000000000 : ℝ)|^1105 ≤ (43291563073919/100000000000000 : ℝ)^849
        have hw : |(5255805099/10000000000 : ℝ)|=(5255805099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1976012957/10000000000 : ℝ)|^1105 ≤ (6059243878399/50000000000000 : ℝ)^849
        have hw : |(-1976012957/10000000000 : ℝ)|=(1976012957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_box_15 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4121829151/10000000000 : ℝ)*x 0 + (438746917/1000000000 : ℝ)*x 1 + (4387468943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4121829151/10000000000 : ℝ)^1105 ≤ (1577602578259/5000000000000 : ℝ)^849 := by
    have hnat : (4121829151 : ℕ)^1105*5000000000000^849 ≤ 1577602578259^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4121829151 10000000000 1577602578259 5000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438746917/1000000000 : ℝ)^1105 ≤ (34223975362117/100000000000000 : ℝ)^849 := by
    have hnat : (438746917 : ℕ)^1105*100000000000000^849 ≤ 34223975362117^849*1000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438746917 1000000000 34223975362117 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4387468943/10000000000 : ℝ)^1105 ≤ (3422397305751/10000000000000 : ℝ)^849 := by
    have hnat : (4387468943 : ℕ)^1105*10000000000000^849 ≤ 3422397305751^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4387468943 10000000000 3422397305751 10000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4121829151/10000000000 : ℝ), (438746917/1000000000 : ℝ), (4387468943/10000000000 : ℝ)] ![(1577602578259/5000000000000 : ℝ), (34223975362117/100000000000000 : ℝ), (3422397305751/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4121829151/10000000000 : ℝ)|^1105 ≤ (1577602578259/5000000000000 : ℝ)^849
        have hw : |(4121829151/10000000000 : ℝ)|=(4121829151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(438746917/1000000000 : ℝ)|^1105 ≤ (34223975362117/100000000000000 : ℝ)^849
        have hw : |(438746917/1000000000 : ℝ)|=(438746917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4387468943/10000000000 : ℝ)|^1105 ≤ (3422397305751/10000000000000 : ℝ)^849
        have hw : |(4387468943/10000000000 : ℝ)|=(4387468943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1460_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5701/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(1573/2500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7397/12500 : ℝ) ∧ (40309/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (106/125 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3693/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5701/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3693/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5701/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3693/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5701/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3693/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5701/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3693/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5701/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3693/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5701/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5701/50000 : ℝ) ^ (4419/1024 : ℝ) ≤ (2130139169888577/25000000000000000000 : ℝ) := by
    have hpowers : (5701/50000 : ℝ)^4419 ≤ (2130139169888577/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5701 : ℕ)^4419*25000000000000000000^1024 ≤ 2130139169888577^1024*50000^4419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5701 50000 2130139169888577 25000000000000000000 4419 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5701/50000 : ℝ)) (X := (2130139169888577/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3693/25000 : ℝ) ^ (4419/1024 : ℝ) ≤ (13023979317707727/50000000000000000000 : ℝ) := by
    have hpowers : (3693/25000 : ℝ)^4419 ≤ (13023979317707727/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3693 : ℕ)^4419*50000000000000000000^1024 ≤ 13023979317707727^1024*25000^4419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3693 25000 13023979317707727 50000000000000000000 4419 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3693/25000 : ℝ)) (X := (13023979317707727/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502130139169888577/12500000000000000000 : ℝ) ≤ (10000394862138279/10000000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (12502130139169888577/12500000000000000000 : ℝ)^1024 ≤ (10000394862138279/10000000000000000 : ℝ)^4419 := by
      have hnat : (12502130139169888577 : ℕ)^1024*10000000000000000^4419 ≤ 10000394862138279^4419*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502130139169888577 12500000000000000000 10000394862138279 10000000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000394862138279/10000000000000000 : ℝ)) (X := (12502130139169888577/12500000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017284257657484881/50000000000000000000 : ℝ) ≤ (10000800938223719/10000000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (50017284257657484881/50000000000000000000 : ℝ)^1024 ≤ (10000800938223719/10000000000000000 : ℝ)^4419 := by
      have hnat : (50017284257657484881 : ℕ)^1024*10000000000000000^4419 ≤ 10000800938223719^4419*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017284257657484881 50000000000000000000 10000800938223719 10000000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000800938223719/10000000000000000 : ℝ)) (X := (50017284257657484881/50000000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013023979317707727/25000000000000000000 : ℝ) ≤ (10001207014309159/10000000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (25013023979317707727/25000000000000000000 : ℝ)^1024 ≤ (10001207014309159/10000000000000000 : ℝ)^4419 := by
      have hnat : (25013023979317707727 : ℕ)^1024*10000000000000000^4419 ≤ 10001207014309159^4419*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013023979317707727 25000000000000000000 10001207014309159 10000000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001207014309159/10000000000000000 : ℝ)) (X := (25013023979317707727/25000000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2130139169888577/25000000000000000000 : ℝ) ≤ ((3369207052635362647/3370000000000000000 : ℝ)+2*(1268987767/1053125000000 : ℝ)*(5701/50000 : ℝ))^(4419/1024 : ℝ) := by
    rw [show (3369207052635362647/3370000000000000000 : ℝ)+2*(1268987767/1053125000000 : ℝ)*(5701/50000 : ℝ)=(10000394862138279/10000000000000000 : ℝ) by norm_num, show 1+2*(2130139169888577/25000000000000000000 : ℝ)=(12502130139169888577/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13023979317707727/50000000000000000000 : ℝ)+(2130139169888577/25000000000000000000 : ℝ) ≤ ((3369207052635362647/3370000000000000000 : ℝ)+(1268987767/1053125000000 : ℝ)*((3693/25000 : ℝ)+(5701/50000 : ℝ)))^(4419/1024 : ℝ) := by
    rw [show (3369207052635362647/3370000000000000000 : ℝ)+(1268987767/1053125000000 : ℝ)*((3693/25000 : ℝ)+(5701/50000 : ℝ))=(10000800938223719/10000000000000000 : ℝ) by norm_num, show 1+(13023979317707727/50000000000000000000 : ℝ)+(2130139169888577/25000000000000000000 : ℝ)=(50017284257657484881/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13023979317707727/50000000000000000000 : ℝ) ≤ ((3369207052635362647/3370000000000000000 : ℝ)+2*(1268987767/1053125000000 : ℝ)*(3693/25000 : ℝ))^(4419/1024 : ℝ) := by
    rw [show (3369207052635362647/3370000000000000000 : ℝ)+2*(1268987767/1053125000000 : ℝ)*(3693/25000 : ℝ)=(10001207014309159/10000000000000000 : ℝ) by norm_num, show 1+2*(13023979317707727/50000000000000000000 : ℝ)=(25013023979317707727/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3369207052635362647/3370000000000000000 : ℝ)*(X 1 0+X 2 0)+(1268987767/1053125000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (5701/50000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (3369207052635362647/3370000000000000000 : ℝ)) (alpha := (1268987767/1053125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3369207052635362647/3370000000000000000 : ℝ)*(X 0 1+X 2 1)+(1268987767/1053125000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (5701/50000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (3369207052635362647/3370000000000000000 : ℝ)) (alpha := (1268987767/1053125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3369207052635362647/3370000000000000000 : ℝ)*(X 0 2+X 1 2)+(1268987767/1053125000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (5701/50000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (3369207052635362647/3370000000000000000 : ℝ)) (alpha := (1268987767/1053125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-893897939/5000000000 : ℝ)*X 0 0+(1346231191/2500000000 : ℝ)*X 0 1+(2692462059/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1321562961/2500000000 : ℝ)*X 1 0+(-1923479379/10000000000 : ℝ)*X 1 1+(2692461959/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2643125871/5000000000 : ℝ)*X 2 0+(673115567/1250000000 : ℝ)*X 2 1+(-76939147/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2221190119/5000000000 : ℝ)*X 0 0+(4227484473/10000000000 : ℝ)*X 0 1+(169099397/400000000 : ℝ)*X 0 2+(2221190119/5000000000 : ℝ)*X 1 0+(4227484473/10000000000 : ℝ)*X 1 1+(169099397/400000000 : ℝ)*X 1 2+(2221190119/5000000000 : ℝ)*X 2 0+(4227484473/10000000000 : ℝ)*X 2 1+(169099397/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2107443511/10000000000 : ℝ)*X 0 0+(526694589/1000000000 : ℝ)*X 0 1+(105338907/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5368715449/10000000000 : ℝ)*X 1 0+(-1971569793/10000000000 : ℝ)*X 1 1+(2633472901/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2684357531/5000000000 : ℝ)*X 2 0+(2633472847/5000000000 : ℝ)*X 2 1+(-985785231/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1037474197/2500000000 : ℝ)*X 0 0+(4373676407/10000000000 : ℝ)*X 0 1+(4373676383/10000000000 : ℝ)*X 0 2+(1037474197/2500000000 : ℝ)*X 1 0+(4373676407/10000000000 : ℝ)*X 1 1+(4373676383/10000000000 : ℝ)*X 1 2+(1037474197/2500000000 : ℝ)*X 2 0+(4373676407/10000000000 : ℝ)*X 2 1+(4373676383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-408010157/2000000000 : ℝ)*X 0 0+(103704121/200000000 : ℝ)*X 0 1+(2699439001/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276493577/10000000000 : ℝ)*X 1 0+(-95883341/500000000 : ℝ)*X 1 1+(1079775851/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276493409/10000000000 : ℝ)*X 2 0+(5398879379/10000000000 : ℝ)*X 2 1+(-1917666877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1119104963/2500000000 : ℝ)*X 0 0+(2105089291/5000000000 : ℝ)*X 0 1+(4210177227/10000000000 : ℝ)*X 0 2+(1119104963/2500000000 : ℝ)*X 1 0+(2105089291/5000000000 : ℝ)*X 1 1+(4210177227/10000000000 : ℝ)*X 1 2+(1119104963/2500000000 : ℝ)*X 2 0+(2105089291/5000000000 : ℝ)*X 2 1+(4210177227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-115957371/625000000 : ℝ)*X 0 0+(2732350131/5000000000 : ℝ)*X 0 1+(5255805051/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2688250317/5000000000 : ℝ)*X 1 0+(-988006349/5000000000 : ℝ)*X 1 1+(2627902779/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2688250449/5000000000 : ℝ)*X 2 0+(5255805099/10000000000 : ℝ)*X 2 1+(-1976012957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4121829151/10000000000 : ℝ)*X 0 0+(438746917/1000000000 : ℝ)*X 0 1+(4387468943/10000000000 : ℝ)*X 0 2+(4121829151/10000000000 : ℝ)*X 1 0+(438746917/1000000000 : ℝ)*X 1 1+(4387468943/10000000000 : ℝ)*X 1 2+(4121829151/10000000000 : ℝ)*X 2 0+(438746917/1000000000 : ℝ)*X 2 1+(4387468943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-1573/2500 : ℝ) ≤ (-106015512635093160434922910780611/168500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26443869/50000000000000 : ℝ)*(upper1) + (79649361/50000000000000 : ℝ)*(upper2) + (39466391/20000000000000 : ℝ)*(upper3) + (28008043/25000000000000 : ℝ)*(lower4) + (26977767/100000000000000 : ℝ)*(upper5) + (3050354902875129/100000000000000 : ℝ)*(major0) + (3050354902875129/100000000000000 : ℝ)*(major1) + (3050354902875129/100000000000000 : ℝ)*(major2) + (9277460887/100000000000000 : ℝ)*(sp2) + (2103995996946677/50000000000000 : ℝ)*(sp4) + (4207950920263549/100000000000000 : ℝ)*(sp5) + (4207982716432467/100000000000000 : ℝ)*(sp6) + (29901409654957/1562500000000 : ℝ)*(sp7) + (8214725961/20000000000000 : ℝ)*(sp13) + (29901409654957/1562500000000 : ℝ)*(f.failure) + (2103995996946677/50000000000000 : ℝ)*(f.sum) + (2281937802063/842500000000000000000000000 : ℝ)*base65 + (1893797241562493537/337000000000000000000000000000000 : ℝ)*base68 + (1635646778818493537/337000000000000000000000000000000 : ℝ)*base70 + (122148239325493537/337000000000000000000000000000000 : ℝ)*base72 + (6903653338789/1685000000000000000000000000 : ℝ)*base74 + (14120308472025506463/337000000000000000000000000000000 : ℝ)*base75 + (2075962435194493537/337000000000000000000000000000000 : ℝ)*base78 + (1022784265047506463/337000000000000000000000000000000 : ℝ)*base79 + (62244448536251/1685000000000000000000000000 : ℝ)*base81 + (253731/156250000000000000000 : ℝ)*base89 + (253731/156250000000000000000 : ℝ)*base91 + (253731/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (7397/12500 : ℝ) ≤ (9971534874257362199231104563243/16850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10915659/100000000000000 : ℝ)*(upper0) + (10095841/5000000000000 : ℝ)*(lower1) + (25396633/10000000000000 : ℝ)*(upper4) + (312301043113377/10000000000000 : ℝ)*(major0) + (312301043113377/10000000000000 : ℝ)*(major1) + (312301043113377/10000000000000 : ℝ)*(major2) + (4267012411541691/100000000000000 : ℝ)*(sp0) + (266675410761909/6250000000000 : ℝ)*(sp1) + (2133506224831781/50000000000000 : ℝ)*(sp2) + (979633244128567/50000000000000 : ℝ)*(sp3) + (2618400739/25000000000000 : ℝ)*(sp6) + (2683953287/50000000000000 : ℝ)*(sp7) + (10511724827/100000000000000 : ℝ)*(sp8) + (108175537987/50000000000000 : ℝ)*(sp9) + (489817964040927/25000000000000 : ℝ)*(f.failure) + (2133511461633259/50000000000000 : ℝ)*(f.sum) + (1226428800369/337000000000000000000000000 : ℝ)*base65 + (110840440106828919/33700000000000000000000000000000 : ℝ)*base67 + (91443362020171081/33700000000000000000000000000000 : ℝ)*base70 + (277016317450028919/33700000000000000000000000000000 : ℝ)*base71 + (39131480919/42125000000000000000000000 : ℝ)*base74 + (158863297929171081/33700000000000000000000000000000 : ℝ)*base76 + (309639058464628919/33700000000000000000000000000000 : ℝ)*base77 + (800042866585428919/33700000000000000000000000000000 : ℝ)*base79 + (593768243343/168500000000000000000000000 : ℝ)*base81 + (18140259/2500000000000000000000 : ℝ)*base90 + (18140259/2500000000000000000000 : ℝ)*base92 + (18140259/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40309/50000 : ℝ) ≤ (6792240085153317209531213441721/8425000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21133993/20000000000000 : ℝ)*(upper0) + (27380783/12500000000000 : ℝ)*(upper1) + (72299191/25000000000000 : ℝ)*(upper3) + (3158321/5000000000000 : ℝ)*(upper4) + (342913315428581/10000000000000 : ℝ)*(major0) + (342913315428581/10000000000000 : ℝ)*(major1) + (3429133154285811/100000000000000 : ℝ)*(major2) + (184969473743/50000000000000 : ℝ)*(sp1) + (515239537017/100000000000000 : ℝ)*(sp2) + (139529907837/100000000000000 : ℝ)*(sp3) + (2340034991889881/50000000000000 : ℝ)*(sp8) + (1169925011208069/25000000000000 : ℝ)*(sp9) + (935910948848549/20000000000000 : ℝ)*(sp10) + (107559172071569/5000000000000 : ℝ)*(sp11) + (1075661485669609/50000000000000 : ℝ)*(f.failure) + (2340034991889881/50000000000000 : ℝ)*(f.sum) + (1192945632163/421250000000000000000000000 : ℝ)*base65 + (138087667170246093/33700000000000000000000000000000 : ℝ)*base68 + (2449242725302501717/337000000000000000000000000000000 : ℝ)*base69 + (151421349891946093/33700000000000000000000000000000 : ℝ)*base72 + (8041732703217/1685000000000000000000000000 : ℝ)*base73 + (274933509045498283/337000000000000000000000000000000 : ℝ)*base76 + (31698582234486093/33700000000000000000000000000000 : ℝ)*base78 + (181779518423586093/33700000000000000000000000000000 : ℝ)*base80 + (3893416884763/337000000000000000000000000 : ℝ)*base81 + (74585147/5000000000000000000000 : ℝ)*base89 + (74585147/5000000000000000000000 : ℝ)*base91 + (24585147/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-106/125 : ℝ) ≤ (-71442125249242763260633639311957/84250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20767113/10000000000000 : ℝ)*(upper3) + (1601487/50000000000000 : ℝ)*(lower4) + (2164763/2000000000000 : ℝ)*(upper5) + (54170980173759/1562500000000 : ℝ)*(major0) + (54170980173759/1562500000000 : ℝ)*(major1) + (1733471365560289/50000000000000 : ℝ)*(major2) + (3920235383/25000000000000 : ℝ)*(sp0) + (150297975133/100000000000000 : ℝ)*(sp5) + (316719204083/100000000000000 : ℝ)*(sp6) + (5325660801/50000000000000 : ℝ)*(sp7) + (4787092276238927/100000000000000 : ℝ)*(sp12) + (2393478829602663/50000000000000 : ℝ)*(sp13) + (598348904747047/12500000000000 : ℝ)*(sp14) + (1087516389332301/50000000000000 : ℝ)*(sp15) + (543760857496551/25000000000000 : ℝ)*(f.failure) + (4787107957180459/100000000000000 : ℝ)*(f.sum) + (3249540222231/842500000000000000000000000 : ℝ)*base66 + (5452444570707427/5265625000000000000000000000000 : ℝ)*base68 + (2888731461531824983/168500000000000000000000000000000 : ℝ)*base69 + (3856409237997849/2632812500000000000000000000000 : ℝ)*base71 + (2306547402957/1685000000000000000000000000 : ℝ)*base74 + (1256867174743324983/168500000000000000000000000000000 : ℝ)*base75 + (1316259051780073/5265625000000000000000000000000 : ℝ)*base77 + (35323965811217573/5265625000000000000000000000000 : ℝ)*base79 + (481005095827/842500000000000000000000000 : ℝ)*base81 + (14030133/2500000000000000000000 : ℝ)*base89 + (14030133/2500000000000000000000 : ℝ)*base91 + (35969867/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1460_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5701/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1573/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(7397/12500 : ℝ) else (40309/50000 : ℝ) ≤ X j i ∧ X j i ≤ (106/125 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1460_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1460_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (591/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1573/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(7397/12500 : ℝ) else (40309/50000 : ℝ) ≤ X j i ∧ X j i ≤ (106/125 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1460_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1460_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (591/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1573/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(7397/12500 : ℝ) else (40309/50000 : ℝ) ≤ X j i ∧ X j i ≤ (106/125 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1460_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

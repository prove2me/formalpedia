-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1484_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:14:07.552921+00:00
-- url     : https://prove2.me/submissions/05cb302c-1e00-4a66-a1aa-c7d5a35709d2

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
theorem support_rectangle_w1484_s3_0 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-954746863/5000000000 : ℝ)*x 0 + (5441404431/10000000000 : ℝ)*x 1 + (208481863/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (954746863/5000000000 : ℝ)^4465 ≤ (11666167189161/100000000000000 : ℝ)^3441 := by
    have hnat : (954746863 : ℕ)^4465*100000000000000^3441 ≤ 11666167189161^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954746863 5000000000 11666167189161 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441404431/10000000000 : ℝ)^4465 ≤ (45400621328857/100000000000000 : ℝ)^3441 := by
    have hnat : (5441404431 : ℕ)^4465*100000000000000^3441 ≤ 45400621328857^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441404431 10000000000 45400621328857 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208481863/400000000 : ℝ)^4465 ≤ (21466605737791/50000000000000 : ℝ)^3441 := by
    have hnat : (208481863 : ℕ)^4465*50000000000000^3441 ≤ 21466605737791^3441*400000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208481863 400000000 21466605737791 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-954746863/5000000000 : ℝ), (5441404431/10000000000 : ℝ), (208481863/400000000 : ℝ)] ![(11666167189161/100000000000000 : ℝ), (45400621328857/100000000000000 : ℝ), (21466605737791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-954746863/5000000000 : ℝ)|^4465 ≤ (11666167189161/100000000000000 : ℝ)^3441
        have hw : |(-954746863/5000000000 : ℝ)|=(954746863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441404431/10000000000 : ℝ)|^4465 ≤ (45400621328857/100000000000000 : ℝ)^3441
        have hw : |(5441404431/10000000000 : ℝ)|=(5441404431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208481863/400000000 : ℝ)|^4465 ≤ (21466605737791/50000000000000 : ℝ)^3441
        have hw : |(208481863/400000000 : ℝ)|=(208481863/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s3_1 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070854403/2000000000 : ℝ)*x 0 + (-2027138343/10000000000 : ℝ)*x 1 + (1042409353/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070854403/2000000000 : ℝ)^4465 ≤ (5557442426011/12500000000000 : ℝ)^3441 := by
    have hnat : (1070854403 : ℕ)^4465*12500000000000^3441 ≤ 5557442426011^3441*2000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070854403 2000000000 5557442426011 12500000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2027138343/10000000000 : ℝ)^4465 ≤ (6303623537261/50000000000000 : ℝ)^3441 := by
    have hnat : (2027138343 : ℕ)^4465*50000000000000^3441 ≤ 6303623537261^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027138343 10000000000 6303623537261 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042409353/2000000000 : ℝ)^4465 ≤ (42933213506421/100000000000000 : ℝ)^3441 := by
    have hnat : (1042409353 : ℕ)^4465*100000000000000^3441 ≤ 42933213506421^3441*2000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042409353 2000000000 42933213506421 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070854403/2000000000 : ℝ), (-2027138343/10000000000 : ℝ), (1042409353/2000000000 : ℝ)] ![(5557442426011/12500000000000 : ℝ), (6303623537261/50000000000000 : ℝ), (42933213506421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070854403/2000000000 : ℝ)|^4465 ≤ (5557442426011/12500000000000 : ℝ)^3441
        have hw : |(1070854403/2000000000 : ℝ)|=(1070854403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2027138343/10000000000 : ℝ)|^4465 ≤ (6303623537261/50000000000000 : ℝ)^3441
        have hw : |(-2027138343/10000000000 : ℝ)|=(2027138343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042409353/2000000000 : ℝ)|^4465 ≤ (42933213506421/100000000000000 : ℝ)^3441
        have hw : |(1042409353/2000000000 : ℝ)|=(1042409353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s3_2 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354271947/10000000000 : ℝ)*x 0 + (5212046601/10000000000 : ℝ)*x 1 + (-2027138649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354271947/10000000000 : ℝ)^4465 ≤ (8891907735083/20000000000000 : ℝ)^3441 := by
    have hnat : (5354271947 : ℕ)^4465*20000000000000^3441 ≤ 8891907735083^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354271947 10000000000 8891907735083 20000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5212046601/10000000000 : ℝ)^4465 ≤ (21466605876743/50000000000000 : ℝ)^3441 := by
    have hnat : (5212046601 : ℕ)^4465*50000000000000^3441 ≤ 21466605876743^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212046601 10000000000 21466605876743 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2027138649/10000000000 : ℝ)^4465 ≤ (12607249543943/100000000000000 : ℝ)^3441 := by
    have hnat : (2027138649 : ℕ)^4465*100000000000000^3441 ≤ 12607249543943^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027138649 10000000000 12607249543943 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354271947/10000000000 : ℝ), (5212046601/10000000000 : ℝ), (-2027138649/10000000000 : ℝ)] ![(8891907735083/20000000000000 : ℝ), (21466605876743/50000000000000 : ℝ), (12607249543943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354271947/10000000000 : ℝ)|^4465 ≤ (8891907735083/20000000000000 : ℝ)^3441
        have hw : |(5354271947/10000000000 : ℝ)|=(5354271947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5212046601/10000000000 : ℝ)|^4465 ≤ (21466605876743/50000000000000 : ℝ)^3441
        have hw : |(5212046601/10000000000 : ℝ)|=(5212046601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2027138649/10000000000 : ℝ)|^4465 ≤ (12607249543943/100000000000000 : ℝ)^3441
        have hw : |(-2027138649/10000000000 : ℝ)|=(2027138649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s3_3 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4282561019/10000000000 : ℝ)*x 0 + (2017116467/5000000000 : ℝ)*x 1 + (284004713/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4282561019/10000000000 : ℝ)^4465 ≤ (16636922587449/50000000000000 : ℝ)^3441 := by
    have hnat : (4282561019 : ℕ)^4465*50000000000000^3441 ≤ 16636922587449^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4282561019 10000000000 16636922587449 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2017116467/5000000000 : ℝ)^4465 ≤ (7698040828009/25000000000000 : ℝ)^3441 := by
    have hnat : (2017116467 : ℕ)^4465*25000000000000^3441 ≤ 7698040828009^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017116467 5000000000 7698040828009 25000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (284004713/625000000 : ℝ)^4465 ≤ (4491748937851/12500000000000 : ℝ)^3441 := by
    have hnat : (284004713 : ℕ)^4465*12500000000000^3441 ≤ 4491748937851^3441*625000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284004713 625000000 4491748937851 12500000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4282561019/10000000000 : ℝ), (2017116467/5000000000 : ℝ), (284004713/625000000 : ℝ)] ![(16636922587449/50000000000000 : ℝ), (7698040828009/25000000000000 : ℝ), (4491748937851/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4282561019/10000000000 : ℝ)|^4465 ≤ (16636922587449/50000000000000 : ℝ)^3441
        have hw : |(4282561019/10000000000 : ℝ)|=(4282561019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2017116467/5000000000 : ℝ)|^4465 ≤ (7698040828009/25000000000000 : ℝ)^3441
        have hw : |(2017116467/5000000000 : ℝ)|=(2017116467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(284004713/625000000 : ℝ)|^4465 ≤ (4491748937851/12500000000000 : ℝ)^3441
        have hw : |(284004713/625000000 : ℝ)|=(284004713/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s3_4 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1909527411/10000000000 : ℝ)*x 0 + (104265321/200000000 : ℝ)*x 1 + (2720087867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1909527411/10000000000 : ℝ)^4465 ≤ (2916608558539/25000000000000 : ℝ)^3441 := by
    have hnat : (1909527411 : ℕ)^4465*25000000000000^3441 ≤ 2916608558539^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909527411 10000000000 2916608558539 25000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104265321/200000000 : ℝ)^4465 ≤ (21473123220721/50000000000000 : ℝ)^3441 := by
    have hnat : (104265321 : ℕ)^4465*50000000000000^3441 ≤ 21473123220721^3441*200000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104265321 200000000 21473123220721 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2720087867/5000000000 : ℝ)^4465 ≤ (45387319303041/100000000000000 : ℝ)^3441 := by
    have hnat : (2720087867 : ℕ)^4465*100000000000000^3441 ≤ 45387319303041^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720087867 5000000000 45387319303041 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1909527411/10000000000 : ℝ), (104265321/200000000 : ℝ), (2720087867/5000000000 : ℝ)] ![(2916608558539/25000000000000 : ℝ), (21473123220721/50000000000000 : ℝ), (45387319303041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1909527411/10000000000 : ℝ)|^4465 ≤ (2916608558539/25000000000000 : ℝ)^3441
        have hw : |(-1909527411/10000000000 : ℝ)|=(1909527411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104265321/200000000 : ℝ)|^4465 ≤ (21473123220721/50000000000000 : ℝ)^3441
        have hw : |(104265321/200000000 : ℝ)|=(104265321/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2720087867/5000000000 : ℝ)|^4465 ≤ (45387319303041/100000000000000 : ℝ)^3441
        have hw : |(2720087867/5000000000 : ℝ)|=(2720087867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s3_5 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647164249/5000000000 : ℝ)*x 0 + (-1799009633/10000000000 : ℝ)*x 1 + (272008793/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647164249/5000000000 : ℝ)^4465 ≤ (21907375239331/50000000000000 : ℝ)^3441 := by
    have hnat : (2647164249 : ℕ)^4465*50000000000000^3441 ≤ 21907375239331^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647164249 5000000000 21907375239331 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1799009633/10000000000 : ℝ)^4465 ≤ (539896442383/5000000000000 : ℝ)^3441 := by
    have hnat : (1799009633 : ℕ)^4465*5000000000000^3441 ≤ 539896442383^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799009633 10000000000 539896442383 5000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272008793/500000000 : ℝ)^4465 ≤ (22693660333543/50000000000000 : ℝ)^3441 := by
    have hnat : (272008793 : ℕ)^4465*50000000000000^3441 ≤ 22693660333543^3441*500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272008793 500000000 22693660333543 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647164249/5000000000 : ℝ), (-1799009633/10000000000 : ℝ), (272008793/500000000 : ℝ)] ![(21907375239331/50000000000000 : ℝ), (539896442383/5000000000000 : ℝ), (22693660333543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647164249/5000000000 : ℝ)|^4465 ≤ (21907375239331/50000000000000 : ℝ)^3441
        have hw : |(2647164249/5000000000 : ℝ)|=(2647164249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1799009633/10000000000 : ℝ)|^4465 ≤ (539896442383/5000000000000 : ℝ)^3441
        have hw : |(-1799009633/10000000000 : ℝ)|=(1799009633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(272008793/500000000 : ℝ)|^4465 ≤ (22693660333543/50000000000000 : ℝ)^3441
        have hw : |(272008793/500000000 : ℝ)|=(272008793/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s3_6 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294328923/10000000000 : ℝ)*x 0 + (5440175431/10000000000 : ℝ)*x 1 + (-899504821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294328923/10000000000 : ℝ)^4465 ≤ (43814755042553/100000000000000 : ℝ)^3441 := by
    have hnat : (5294328923 : ℕ)^4465*100000000000000^3441 ≤ 43814755042553^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294328923 10000000000 43814755042553 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440175431/10000000000 : ℝ)^4465 ≤ (9077463204567/20000000000000 : ℝ)^3441 := by
    have hnat : (5440175431 : ℕ)^4465*20000000000000^3441 ≤ 9077463204567^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440175431 10000000000 9077463204567 20000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899504821/5000000000 : ℝ)^4465 ≤ (2159585783551/20000000000000 : ℝ)^3441 := by
    have hnat : (899504821 : ℕ)^4465*20000000000000^3441 ≤ 2159585783551^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899504821 5000000000 2159585783551 20000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294328923/10000000000 : ℝ), (5440175431/10000000000 : ℝ), (-899504821/5000000000 : ℝ)] ![(43814755042553/100000000000000 : ℝ), (9077463204567/20000000000000 : ℝ), (2159585783551/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294328923/10000000000 : ℝ)|^4465 ≤ (43814755042553/100000000000000 : ℝ)^3441
        have hw : |(5294328923/10000000000 : ℝ)|=(5294328923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440175431/10000000000 : ℝ)|^4465 ≤ (9077463204567/20000000000000 : ℝ)^3441
        have hw : |(5440175431/10000000000 : ℝ)|=(5440175431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-899504821/5000000000 : ℝ)|^4465 ≤ (2159585783551/20000000000000 : ℝ)^3441
        have hw : |(-899504821/5000000000 : ℝ)|=(899504821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s3_7 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107065899/250000000 : ℝ)*x 0 + (1135341277/2500000000 : ℝ)*x 1 + (4036964131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107065899/250000000 : ℝ)^4465 ≤ (8318650178453/25000000000000 : ℝ)^3441 := by
    have hnat : (107065899 : ℕ)^4465*25000000000000^3441 ≤ 8318650178453^3441*250000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107065899 250000000 8318650178453 25000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1135341277/2500000000 : ℝ)^4465 ≤ (35906183132571/100000000000000 : ℝ)^3441 := by
    have hnat : (1135341277 : ℕ)^4465*100000000000000^3441 ≤ 35906183132571^3441*2500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135341277 2500000000 35906183132571 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4036964131/10000000000 : ℝ)^4465 ≤ (1232768645891/4000000000000 : ℝ)^3441 := by
    have hnat : (4036964131 : ℕ)^4465*4000000000000^3441 ≤ 1232768645891^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4036964131 10000000000 1232768645891 4000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107065899/250000000 : ℝ), (1135341277/2500000000 : ℝ), (4036964131/10000000000 : ℝ)] ![(8318650178453/25000000000000 : ℝ), (35906183132571/100000000000000 : ℝ), (1232768645891/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107065899/250000000 : ℝ)|^4465 ≤ (8318650178453/25000000000000 : ℝ)^3441
        have hw : |(107065899/250000000 : ℝ)|=(107065899/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1135341277/2500000000 : ℝ)|^4465 ≤ (35906183132571/100000000000000 : ℝ)^3441
        have hw : |(1135341277/2500000000 : ℝ)|=(1135341277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4036964131/10000000000 : ℝ)|^4465 ≤ (1232768645891/4000000000000 : ℝ)^3441
        have hw : |(4036964131/10000000000 : ℝ)|=(4036964131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1484_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80572949/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2679/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1557/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16113/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10219/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16113/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10219/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16113/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10219/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16113/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10219/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16113/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10219/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16113/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10219/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10219/100000 : ℝ) ^ (4463/1024 : ℝ) ≤ (2407559998884071/50000000000000000000 : ℝ) := by
    have hpowers : (10219/100000 : ℝ)^4463 ≤ (2407559998884071/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10219 : ℕ)^4463*50000000000000000000^1024 ≤ 2407559998884071^1024*100000^4463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10219 100000 2407559998884071 50000000000000000000 4463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10219/100000 : ℝ)) (X := (2407559998884071/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16113/100000 : ℝ) ^ (4463/1024 : ℝ) ≤ (35039579966929991/100000000000000000000 : ℝ) := by
    have hpowers : (16113/100000 : ℝ)^4463 ≤ (35039579966929991/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16113 : ℕ)^4463*100000000000000000000^1024 ≤ 35039579966929991^1024*100000^4463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16113 100000 35039579966929991 100000000000000000000 4463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16113/100000 : ℝ)) (X := (35039579966929991/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002407559998884071/25000000000000000000 : ℝ) ≤ (10000220950031081/10000000000000000 : ℝ) ^ (4463/1024 : ℝ) := by
    have hpowers : (25002407559998884071/25000000000000000000 : ℝ)^1024 ≤ (10000220950031081/10000000000000000 : ℝ)^4463 := by
      have hnat : (25002407559998884071 : ℕ)^1024*10000000000000000^4463 ≤ 10000220950031081^4463*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002407559998884071 25000000000000000000 10000220950031081 10000000000000000 1024 4463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000220950031081/10000000000000000 : ℝ)) (X := (25002407559998884071/25000000000000000000 : ℝ)) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039854699964698133/100000000000000000000 : ℝ) ≤ (10000914294143029/10000000000000000 : ℝ) ^ (4463/1024 : ℝ) := by
    have hpowers : (100039854699964698133/100000000000000000000 : ℝ)^1024 ≤ (10000914294143029/10000000000000000 : ℝ)^4463 := by
      have hnat : (100039854699964698133 : ℕ)^1024*10000000000000000^4463 ≤ 10000914294143029^4463*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039854699964698133 100000000000000000000 10000914294143029 10000000000000000 1024 4463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000914294143029/10000000000000000 : ℝ)) (X := (100039854699964698133/100000000000000000000 : ℝ)) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035039579966929991/50000000000000000000 : ℝ) ≤ (10001607638254977/10000000000000000 : ℝ) ^ (4463/1024 : ℝ) := by
    have hpowers : (50035039579966929991/50000000000000000000 : ℝ)^1024 ≤ (10001607638254977/10000000000000000 : ℝ)^4463 := by
      have hnat : (50035039579966929991 : ℕ)^1024*10000000000000000^4463 ≤ 10001607638254977^4463*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035039579966929991 50000000000000000000 10001607638254977 10000000000000000 1024 4463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001607638254977/10000000000000000 : ℝ)) (X := (50035039579966929991/50000000000000000000 : ℝ)) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2407559998884071/50000000000000000000 : ℝ) ≤ ((5892713171252319819/5894000000000000000 : ℝ)+2*(173336027987/147350000000000 : ℝ)*(10219/100000 : ℝ))^(4463/1024 : ℝ) := by
    rw [show (5892713171252319819/5894000000000000000 : ℝ)+2*(173336027987/147350000000000 : ℝ)*(10219/100000 : ℝ)=(10000220950031081/10000000000000000 : ℝ) by norm_num, show 1+2*(2407559998884071/50000000000000000000 : ℝ)=(25002407559998884071/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35039579966929991/100000000000000000000 : ℝ)+(2407559998884071/50000000000000000000 : ℝ) ≤ ((5892713171252319819/5894000000000000000 : ℝ)+(173336027987/147350000000000 : ℝ)*((16113/100000 : ℝ)+(10219/100000 : ℝ)))^(4463/1024 : ℝ) := by
    rw [show (5892713171252319819/5894000000000000000 : ℝ)+(173336027987/147350000000000 : ℝ)*((16113/100000 : ℝ)+(10219/100000 : ℝ))=(10000914294143029/10000000000000000 : ℝ) by norm_num, show 1+(35039579966929991/100000000000000000000 : ℝ)+(2407559998884071/50000000000000000000 : ℝ)=(100039854699964698133/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35039579966929991/100000000000000000000 : ℝ) ≤ ((5892713171252319819/5894000000000000000 : ℝ)+2*(173336027987/147350000000000 : ℝ)*(16113/100000 : ℝ))^(4463/1024 : ℝ) := by
    rw [show (5892713171252319819/5894000000000000000 : ℝ)+2*(173336027987/147350000000000 : ℝ)*(16113/100000 : ℝ)=(10001607638254977/10000000000000000 : ℝ) by norm_num, show 1+2*(35039579966929991/100000000000000000000 : ℝ)=(50035039579966929991/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5892713171252319819/5894000000000000000 : ℝ)*(X 1 0+X 2 0)+(173336027987/147350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4463/1024 : ℝ)) (lo := (10219/100000 : ℝ)) (hi := (16113/100000 : ℝ)) (c := (5892713171252319819/5894000000000000000 : ℝ)) (alpha := (173336027987/147350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5892713171252319819/5894000000000000000 : ℝ)*(X 0 1+X 2 1)+(173336027987/147350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4463/1024 : ℝ)) (lo := (10219/100000 : ℝ)) (hi := (16113/100000 : ℝ)) (c := (5892713171252319819/5894000000000000000 : ℝ)) (alpha := (173336027987/147350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5892713171252319819/5894000000000000000 : ℝ)*(X 0 2+X 1 2)+(173336027987/147350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4463/1024 : ℝ)) (lo := (10219/100000 : ℝ)) (hi := (16113/100000 : ℝ)) (c := (5892713171252319819/5894000000000000000 : ℝ)) (alpha := (173336027987/147350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-954746863/5000000000 : ℝ)*X 0 0+(5441404431/10000000000 : ℝ)*X 0 1+(208481863/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070854403/2000000000 : ℝ)*X 1 0+(-2027138343/10000000000 : ℝ)*X 1 1+(1042409353/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354271947/10000000000 : ℝ)*X 2 0+(5212046601/10000000000 : ℝ)*X 2 1+(-2027138649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4282561019/10000000000 : ℝ)*X 0 0+(2017116467/5000000000 : ℝ)*X 0 1+(284004713/625000000 : ℝ)*X 0 2+(4282561019/10000000000 : ℝ)*X 1 0+(2017116467/5000000000 : ℝ)*X 1 1+(284004713/625000000 : ℝ)*X 1 2+(4282561019/10000000000 : ℝ)*X 2 0+(2017116467/5000000000 : ℝ)*X 2 1+(284004713/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1909527411/10000000000 : ℝ)*X 0 0+(104265321/200000000 : ℝ)*X 0 1+(2720087867/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647164249/5000000000 : ℝ)*X 1 0+(-1799009633/10000000000 : ℝ)*X 1 1+(272008793/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294328923/10000000000 : ℝ)*X 2 0+(5440175431/10000000000 : ℝ)*X 2 1+(-899504821/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((107065899/250000000 : ℝ)*X 0 0+(1135341277/2500000000 : ℝ)*X 0 1+(4036964131/10000000000 : ℝ)*X 0 2+(107065899/250000000 : ℝ)*X 1 0+(1135341277/2500000000 : ℝ)*X 1 1+(4036964131/10000000000 : ℝ)*X 1 2+(107065899/250000000 : ℝ)*X 2 0+(1135341277/2500000000 : ℝ)*X 2 1+(4036964131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35459648141728148899473531/3683750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2025355207/100000000000000 : ℝ)*(base19) + (225601081/12500000000000 : ℝ)*(base23) + (442191/500000000000 : ℝ)*(lower2) + (417766177/100000000000000 : ℝ)*(upper3) + (5080127/100000000000000 : ℝ)*(upper5) + (39509249671289/1250000000000 : ℝ)*(major0) + (39509249671289/1250000000000 : ℝ)*(major1) + (39509249671289/1250000000000 : ℝ)*(major2) + (2180018350813099/50000000000000 : ℝ)*(sp0) + (2180031251430351/50000000000000 : ℝ)*(sp1) + (218003136170363/5000000000000 : ℝ)*(sp2) + (490350059527933/25000000000000 : ℝ)*(sp3) + (2782658971/10000000000000 : ℝ)*(sp4) + (14860213091/100000000000000 : ℝ)*(sp7) + (1961415098324823/100000000000000 : ℝ)*(f.failure) + (1090016132053977/25000000000000 : ℝ)*(f.sum) + (866522374297/1473500000000000000000000000 : ℝ)*base66 + (6461007552728813/1052500000000000000000000000000 : ℝ)*base67 + (16781027691046313/1052500000000000000000000000000 : ℝ)*base69 + (411824380418813/1052500000000000000000000000000 : ℝ)*base71 + (1560483437267/1473500000000000000000000000 : ℝ)*base74 + (14073513498946313/1052500000000000000000000000000 : ℝ)*base75 + (2188148954193813/1052500000000000000000000000000 : ℝ)*base77 + (25935947173573813/1052500000000000000000000000000 : ℝ)*base79 + (10135758670137/2947000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (50986973/5000000000000000000000 : ℝ)*base90 + (50986973/5000000000000000000000 : ℝ)*base92 + (50986973/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33472679731430547852258477/9209375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (267255153/100000000000000 : ℝ)*(base19) + (750092177/100000000000000 : ℝ)*(base23) + (62875129/100000000000000 : ℝ)*(lower4) + (39367209/50000000000000 : ℝ)*(upper5) + (99837405280993/3125000000000 : ℝ)*(major0) + (99837405280993/3125000000000 : ℝ)*(major1) + (99837405280993/3125000000000 : ℝ)*(major2) + (417733359/50000000000000 : ℝ)*(sp0) + (1722286603/20000000000000 : ℝ)*(sp1) + (595098989/6250000000000 : ℝ)*(sp2) + (2203521810828139/50000000000000 : ℝ)*(sp4) + (1101758894608707/25000000000000 : ℝ)*(sp5) + (1101758546361749/25000000000000 : ℝ)*(sp6) + (991274679853091/50000000000000 : ℝ)*(sp7) + (991274679853091/50000000000000 : ℝ)*(f.failure) + (1101761114280749/25000000000000 : ℝ)*(f.sum) + (41449312041883/7367500000000000000000000000 : ℝ)*base66 + (7419229807489681/2631250000000000000000000000000 : ℝ)*base67 + (19855570232072819/2631250000000000000000000000000 : ℝ)*base70 + (16876473047354069/2631250000000000000000000000000 : ℝ)*base72 + (22516329292379/14735000000000000000000000000 : ℝ)*base73 + (17674394631529069/2631250000000000000000000000000 : ℝ)*base76 + (19720188767397819/2631250000000000000000000000000 : ℝ)*base78 + (48528376241147819/2631250000000000000000000000000 : ℝ)*base80 + (1089789276083/7367500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (28635359/2500000000000000000000 : ℝ)*base89 + (28635359/2500000000000000000000 : ℝ)*base91 + (28635359/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1484_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80572949/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2679/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1557/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1484_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1484_s4_0 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-955049273/5000000000 : ℝ)*x 0 + (5437497983/10000000000 : ℝ)*x 1 + (5215554021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (955049273/5000000000 : ℝ)^4465 ≤ (5835481120799/50000000000000 : ℝ)^3441 := by
    have hnat : (955049273 : ℕ)^4465*50000000000000^3441 ≤ 5835481120799^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955049273 5000000000 5835481120799 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437497983/10000000000 : ℝ)^4465 ≤ (45358332736741/100000000000000 : ℝ)^3441 := by
    have hnat : (5437497983 : ℕ)^4465*100000000000000^3441 ≤ 45358332736741^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437497983 10000000000 45358332736741 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215554021/10000000000 : ℝ)^4465 ≤ (21485352503569/50000000000000 : ℝ)^3441 := by
    have hnat : (5215554021 : ℕ)^4465*50000000000000^3441 ≤ 21485352503569^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215554021 10000000000 21485352503569 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-955049273/5000000000 : ℝ), (5437497983/10000000000 : ℝ), (5215554021/10000000000 : ℝ)] ![(5835481120799/50000000000000 : ℝ), (45358332736741/100000000000000 : ℝ), (21485352503569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-955049273/5000000000 : ℝ)|^4465 ≤ (5835481120799/50000000000000 : ℝ)^3441
        have hw : |(-955049273/5000000000 : ℝ)|=(955049273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437497983/10000000000 : ℝ)|^4465 ≤ (45358332736741/100000000000000 : ℝ)^3441
        have hw : |(5437497983/10000000000 : ℝ)|=(5437497983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215554021/10000000000 : ℝ)|^4465 ≤ (21485352503569/50000000000000 : ℝ)^3441
        have hw : |(5215554021/10000000000 : ℝ)|=(5215554021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s4_1 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070651253/2000000000 : ℝ)*x 0 + (-505962087/2500000000 : ℝ)*x 1 + (5215553679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070651253/2000000000 : ℝ)^4465 ≤ (22224297706493/50000000000000 : ℝ)^3441 := by
    have hnat : (1070651253 : ℕ)^4465*50000000000000^3441 ≤ 22224297706493^3441*2000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070651253 2000000000 22224297706493 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505962087/2500000000 : ℝ)^4465 ≤ (6290351610427/50000000000000 : ℝ)^3441 := by
    have hnat : (505962087 : ℕ)^4465*50000000000000^3441 ≤ 6290351610427^3441*2500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505962087 2500000000 6290351610427 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215553679/10000000000 : ℝ)^4465 ≤ (2685668834431/6250000000000 : ℝ)^3441 := by
    have hnat : (5215553679 : ℕ)^4465*6250000000000^3441 ≤ 2685668834431^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215553679 10000000000 2685668834431 6250000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070651253/2000000000 : ℝ), (-505962087/2500000000 : ℝ), (5215553679/10000000000 : ℝ)] ![(22224297706493/50000000000000 : ℝ), (6290351610427/50000000000000 : ℝ), (2685668834431/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070651253/2000000000 : ℝ)|^4465 ≤ (22224297706493/50000000000000 : ℝ)^3441
        have hw : |(1070651253/2000000000 : ℝ)|=(1070651253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-505962087/2500000000 : ℝ)|^4465 ≤ (6290351610427/50000000000000 : ℝ)^3441
        have hw : |(-505962087/2500000000 : ℝ)|=(505962087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215553679/10000000000 : ℝ)|^4465 ≤ (2685668834431/6250000000000 : ℝ)^3441
        have hw : |(5215553679/10000000000 : ℝ)|=(5215553679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s4_2 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070651227/2000000000 : ℝ)*x 0 + (5215554013/10000000000 : ℝ)*x 1 + (-1011924039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070651227/2000000000 : ℝ)^4465 ≤ (44448594012367/100000000000000 : ℝ)^3441 := by
    have hnat : (1070651227 : ℕ)^4465*100000000000000^3441 ≤ 44448594012367^3441*2000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070651227 2000000000 44448594012367 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215554013/10000000000 : ℝ)^4465 ≤ (10742676230403/25000000000000 : ℝ)^3441 := by
    have hnat : (5215554013 : ℕ)^4465*25000000000000^3441 ≤ 10742676230403^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215554013 10000000000 10742676230403 25000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1011924039/5000000000 : ℝ)^4465 ≤ (6290350521503/50000000000000 : ℝ)^3441 := by
    have hnat : (1011924039 : ℕ)^4465*50000000000000^3441 ≤ 6290350521503^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011924039 5000000000 6290350521503 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070651227/2000000000 : ℝ), (5215554013/10000000000 : ℝ), (-1011924039/5000000000 : ℝ)] ![(44448594012367/100000000000000 : ℝ), (10742676230403/25000000000000 : ℝ), (6290350521503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070651227/2000000000 : ℝ)|^4465 ≤ (44448594012367/100000000000000 : ℝ)^3441
        have hw : |(1070651227/2000000000 : ℝ)|=(1070651227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215554013/10000000000 : ℝ)|^4465 ≤ (10742676230403/25000000000000 : ℝ)^3441
        have hw : |(5215554013/10000000000 : ℝ)|=(5215554013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1011924039/5000000000 : ℝ)|^4465 ≤ (6290350521503/50000000000000 : ℝ)^3441
        have hw : |(-1011924039/5000000000 : ℝ)|=(1011924039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s4_3 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4282935299/10000000000 : ℝ)*x 0 + (4042429209/10000000000 : ℝ)*x 1 + (1133947987/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4282935299/10000000000 : ℝ)^4465 ≤ (33277618623951/100000000000000 : ℝ)^3441 := by
    have hnat : (4282935299 : ℕ)^4465*100000000000000^3441 ≤ 33277618623951^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4282935299 10000000000 33277618623951 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4042429209/10000000000 : ℝ)^4465 ≤ (15436682377681/50000000000000 : ℝ)^3441 := by
    have hnat : (4042429209 : ℕ)^4465*50000000000000^3441 ≤ 15436682377681^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4042429209 10000000000 15436682377681 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133947987/2500000000 : ℝ)^4465 ≤ (17924508303841/50000000000000 : ℝ)^3441 := by
    have hnat : (1133947987 : ℕ)^4465*50000000000000^3441 ≤ 17924508303841^3441*2500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133947987 2500000000 17924508303841 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4282935299/10000000000 : ℝ), (4042429209/10000000000 : ℝ), (1133947987/2500000000 : ℝ)] ![(33277618623951/100000000000000 : ℝ), (15436682377681/50000000000000 : ℝ), (17924508303841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4282935299/10000000000 : ℝ)|^4465 ≤ (33277618623951/100000000000000 : ℝ)^3441
        have hw : |(4282935299/10000000000 : ℝ)|=(4282935299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4042429209/10000000000 : ℝ)|^4465 ≤ (15436682377681/50000000000000 : ℝ)^3441
        have hw : |(4042429209/10000000000 : ℝ)|=(4042429209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1133947987/2500000000 : ℝ)|^4465 ≤ (17924508303841/50000000000000 : ℝ)^3441
        have hw : |(1133947987/2500000000 : ℝ)|=(1133947987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s4_4 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1910129397/10000000000 : ℝ)*x 0 + (521669609/1000000000 : ℝ)*x 1 + (5436347319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1910129397/10000000000 : ℝ)^4465 ≤ (11671206842453/100000000000000 : ℝ)^3441 := by
    have hnat : (1910129397 : ℕ)^4465*100000000000000^3441 ≤ 11671206842453^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1910129397 10000000000 11671206842453 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521669609/1000000000 : ℝ)^4465 ≤ (5372864374663/12500000000000 : ℝ)^3441 := by
    have hnat : (521669609 : ℕ)^4465*12500000000000^3441 ≤ 5372864374663^3441*1000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521669609 1000000000 5372864374663 12500000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436347319/10000000000 : ℝ)^4465 ≤ (22672939070801/50000000000000 : ℝ)^3441 := by
    have hnat : (5436347319 : ℕ)^4465*50000000000000^3441 ≤ 22672939070801^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436347319 10000000000 22672939070801 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1910129397/10000000000 : ℝ), (521669609/1000000000 : ℝ), (5436347319/10000000000 : ℝ)] ![(11671206842453/100000000000000 : ℝ), (5372864374663/12500000000000 : ℝ), (22672939070801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1910129397/10000000000 : ℝ)|^4465 ≤ (11671206842453/100000000000000 : ℝ)^3441
        have hw : |(-1910129397/10000000000 : ℝ)|=(1910129397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521669609/1000000000 : ℝ)|^4465 ≤ (5372864374663/12500000000000 : ℝ)^3441
        have hw : |(521669609/1000000000 : ℝ)|=(521669609/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436347319/10000000000 : ℝ)|^4465 ≤ (22672939070801/50000000000000 : ℝ)^3441
        have hw : |(5436347319/10000000000 : ℝ)|=(5436347319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s4_5 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295252447/10000000000 : ℝ)*x 0 + (-90152757/500000000 : ℝ)*x 1 + (5436347517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295252447/10000000000 : ℝ)^4465 ≤ (8764934524531/20000000000000 : ℝ)^3441 := by
    have hnat : (5295252447 : ℕ)^4465*20000000000000^3441 ≤ 8764934524531^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295252447 10000000000 8764934524531 20000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90152757/500000000 : ℝ)^4465 ≤ (10829447085901/100000000000000 : ℝ)^3441 := by
    have hnat : (90152757 : ℕ)^4465*100000000000000^3441 ≤ 10829447085901^3441*500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90152757 500000000 10829447085901 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436347517/10000000000 : ℝ)^4465 ≤ (22672940142327/50000000000000 : ℝ)^3441 := by
    have hnat : (5436347517 : ℕ)^4465*50000000000000^3441 ≤ 22672940142327^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436347517 10000000000 22672940142327 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295252447/10000000000 : ℝ), (-90152757/500000000 : ℝ), (5436347517/10000000000 : ℝ)] ![(8764934524531/20000000000000 : ℝ), (10829447085901/100000000000000 : ℝ), (22672940142327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295252447/10000000000 : ℝ)|^4465 ≤ (8764934524531/20000000000000 : ℝ)^3441
        have hw : |(5295252447/10000000000 : ℝ)|=(5295252447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-90152757/500000000 : ℝ)|^4465 ≤ (10829447085901/100000000000000 : ℝ)^3441
        have hw : |(-90152757/500000000 : ℝ)|=(90152757/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436347517/10000000000 : ℝ)|^4465 ≤ (22672940142327/50000000000000 : ℝ)^3441
        have hw : |(5436347517/10000000000 : ℝ)|=(5436347517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s4_6 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295253151/10000000000 : ℝ)*x 0 + (5436347097/10000000000 : ℝ)*x 1 + (-1803054753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295253151/10000000000 : ℝ)^4465 ≤ (43824680182997/100000000000000 : ℝ)^3441 := by
    have hnat : (5295253151 : ℕ)^4465*100000000000000^3441 ≤ 43824680182997^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295253151 10000000000 43824680182997 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436347097/10000000000 : ℝ)^4465 ≤ (45345875738787/100000000000000 : ℝ)^3441 := by
    have hnat : (5436347097 : ℕ)^4465*100000000000000^3441 ≤ 45345875738787^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436347097 10000000000 45345875738787 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1803054753/10000000000 : ℝ)^4465 ≤ (5414722034903/50000000000000 : ℝ)^3441 := by
    have hnat : (1803054753 : ℕ)^4465*50000000000000^3441 ≤ 5414722034903^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1803054753 10000000000 5414722034903 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295253151/10000000000 : ℝ), (5436347097/10000000000 : ℝ), (-1803054753/10000000000 : ℝ)] ![(43824680182997/100000000000000 : ℝ), (45345875738787/100000000000000 : ℝ), (5414722034903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295253151/10000000000 : ℝ)|^4465 ≤ (43824680182997/100000000000000 : ℝ)^3441
        have hw : |(5295253151/10000000000 : ℝ)|=(5295253151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436347097/10000000000 : ℝ)|^4465 ≤ (45345875738787/100000000000000 : ℝ)^3441
        have hw : |(5436347097/10000000000 : ℝ)|=(5436347097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1803054753/10000000000 : ℝ)|^4465 ≤ (5414722034903/50000000000000 : ℝ)^3441
        have hw : |(-1803054753/10000000000 : ℝ)|=(1803054753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s4_7 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2141502127/5000000000 : ℝ)*x 0 + (4533252909/10000000000 : ℝ)*x 1 + (808997231/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141502127/5000000000 : ℝ)^4465 ≤ (6655662766249/20000000000000 : ℝ)^3441 := by
    have hnat : (2141502127 : ℕ)^4465*20000000000000^3441 ≤ 6655662766249^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141502127 5000000000 6655662766249 20000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4533252909/10000000000 : ℝ)^4465 ≤ (35822979418171/100000000000000 : ℝ)^3441 := by
    have hnat : (4533252909 : ℕ)^4465*100000000000000^3441 ≤ 35822979418171^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533252909 10000000000 35822979418171 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (808997231/2000000000 : ℝ)^4465 ≤ (3089870674761/10000000000000 : ℝ)^3441 := by
    have hnat : (808997231 : ℕ)^4465*10000000000000^3441 ≤ 3089870674761^3441*2000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808997231 2000000000 3089870674761 10000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2141502127/5000000000 : ℝ), (4533252909/10000000000 : ℝ), (808997231/2000000000 : ℝ)] ![(6655662766249/20000000000000 : ℝ), (35822979418171/100000000000000 : ℝ), (3089870674761/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2141502127/5000000000 : ℝ)|^4465 ≤ (6655662766249/20000000000000 : ℝ)^3441
        have hw : |(2141502127/5000000000 : ℝ)|=(2141502127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4533252909/10000000000 : ℝ)|^4465 ≤ (35822979418171/100000000000000 : ℝ)^3441
        have hw : |(4533252909/10000000000 : ℝ)|=(4533252909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(808997231/2000000000 : ℝ)|^4465 ≤ (3089870674761/10000000000000 : ℝ)^3441
        have hw : |(808997231/2000000000 : ℝ)|=(808997231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1484_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80572949/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1557/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2679/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10791/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1557/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2679/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1557/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2679/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1557/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2679/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1557/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2679/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1557/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2679/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1557/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2679/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2679/25000 : ℝ) ^ (4463/1024 : ℝ) ≤ (5922377095536903/100000000000000000000 : ℝ) := by
    have hpowers : (2679/25000 : ℝ)^4463 ≤ (5922377095536903/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2679 : ℕ)^4463*100000000000000000000^1024 ≤ 5922377095536903^1024*25000^4463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2679 25000 5922377095536903 100000000000000000000 4463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2679/25000 : ℝ)) (X := (5922377095536903/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1557/10000 : ℝ) ^ (4463/1024 : ℝ) ≤ (30176714292322443/100000000000000000000 : ℝ) := by
    have hpowers : (1557/10000 : ℝ)^4463 ≤ (30176714292322443/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1557 : ℕ)^4463*100000000000000000000^1024 ≤ 30176714292322443^1024*10000^4463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1557 10000 30176714292322443 100000000000000000000 4463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1557/10000 : ℝ)) (X := (30176714292322443/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005922377095536903/50000000000000000000 : ℝ) ≤ (125003396951271/125000000000000 : ℝ) ^ (4463/1024 : ℝ) := by
    have hpowers : (50005922377095536903/50000000000000000000 : ℝ)^1024 ≤ (125003396951271/125000000000000 : ℝ)^4463 := by
      have hnat : (50005922377095536903 : ℕ)^1024*125000000000000^4463 ≤ 125003396951271^4463*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005922377095536903 50000000000000000000 125003396951271 125000000000000 1024 4463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125003396951271/125000000000000 : ℝ)) (X := (50005922377095536903/50000000000000000000 : ℝ)) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018049545693929673/50000000000000000000 : ℝ) ≤ (10000828149886563/10000000000000000 : ℝ) ^ (4463/1024 : ℝ) := by
    have hpowers : (50018049545693929673/50000000000000000000 : ℝ)^1024 ≤ (10000828149886563/10000000000000000 : ℝ)^4463 := by
      have hnat : (50018049545693929673 : ℕ)^1024*10000000000000000^4463 ≤ 10000828149886563^4463*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018049545693929673 50000000000000000000 10000828149886563 10000000000000000 1024 4463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000828149886563/10000000000000000 : ℝ)) (X := (50018049545693929673/50000000000000000000 : ℝ)) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030176714292322443/50000000000000000000 : ℝ) ≤ (5000692271835723/5000000000000000 : ℝ) ^ (4463/1024 : ℝ) := by
    have hpowers : (50030176714292322443/50000000000000000000 : ℝ)^1024 ≤ (5000692271835723/5000000000000000 : ℝ)^4463 := by
      have hnat : (50030176714292322443 : ℕ)^1024*5000000000000000^4463 ≤ 5000692271835723^4463*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030176714292322443 50000000000000000000 5000692271835723 5000000000000000 1024 4463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000692271835723/5000000000000000 : ℝ)) (X := (50030176714292322443/50000000000000000000 : ℝ)) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5922377095536903/100000000000000000000 : ℝ) ≤ ((2022058103021664261/2022500000000000000 : ℝ)+2*(185464594961/161800000000000 : ℝ)*(2679/25000 : ℝ))^(4463/1024 : ℝ) := by
    rw [show (2022058103021664261/2022500000000000000 : ℝ)+2*(185464594961/161800000000000 : ℝ)*(2679/25000 : ℝ)=(125003396951271/125000000000000 : ℝ) by norm_num, show 1+2*(5922377095536903/100000000000000000000 : ℝ)=(50005922377095536903/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30176714292322443/100000000000000000000 : ℝ)+(5922377095536903/100000000000000000000 : ℝ) ≤ ((2022058103021664261/2022500000000000000 : ℝ)+(185464594961/161800000000000 : ℝ)*((1557/10000 : ℝ)+(2679/25000 : ℝ)))^(4463/1024 : ℝ) := by
    rw [show (2022058103021664261/2022500000000000000 : ℝ)+(185464594961/161800000000000 : ℝ)*((1557/10000 : ℝ)+(2679/25000 : ℝ))=(10000828149886563/10000000000000000 : ℝ) by norm_num, show 1+(30176714292322443/100000000000000000000 : ℝ)+(5922377095536903/100000000000000000000 : ℝ)=(50018049545693929673/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30176714292322443/100000000000000000000 : ℝ) ≤ ((2022058103021664261/2022500000000000000 : ℝ)+2*(185464594961/161800000000000 : ℝ)*(1557/10000 : ℝ))^(4463/1024 : ℝ) := by
    rw [show (2022058103021664261/2022500000000000000 : ℝ)+2*(185464594961/161800000000000 : ℝ)*(1557/10000 : ℝ)=(5000692271835723/5000000000000000 : ℝ) by norm_num, show 1+2*(30176714292322443/100000000000000000000 : ℝ)=(50030176714292322443/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2022058103021664261/2022500000000000000 : ℝ)*(X 1 0+X 2 0)+(185464594961/161800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4463/1024 : ℝ)) (lo := (2679/25000 : ℝ)) (hi := (1557/10000 : ℝ)) (c := (2022058103021664261/2022500000000000000 : ℝ)) (alpha := (185464594961/161800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2022058103021664261/2022500000000000000 : ℝ)*(X 0 1+X 2 1)+(185464594961/161800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4463/1024 : ℝ)) (lo := (2679/25000 : ℝ)) (hi := (1557/10000 : ℝ)) (c := (2022058103021664261/2022500000000000000 : ℝ)) (alpha := (185464594961/161800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2022058103021664261/2022500000000000000 : ℝ)*(X 0 2+X 1 2)+(185464594961/161800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4463/1024 : ℝ)) (lo := (2679/25000 : ℝ)) (hi := (1557/10000 : ℝ)) (c := (2022058103021664261/2022500000000000000 : ℝ)) (alpha := (185464594961/161800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-955049273/5000000000 : ℝ)*X 0 0+(5437497983/10000000000 : ℝ)*X 0 1+(5215554021/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070651253/2000000000 : ℝ)*X 1 0+(-505962087/2500000000 : ℝ)*X 1 1+(5215553679/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070651227/2000000000 : ℝ)*X 2 0+(5215554013/10000000000 : ℝ)*X 2 1+(-1011924039/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4282935299/10000000000 : ℝ)*X 0 0+(4042429209/10000000000 : ℝ)*X 0 1+(1133947987/2500000000 : ℝ)*X 0 2+(4282935299/10000000000 : ℝ)*X 1 0+(4042429209/10000000000 : ℝ)*X 1 1+(1133947987/2500000000 : ℝ)*X 1 2+(4282935299/10000000000 : ℝ)*X 2 0+(4042429209/10000000000 : ℝ)*X 2 1+(1133947987/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1910129397/10000000000 : ℝ)*X 0 0+(521669609/1000000000 : ℝ)*X 0 1+(5436347319/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295252447/10000000000 : ℝ)*X 1 0+(-90152757/500000000 : ℝ)*X 1 1+(5436347517/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295253151/10000000000 : ℝ)*X 2 0+(5436347097/10000000000 : ℝ)*X 2 1+(-1803054753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2141502127/5000000000 : ℝ)*X 0 0+(4533252909/10000000000 : ℝ)*X 0 1+(808997231/2000000000 : ℝ)*X 0 2+(2141502127/5000000000 : ℝ)*X 1 0+(4533252909/10000000000 : ℝ)*X 1 1+(808997231/2000000000 : ℝ)*X 1 2+(2141502127/5000000000 : ℝ)*X 2 0+(4533252909/10000000000 : ℝ)*X 2 1+(808997231/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (92469320316233368470831/8090000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2018104333/100000000000000 : ℝ)*(base19) + (1783865761/100000000000000 : ℝ)*(base23) + (8352469/12500000000000 : ℝ)*(lower2) + (1857453/4000000000000 : ℝ)*(upper3) + (188362683/100000000000000 : ℝ)*(upper5) + (3266319907711999/100000000000000 : ℝ)*(major0) + (3266319907711999/100000000000000 : ℝ)*(major1) + (3266319907711999/100000000000000 : ℝ)*(major2) + (4505671461184961/100000000000000 : ℝ)*(sp0) + (225285204588211/5000000000000 : ℝ)*(sp1) + (4505704326002791/100000000000000 : ℝ)*(sp2) + (2026920386896547/100000000000000 : ℝ)*(sp3) + (34648683591/100000000000000 : ℝ)*(sp4) + (12937656337/100000000000000 : ℝ)*(sp7) + (506733331138221/25000000000000 : ℝ)*(f.failure) + (563213263733569/12500000000000 : ℝ)*(f.sum) + (46859886000581/8090000000000000000000000000 : ℝ)*base66 + (411494892676905239/202250000000000000000000000000000 : ℝ)*base67 + (597726538205094761/202250000000000000000000000000000 : ℝ)*base70 + (584048360592594761/202250000000000000000000000000000 : ℝ)*base72 + (33465178169601/8090000000000000000000000000 : ℝ)*base74 + (283851952287405239/202250000000000000000000000000000 : ℝ)*base75 + (3684547835183844761/202250000000000000000000000000000 : ℝ)*base78 + (1259942252459405239/202250000000000000000000000000000 : ℝ)*base79 + (26730778995331/8090000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (5083729/1250000000000000000000 : ℝ)*base89 + (5083729/1250000000000000000000 : ℝ)*base91 + (5083729/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (184379618887523761151844693/25281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (950931199/100000000000000 : ℝ)*(base19) + (481841943/25000000000000 : ℝ)*(base23) + (176402617/100000000000000 : ℝ)*(upper3) + (29348497/25000000000000 : ℝ)*(lower4) + (83171199/50000000000000 : ℝ)*(upper5) + (825091996432479/25000000000000 : ℝ)*(major0) + (825091996432479/25000000000000 : ℝ)*(major1) + (825091996432479/25000000000000 : ℝ)*(major2) + (984267379/6250000000000 : ℝ)*(sp1) + (29393618911/100000000000000 : ℝ)*(sp2) + (2276336838041949/50000000000000 : ℝ)*(sp4) + (1138164244218659/25000000000000 : ℝ)*(sp5) + (910528471019443/20000000000000 : ℝ)*(sp6) + (1024031026135681/50000000000000 : ℝ)*(sp7) + (1024031026135681/50000000000000 : ℝ)*(f.failure) + (2276336838041949/50000000000000 : ℝ)*(f.sum) + (387366897813/1011250000000000000000000000 : ℝ)*base66 + (320732828004045519/50562500000000000000000000000000 : ℝ)*base67 + (102764094523829481/50562500000000000000000000000000 : ℝ)*base70 + (548245841527079481/50562500000000000000000000000000 : ℝ)*base72 + (586785705233/1011250000000000000000000000 : ℝ)*base74 + (143085605097795519/50562500000000000000000000000000 : ℝ)*base75 + (157528883336545519/50562500000000000000000000000000 : ℝ)*base77 + (393127412672670519/50562500000000000000000000000000 : ℝ)*base79 + (23465895323427/4045000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (7706731/2500000000000000000000 : ℝ)*base90 + (7706731/2500000000000000000000 : ℝ)*base92 + (7706731/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1484_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80572949/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1557/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2679/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10791/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1484_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1484_s5_0 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1910178781/10000000000 : ℝ)*x 0 + (679621461/1250000000 : ℝ)*x 1 + (1043205473/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1910178781/10000000000 : ℝ)^4465 ≤ (2334319676773/20000000000000 : ℝ)^3441 := by
    have hnat : (1910178781 : ℕ)^4465*20000000000000^3441 ≤ 2334319676773^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1910178781 10000000000 2334319676773 20000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679621461/1250000000 : ℝ)^4465 ≤ (45352636110139/100000000000000 : ℝ)^3441 := by
    have hnat : (679621461 : ℕ)^4465*100000000000000^3441 ≤ 45352636110139^3441*1250000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679621461 1250000000 45352636110139 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043205473/2000000000 : ℝ)^4465 ≤ (10743941371347/25000000000000 : ℝ)^3441 := by
    have hnat : (1043205473 : ℕ)^4465*25000000000000^3441 ≤ 10743941371347^3441*2000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043205473 2000000000 10743941371347 25000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1910178781/10000000000 : ℝ), (679621461/1250000000 : ℝ), (1043205473/2000000000 : ℝ)] ![(2334319676773/20000000000000 : ℝ), (45352636110139/100000000000000 : ℝ), (10743941371347/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1910178781/10000000000 : ℝ)|^4465 ≤ (2334319676773/20000000000000 : ℝ)^3441
        have hw : |(-1910178781/10000000000 : ℝ)|=(1910178781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679621461/1250000000 : ℝ)|^4465 ≤ (45352636110139/100000000000000 : ℝ)^3441
        have hw : |(679621461/1250000000 : ℝ)|=(679621461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043205473/2000000000 : ℝ)|^4465 ≤ (10743941371347/25000000000000 : ℝ)^3441
        have hw : |(1043205473/2000000000 : ℝ)|=(1043205473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s5_1 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353119047/10000000000 : ℝ)*x 0 + (-40468079/200000000 : ℝ)*x 1 + (2608013621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353119047/10000000000 : ℝ)^4465 ≤ (44447117032481/100000000000000 : ℝ)^3441 := by
    have hnat : (5353119047 : ℕ)^4465*100000000000000^3441 ≤ 44447117032481^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353119047 10000000000 44447117032481 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40468079/200000000 : ℝ)^4465 ≤ (3144279694529/25000000000000 : ℝ)^3441 := by
    have hnat : (40468079 : ℕ)^4465*25000000000000^3441 ≤ 3144279694529^3441*200000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40468079 200000000 3144279694529 25000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608013621/5000000000 : ℝ)^4465 ≤ (42975764170389/100000000000000 : ℝ)^3441 := by
    have hnat : (2608013621 : ℕ)^4465*100000000000000^3441 ≤ 42975764170389^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608013621 5000000000 42975764170389 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353119047/10000000000 : ℝ), (-40468079/200000000 : ℝ), (2608013621/5000000000 : ℝ)] ![(44447117032481/100000000000000 : ℝ), (3144279694529/25000000000000 : ℝ), (42975764170389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353119047/10000000000 : ℝ)|^4465 ≤ (44447117032481/100000000000000 : ℝ)^3441
        have hw : |(5353119047/10000000000 : ℝ)|=(5353119047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40468079/200000000 : ℝ)|^4465 ≤ (3144279694529/25000000000000 : ℝ)^3441
        have hw : |(-40468079/200000000 : ℝ)|=(40468079/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608013621/5000000000 : ℝ)|^4465 ≤ (42975764170389/100000000000000 : ℝ)^3441
        have hw : |(2608013621/5000000000 : ℝ)|=(2608013621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s5_2 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334569953/625000000 : ℝ)*x 0 + (521602711/1000000000 : ℝ)*x 1 + (-2023403857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334569953/625000000 : ℝ)^4465 ≤ (22223559599019/50000000000000 : ℝ)^3441 := by
    have hnat : (334569953 : ℕ)^4465*50000000000000^3441 ≤ 22223559599019^3441*625000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334569953 625000000 22223559599019 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521602711/1000000000 : ℝ)^4465 ≤ (42975762759169/100000000000000 : ℝ)^3441 := by
    have hnat : (521602711 : ℕ)^4465*100000000000000^3441 ≤ 42975762759169^3441*1000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521602711 1000000000 42975762759169 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2023403857/10000000000 : ℝ)^4465 ≤ (6288559014009/50000000000000 : ℝ)^3441 := by
    have hnat : (2023403857 : ℕ)^4465*50000000000000^3441 ≤ 6288559014009^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023403857 10000000000 6288559014009 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334569953/625000000 : ℝ), (521602711/1000000000 : ℝ), (-2023403857/10000000000 : ℝ)] ![(22223559599019/50000000000000 : ℝ), (42975762759169/100000000000000 : ℝ), (6288559014009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334569953/625000000 : ℝ)|^4465 ≤ (22223559599019/50000000000000 : ℝ)^3441
        have hw : |(334569953/625000000 : ℝ)|=(334569953/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521602711/1000000000 : ℝ)|^4465 ≤ (42975762759169/100000000000000 : ℝ)^3441
        have hw : |(521602711/1000000000 : ℝ)|=(521602711/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2023403857/10000000000 : ℝ)|^4465 ≤ (6288559014009/50000000000000 : ℝ)^3441
        have hw : |(-2023403857/10000000000 : ℝ)|=(2023403857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s5_3 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4282985769/10000000000 : ℝ)*x 0 + (4043533141/10000000000 : ℝ)*x 1 + (906935101/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4282985769/10000000000 : ℝ)^4465 ≤ (8319531866087/25000000000000 : ℝ)^3441 := by
    have hnat : (4282985769 : ℕ)^4465*25000000000000^3441 ≤ 8319531866087^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4282985769 10000000000 8319531866087 25000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4043533141/10000000000 : ℝ)^4465 ≤ (30884305283799/100000000000000 : ℝ)^3441 := by
    have hnat : (4043533141 : ℕ)^4465*100000000000000^3441 ≤ 30884305283799^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4043533141 10000000000 30884305283799 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (906935101/2000000000 : ℝ)^4465 ≤ (17918783619243/50000000000000 : ℝ)^3441 := by
    have hnat : (906935101 : ℕ)^4465*50000000000000^3441 ≤ 17918783619243^3441*2000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906935101 2000000000 17918783619243 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4282985769/10000000000 : ℝ), (4043533141/10000000000 : ℝ), (906935101/2000000000 : ℝ)] ![(8319531866087/25000000000000 : ℝ), (30884305283799/100000000000000 : ℝ), (17918783619243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4282985769/10000000000 : ℝ)|^4465 ≤ (8319531866087/25000000000000 : ℝ)^3441
        have hw : |(4282985769/10000000000 : ℝ)|=(4282985769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4043533141/10000000000 : ℝ)|^4465 ≤ (30884305283799/100000000000000 : ℝ)^3441
        have hw : |(4043533141/10000000000 : ℝ)|=(4043533141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(906935101/2000000000 : ℝ)|^4465 ≤ (17918783619243/50000000000000 : ℝ)^3441
        have hw : |(906935101/2000000000 : ℝ)|=(906935101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s5_4 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-477552263/2500000000 : ℝ)*x 0 + (163036217/312500000 : ℝ)*x 1 + (1358957937/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (477552263/2500000000 : ℝ)^4465 ≤ (11671838389203/100000000000000 : ℝ)^3441 := by
    have hnat : (477552263 : ℕ)^4465*100000000000000^3441 ≤ 11671838389203^3441*2500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477552263 2500000000 11671838389203 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163036217/312500000 : ℝ)^4465 ≤ (21493931824419/50000000000000 : ℝ)^3441 := by
    have hnat : (163036217 : ℕ)^4465*50000000000000^3441 ≤ 21493931824419^3441*312500000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163036217 312500000 21493931824419 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358957937/2500000000 : ℝ)^4465 ≤ (5667537242701/12500000000000 : ℝ)^3441 := by
    have hnat : (1358957937 : ℕ)^4465*12500000000000^3441 ≤ 5667537242701^3441*2500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358957937 2500000000 5667537242701 12500000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-477552263/2500000000 : ℝ), (163036217/312500000 : ℝ), (1358957937/2500000000 : ℝ)] ![(11671838389203/100000000000000 : ℝ), (21493931824419/50000000000000 : ℝ), (5667537242701/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-477552263/2500000000 : ℝ)|^4465 ≤ (11671838389203/100000000000000 : ℝ)^3441
        have hw : |(-477552263/2500000000 : ℝ)|=(477552263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163036217/312500000 : ℝ)|^4465 ≤ (21493931824419/50000000000000 : ℝ)^3441
        have hw : |(163036217/312500000 : ℝ)|=(163036217/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358957937/2500000000 : ℝ)|^4465 ≤ (5667537242701/12500000000000 : ℝ)^3441
        have hw : |(1358957937/2500000000 : ℝ)|=(1358957937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s5_5 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323844347/2500000000 : ℝ)*x 0 + (-90179967/500000000 : ℝ)*x 1 + (5435831669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323844347/2500000000 : ℝ)^4465 ≤ (21913007192043/50000000000000 : ℝ)^3441 := by
    have hnat : (1323844347 : ℕ)^4465*50000000000000^3441 ≤ 21913007192043^3441*2500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323844347 2500000000 21913007192043 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90179967/500000000 : ℝ)^4465 ≤ (10833688513963/100000000000000 : ℝ)^3441 := by
    have hnat : (90179967 : ℕ)^4465*100000000000000^3441 ≤ 10833688513963^3441*500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90179967 500000000 10833688513963 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435831669/10000000000 : ℝ)^4465 ≤ (2833768567911/6250000000000 : ℝ)^3441 := by
    have hnat : (5435831669 : ℕ)^4465*6250000000000^3441 ≤ 2833768567911^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435831669 10000000000 2833768567911 6250000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323844347/2500000000 : ℝ), (-90179967/500000000 : ℝ), (5435831669/10000000000 : ℝ)] ![(21913007192043/50000000000000 : ℝ), (10833688513963/100000000000000 : ℝ), (2833768567911/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323844347/2500000000 : ℝ)|^4465 ≤ (21913007192043/50000000000000 : ℝ)^3441
        have hw : |(1323844347/2500000000 : ℝ)|=(1323844347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-90179967/500000000 : ℝ)|^4465 ≤ (10833688513963/100000000000000 : ℝ)^3441
        have hw : |(-90179967/500000000 : ℝ)|=(90179967/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435831669/10000000000 : ℝ)|^4465 ≤ (2833768567911/6250000000000 : ℝ)^3441
        have hw : |(5435831669/10000000000 : ℝ)|=(5435831669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s5_6 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295377397/10000000000 : ℝ)*x 0 + (169869741/312500000 : ℝ)*x 1 + (-450899817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295377397/10000000000 : ℝ)^4465 ≤ (43826014480739/100000000000000 : ℝ)^3441 := by
    have hnat : (5295377397 : ℕ)^4465*100000000000000^3441 ≤ 43826014480739^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295377397 10000000000 43826014480739 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169869741/312500000 : ℝ)^4465 ≤ (45340297551973/100000000000000 : ℝ)^3441 := by
    have hnat : (169869741 : ℕ)^4465*100000000000000^3441 ≤ 45340297551973^3441*312500000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169869741 312500000 45340297551973 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450899817/2500000000 : ℝ)^4465 ≤ (10833687952779/100000000000000 : ℝ)^3441 := by
    have hnat : (450899817 : ℕ)^4465*100000000000000^3441 ≤ 10833687952779^3441*2500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450899817 2500000000 10833687952779 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295377397/10000000000 : ℝ), (169869741/312500000 : ℝ), (-450899817/2500000000 : ℝ)] ![(43826014480739/100000000000000 : ℝ), (45340297551973/100000000000000 : ℝ), (10833687952779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295377397/10000000000 : ℝ)|^4465 ≤ (43826014480739/100000000000000 : ℝ)^3441
        have hw : |(5295377397/10000000000 : ℝ)|=(5295377397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169869741/312500000 : ℝ)|^4465 ≤ (45340297551973/100000000000000 : ℝ)^3441
        have hw : |(169869741/312500000 : ℝ)|=(169869741/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-450899817/2500000000 : ℝ)|^4465 ≤ (10833687952779/100000000000000 : ℝ)^3441
        have hw : |(-450899817/2500000000 : ℝ)|=(450899817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s5_7 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070763183/2500000000 : ℝ)*x 0 + (566519941/1250000000 : ℝ)*x 1 + (2023033929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070763183/2500000000 : ℝ)^4465 ≤ (33278802590533/100000000000000 : ℝ)^3441 := by
    have hnat : (1070763183 : ℕ)^4465*100000000000000^3441 ≤ 33278802590533^3441*2500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070763183 2500000000 33278802590533 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566519941/1250000000 : ℝ)^4465 ≤ (35811768414857/100000000000000 : ℝ)^3441 := by
    have hnat : (566519941 : ℕ)^4465*100000000000000^3441 ≤ 35811768414857^3441*1250000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566519941 1250000000 35811768414857 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2023033929/5000000000 : ℝ)^4465 ≤ (15454714491869/50000000000000 : ℝ)^3441 := by
    have hnat : (2023033929 : ℕ)^4465*50000000000000^3441 ≤ 15454714491869^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023033929 5000000000 15454714491869 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070763183/2500000000 : ℝ), (566519941/1250000000 : ℝ), (2023033929/5000000000 : ℝ)] ![(33278802590533/100000000000000 : ℝ), (35811768414857/100000000000000 : ℝ), (15454714491869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070763183/2500000000 : ℝ)|^4465 ≤ (33278802590533/100000000000000 : ℝ)^3441
        have hw : |(1070763183/2500000000 : ℝ)|=(1070763183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(566519941/1250000000 : ℝ)|^4465 ≤ (35811768414857/100000000000000 : ℝ)^3441
        have hw : |(566519941/1250000000 : ℝ)|=(566519941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2023033929/5000000000 : ℝ)|^4465 ≤ (15454714491869/50000000000000 : ℝ)^3441
        have hw : |(2023033929/5000000000 : ℝ)|=(2023033929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1484_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80572949/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10791/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5401/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7739/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10791/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10791/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10791/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10791/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10791/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10791/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10791/100000 : ℝ) ^ (4463/1024 : ℝ) ≤ (6105167611752399/100000000000000000000 : ℝ) := by
    have hpowers : (10791/100000 : ℝ)^4463 ≤ (6105167611752399/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10791 : ℕ)^4463*100000000000000000000^1024 ≤ 6105167611752399^1024*100000^4463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10791 100000 6105167611752399 100000000000000000000 4463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10791/100000 : ℝ)) (X := (6105167611752399/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4463/1024 : ℝ) ≤ (29498447789008239/100000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4463 ≤ (29498447789008239/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4463*100000000000000000000^1024 ≤ 29498447789008239^1024*100000^4463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 29498447789008239 100000000000000000000 4463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (29498447789008239/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006105167611752399/50000000000000000000 : ℝ) ≤ (10000280143291597/10000000000000000 : ℝ) ^ (4463/1024 : ℝ) := by
    have hpowers : (50006105167611752399/50000000000000000000 : ℝ)^1024 ≤ (10000280143291597/10000000000000000 : ℝ)^4463 := by
      have hnat : (50006105167611752399 : ℕ)^1024*10000000000000000^4463 ≤ 10000280143291597^4463*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006105167611752399 50000000000000000000 10000280143291597 10000000000000000 1024 4463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000280143291597/10000000000000000 : ℝ)) (X := (50006105167611752399/50000000000000000000 : ℝ)) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017801807700380319/50000000000000000000 : ℝ) ≤ (10000816784722049/10000000000000000 : ℝ) ^ (4463/1024 : ℝ) := by
    have hpowers : (50017801807700380319/50000000000000000000 : ℝ)^1024 ≤ (10000816784722049/10000000000000000 : ℝ)^4463 := by
      have hnat : (50017801807700380319 : ℕ)^1024*10000000000000000^4463 ≤ 10000816784722049^4463*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017801807700380319 50000000000000000000 10000816784722049 10000000000000000 1024 4463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000816784722049/10000000000000000 : ℝ)) (X := (50017801807700380319/50000000000000000000 : ℝ)) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029498447789008239/50000000000000000000 : ℝ) ≤ (10001353426152501/10000000000000000 : ℝ) ^ (4463/1024 : ℝ) := by
    have hpowers : (50029498447789008239/50000000000000000000 : ℝ)^1024 ≤ (10001353426152501/10000000000000000 : ℝ)^4463 := by
      have hnat : (50029498447789008239 : ℕ)^1024*10000000000000000^4463 ≤ 10001353426152501^4463*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029498447789008239 50000000000000000000 10001353426152501 10000000000000000 1024 4463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001353426152501/10000000000000000 : ℝ)) (X := (50029498447789008239/50000000000000000000 : ℝ)) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6105167611752399/100000000000000000000 : ℝ) ≤ ((2609429684323994869/2610000000000000000 : ℝ)+2*(134160357613/117450000000000 : ℝ)*(10791/100000 : ℝ))^(4463/1024 : ℝ) := by
    rw [show (2609429684323994869/2610000000000000000 : ℝ)+2*(134160357613/117450000000000 : ℝ)*(10791/100000 : ℝ)=(10000280143291597/10000000000000000 : ℝ) by norm_num, show 1+2*(6105167611752399/100000000000000000000 : ℝ)=(50006105167611752399/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29498447789008239/100000000000000000000 : ℝ)+(6105167611752399/100000000000000000000 : ℝ) ≤ ((2609429684323994869/2610000000000000000 : ℝ)+(134160357613/117450000000000 : ℝ)*((15489/100000 : ℝ)+(10791/100000 : ℝ)))^(4463/1024 : ℝ) := by
    rw [show (2609429684323994869/2610000000000000000 : ℝ)+(134160357613/117450000000000 : ℝ)*((15489/100000 : ℝ)+(10791/100000 : ℝ))=(10000816784722049/10000000000000000 : ℝ) by norm_num, show 1+(29498447789008239/100000000000000000000 : ℝ)+(6105167611752399/100000000000000000000 : ℝ)=(50017801807700380319/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29498447789008239/100000000000000000000 : ℝ) ≤ ((2609429684323994869/2610000000000000000 : ℝ)+2*(134160357613/117450000000000 : ℝ)*(15489/100000 : ℝ))^(4463/1024 : ℝ) := by
    rw [show (2609429684323994869/2610000000000000000 : ℝ)+2*(134160357613/117450000000000 : ℝ)*(15489/100000 : ℝ)=(10001353426152501/10000000000000000 : ℝ) by norm_num, show 1+2*(29498447789008239/100000000000000000000 : ℝ)=(50029498447789008239/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2609429684323994869/2610000000000000000 : ℝ)*(X 1 0+X 2 0)+(134160357613/117450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4463/1024 : ℝ)) (lo := (10791/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (2609429684323994869/2610000000000000000 : ℝ)) (alpha := (134160357613/117450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2609429684323994869/2610000000000000000 : ℝ)*(X 0 1+X 2 1)+(134160357613/117450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4463/1024 : ℝ)) (lo := (10791/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (2609429684323994869/2610000000000000000 : ℝ)) (alpha := (134160357613/117450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2609429684323994869/2610000000000000000 : ℝ)*(X 0 2+X 1 2)+(134160357613/117450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4463/1024 : ℝ)) (lo := (10791/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (2609429684323994869/2610000000000000000 : ℝ)) (alpha := (134160357613/117450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1910178781/10000000000 : ℝ)*X 0 0+(679621461/1250000000 : ℝ)*X 0 1+(1043205473/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353119047/10000000000 : ℝ)*X 1 0+(-40468079/200000000 : ℝ)*X 1 1+(2608013621/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334569953/625000000 : ℝ)*X 2 0+(521602711/1000000000 : ℝ)*X 2 1+(-2023403857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4282985769/10000000000 : ℝ)*X 0 0+(4043533141/10000000000 : ℝ)*X 0 1+(906935101/2000000000 : ℝ)*X 0 2+(4282985769/10000000000 : ℝ)*X 1 0+(4043533141/10000000000 : ℝ)*X 1 1+(906935101/2000000000 : ℝ)*X 1 2+(4282985769/10000000000 : ℝ)*X 2 0+(4043533141/10000000000 : ℝ)*X 2 1+(906935101/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-477552263/2500000000 : ℝ)*X 0 0+(163036217/312500000 : ℝ)*X 0 1+(1358957937/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323844347/2500000000 : ℝ)*X 1 0+(-90179967/500000000 : ℝ)*X 1 1+(5435831669/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295377397/10000000000 : ℝ)*X 2 0+(169869741/312500000 : ℝ)*X 2 1+(-450899817/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1070763183/2500000000 : ℝ)*X 0 0+(566519941/1250000000 : ℝ)*X 0 1+(2023033929/5000000000 : ℝ)*X 0 2+(1070763183/2500000000 : ℝ)*X 1 0+(566519941/1250000000 : ℝ)*X 1 1+(2023033929/5000000000 : ℝ)*X 1 2+(1070763183/2500000000 : ℝ)*X 2 0+(566519941/1250000000 : ℝ)*X 2 1+(2023033929/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4080692446075157107014751/1631250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (425087871/100000000000000 : ℝ)*(base19) + (81084797/20000000000000 : ℝ)*(base23) + (101499527/100000000000000 : ℝ)*(lower2) + (41409639/50000000000000 : ℝ)*(upper3) + (59053553/100000000000000 : ℝ)*(upper5) + (82026344200993/2500000000000 : ℝ)*(major0) + (82026344200993/2500000000000 : ℝ)*(major1) + (82026344200993/2500000000000 : ℝ)*(major2) + (4526027996312369/100000000000000 : ℝ)*(sp0) + (1131507630637407/25000000000000 : ℝ)*(sp1) + (2263015271106757/50000000000000 : ℝ)*(sp2) + (40721447280261/2000000000000 : ℝ)*(sp3) + (2951325131/100000000000000 : ℝ)*(sp4) + (4141043083/100000000000000 : ℝ)*(sp7) + (509019126264033/25000000000000 : ℝ)*(f.failure) + (4526030947637499/100000000000000 : ℝ)*(f.sum) + (9111791583799/2349000000000000000000000000 : ℝ)*base65 + (1073948677030105747/58725000000000000000000000000000 : ℝ)*base68 + (548914157548180747/58725000000000000000000000000000 : ℝ)*base70 + (322088820677305747/58725000000000000000000000000000 : ℝ)*base72 + (6991781242141/1174500000000000000000000000 : ℝ)*base74 + (748163930866855747/58725000000000000000000000000000 : ℝ)*base76 + (167116681981594253/58725000000000000000000000000000 : ℝ)*base77 + (247484386415005747/58725000000000000000000000000000 : ℝ)*base80 + (451131087179/234900000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (8556683/1250000000000000000000 : ℝ)*base90 + (8556683/1250000000000000000000 : ℝ)*base92 + (8556683/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (469296264855310477508888867/65250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1233761021/100000000000000 : ℝ)*(base19) + (280055247/20000000000000 : ℝ)*(base23) + (149572351/100000000000000 : ℝ)*(upper3) + (64976153/100000000000000 : ℝ)*(lower4) + (3926233/2500000000000 : ℝ)*(upper5) + (1657566671941727/50000000000000 : ℝ)*(major0) + (1657566671941727/50000000000000 : ℝ)*(major1) + (1657566671941727/50000000000000 : ℝ)*(major2) + (17170260111/100000000000000 : ℝ)*(sp1) + (20475292917/100000000000000 : ℝ)*(sp2) + (14290755215923/312500000000 : ℝ)*(sp4) + (1143255816268557/25000000000000 : ℝ)*(sp5) + (71453434273847/1562500000000 : ℝ)*(sp6) + (1028612389464439/50000000000000 : ℝ)*(sp7) + (1028612389464439/50000000000000 : ℝ)*(f.failure) + (14290755215923/312500000000 : ℝ)*(f.sum) + (4621460866879/2936250000000000000000000000 : ℝ)*base66 + (8129965040622811133/1174500000000000000000000000000000 : ℝ)*base68 + (11435646005532811133/1174500000000000000000000000000000 : ℝ)*base70 + (4338368917421311133/1174500000000000000000000000000000 : ℝ)*base72 + (24728737342913/5872500000000000000000000000 : ℝ)*base74 + (3299392523925811133/1174500000000000000000000000000000 : ℝ)*base76 + (6652012134690811133/1174500000000000000000000000000000 : ℝ)*base78 + (6015381294609811133/1174500000000000000000000000000000 : ℝ)*base80 + (88547243550091/11745000000000000000000000000 : ℝ)*base82 + (30860611/2500000000000000000000 : ℝ)*base89 + (30860611/2500000000000000000000 : ℝ)*base91 + (30860611/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1484_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80572949/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10791/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5401/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1484_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1484_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80572949/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5401/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1484_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1484_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1484_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80572949/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5401/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1484_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

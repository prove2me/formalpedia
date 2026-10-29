-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1627_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:59:11.704063+00:00
-- url     : https://prove2.me/submissions/b5be5a97-0909-499e-bd1f-b5b6cadb59d1

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
theorem support_rectangle_w1627_s3_0 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1662340139/10000000000 : ℝ)*x 0 + (5454620047/10000000000 : ℝ)*x 1 + (259101521/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1662340139/10000000000 : ℝ)^4827 ≤ (2050784660997/20000000000000 : ℝ)^3803 := by
    have hnat : (1662340139 : ℕ)^4827*20000000000000^3803 ≤ 2050784660997^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1662340139 10000000000 2050784660997 20000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5454620047/10000000000 : ℝ)^4827 ≤ (46332466735453/100000000000000 : ℝ)^3803 := by
    have hnat : (5454620047 : ℕ)^4827*100000000000000^3803 ≤ 46332466735453^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454620047 10000000000 46332466735453 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259101521/500000000 : ℝ)^4827 ≤ (43413609949009/100000000000000 : ℝ)^3803 := by
    have hnat : (259101521 : ℕ)^4827*100000000000000^3803 ≤ 43413609949009^3803*500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259101521 500000000 43413609949009 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1662340139/10000000000 : ℝ), (5454620047/10000000000 : ℝ), (259101521/500000000 : ℝ)] ![(2050784660997/20000000000000 : ℝ), (46332466735453/100000000000000 : ℝ), (43413609949009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1662340139/10000000000 : ℝ)|^4827 ≤ (2050784660997/20000000000000 : ℝ)^3803
        have hw : |(-1662340139/10000000000 : ℝ)|=(1662340139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5454620047/10000000000 : ℝ)|^4827 ≤ (46332466735453/100000000000000 : ℝ)^3803
        have hw : |(5454620047/10000000000 : ℝ)|=(5454620047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259101521/500000000 : ℝ)|^4827 ≤ (43413609949009/100000000000000 : ℝ)^3803
        have hw : |(259101521/500000000 : ℝ)|=(259101521/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s3_1 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070242593/2000000000 : ℝ)*x 0 + (-1802805877/10000000000 : ℝ)*x 1 + (1295507601/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070242593/2000000000 : ℝ)^4827 ≤ (45220460711623/100000000000000 : ℝ)^3803 := by
    have hnat : (1070242593 : ℕ)^4827*100000000000000^3803 ≤ 45220460711623^3803*2000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070242593 2000000000 45220460711623 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1802805877/10000000000 : ℝ)^4827 ≤ (11365929499797/100000000000000 : ℝ)^3803 := by
    have hnat : (1802805877 : ℕ)^4827*100000000000000^3803 ≤ 11365929499797^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1802805877 10000000000 11365929499797 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295507601/2500000000 : ℝ)^4827 ≤ (5426701222359/12500000000000 : ℝ)^3803 := by
    have hnat : (1295507601 : ℕ)^4827*12500000000000^3803 ≤ 5426701222359^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295507601 2500000000 5426701222359 12500000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070242593/2000000000 : ℝ), (-1802805877/10000000000 : ℝ), (1295507601/2500000000 : ℝ)] ![(45220460711623/100000000000000 : ℝ), (11365929499797/100000000000000 : ℝ), (5426701222359/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070242593/2000000000 : ℝ)|^4827 ≤ (45220460711623/100000000000000 : ℝ)^3803
        have hw : |(1070242593/2000000000 : ℝ)|=(1070242593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1802805877/10000000000 : ℝ)|^4827 ≤ (11365929499797/100000000000000 : ℝ)^3803
        have hw : |(-1802805877/10000000000 : ℝ)|=(1802805877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295507601/2500000000 : ℝ)|^4827 ≤ (5426701222359/12500000000000 : ℝ)^3803
        have hw : |(1295507601/2500000000 : ℝ)|=(1295507601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s3_2 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351212877/10000000000 : ℝ)*x 0 + (5182030647/10000000000 : ℝ)*x 1 + (-1802805671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351212877/10000000000 : ℝ)^4827 ≤ (706569683871/1562500000000 : ℝ)^3803 := by
    have hnat : (5351212877 : ℕ)^4827*1562500000000^3803 ≤ 706569683871^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351212877 10000000000 706569683871 1562500000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182030647/10000000000 : ℝ)^4827 ≤ (43413612362817/100000000000000 : ℝ)^3803 := by
    have hnat : (5182030647 : ℕ)^4827*100000000000000^3803 ≤ 43413612362817^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182030647 10000000000 43413612362817 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1802805671/10000000000 : ℝ)^4827 ≤ (11365927851353/100000000000000 : ℝ)^3803 := by
    have hnat : (1802805671 : ℕ)^4827*100000000000000^3803 ≤ 11365927851353^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1802805671 10000000000 11365927851353 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351212877/10000000000 : ℝ), (5182030647/10000000000 : ℝ), (-1802805671/10000000000 : ℝ)] ![(706569683871/1562500000000 : ℝ), (43413612362817/100000000000000 : ℝ), (11365927851353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351212877/10000000000 : ℝ)|^4827 ≤ (706569683871/1562500000000 : ℝ)^3803
        have hw : |(5351212877/10000000000 : ℝ)|=(5351212877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182030647/10000000000 : ℝ)|^4827 ≤ (43413612362817/100000000000000 : ℝ)^3803
        have hw : |(5182030647/10000000000 : ℝ)|=(5182030647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1802805671/10000000000 : ℝ)|^4827 ≤ (11365927851353/100000000000000 : ℝ)^3803
        have hw : |(-1802805671/10000000000 : ℝ)|=(1802805671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s3_3 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (209935017/500000000 : ℝ)*x 0 + (3866746901/10000000000 : ℝ)*x 1 + (4551610957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209935017/500000000 : ℝ)^4827 ≤ (33237961062699/100000000000000 : ℝ)^3803 := by
    have hnat : (209935017 : ℕ)^4827*100000000000000^3803 ≤ 33237961062699^3803*500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209935017 500000000 33237961062699 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3866746901/10000000000 : ℝ)^4827 ≤ (14969386721903/50000000000000 : ℝ)^3803 := by
    have hnat : (3866746901 : ℕ)^4827*50000000000000^3803 ≤ 14969386721903^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3866746901 10000000000 14969386721903 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4551610957/10000000000 : ℝ)^4827 ≤ (36823265472971/100000000000000 : ℝ)^3803 := by
    have hnat : (4551610957 : ℕ)^4827*100000000000000^3803 ≤ 36823265472971^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4551610957 10000000000 36823265472971 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209935017/500000000 : ℝ), (3866746901/10000000000 : ℝ), (4551610957/10000000000 : ℝ)] ![(33237961062699/100000000000000 : ℝ), (14969386721903/50000000000000 : ℝ), (36823265472971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209935017/500000000 : ℝ)|^4827 ≤ (33237961062699/100000000000000 : ℝ)^3803
        have hw : |(209935017/500000000 : ℝ)|=(209935017/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3866746901/10000000000 : ℝ)|^4827 ≤ (14969386721903/50000000000000 : ℝ)^3803
        have hw : |(3866746901/10000000000 : ℝ)|=(3866746901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4551610957/10000000000 : ℝ)|^4827 ≤ (36823265472971/100000000000000 : ℝ)^3803
        have hw : |(4551610957/10000000000 : ℝ)|=(4551610957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s3_4 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1662408299/10000000000 : ℝ)*x 0 + (162002377/312500000 : ℝ)*x 1 + (5452552737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1662408299/10000000000 : ℝ)^4827 ≤ (5127228475411/50000000000000 : ℝ)^3803 := by
    have hnat : (1662408299 : ℕ)^4827*50000000000000^3803 ≤ 5127228475411^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1662408299 10000000000 5127228475411 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162002377/312500000 : ℝ)^4827 ≤ (43435363494487/100000000000000 : ℝ)^3803 := by
    have hnat : (162002377 : ℕ)^4827*100000000000000^3803 ≤ 43435363494487^3803*312500000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162002377 312500000 43435363494487 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452552737/10000000000 : ℝ)^4827 ≤ (23155089772237/50000000000000 : ℝ)^3803 := by
    have hnat : (5452552737 : ℕ)^4827*50000000000000^3803 ≤ 23155089772237^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452552737 10000000000 23155089772237 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1662408299/10000000000 : ℝ), (162002377/312500000 : ℝ), (5452552737/10000000000 : ℝ)] ![(5127228475411/50000000000000 : ℝ), (43435363494487/100000000000000 : ℝ), (23155089772237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1662408299/10000000000 : ℝ)|^4827 ≤ (5127228475411/50000000000000 : ℝ)^3803
        have hw : |(-1662408299/10000000000 : ℝ)|=(1662408299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162002377/312500000 : ℝ)|^4827 ≤ (43435363494487/100000000000000 : ℝ)^3803
        have hw : |(162002377/312500000 : ℝ)|=(162002377/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452552737/10000000000 : ℝ)|^4827 ≤ (23155089772237/50000000000000 : ℝ)^3803
        have hw : |(5452552737/10000000000 : ℝ)|=(5452552737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s3_5 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278614969/10000000000 : ℝ)*x 0 + (-153228333/1000000000 : ℝ)*x 1 + (2726276409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278614969/10000000000 : ℝ)^4827 ≤ (44443208879611/100000000000000 : ℝ)^3803 := by
    have hnat : (5278614969 : ℕ)^4827*100000000000000^3803 ≤ 44443208879611^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278614969 10000000000 44443208879611 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (153228333/1000000000 : ℝ)^4827 ≤ (2311652671227/25000000000000 : ℝ)^3803 := by
    have hnat : (153228333 : ℕ)^4827*25000000000000^3803 ≤ 2311652671227^3803*1000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153228333 1000000000 2311652671227 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2726276409/5000000000 : ℝ)^4827 ≤ (46310180417671/100000000000000 : ℝ)^3803 := by
    have hnat : (2726276409 : ℕ)^4827*100000000000000^3803 ≤ 46310180417671^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726276409 5000000000 46310180417671 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278614969/10000000000 : ℝ), (-153228333/1000000000 : ℝ), (2726276409/5000000000 : ℝ)] ![(44443208879611/100000000000000 : ℝ), (2311652671227/25000000000000 : ℝ), (46310180417671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278614969/10000000000 : ℝ)|^4827 ≤ (44443208879611/100000000000000 : ℝ)^3803
        have hw : |(5278614969/10000000000 : ℝ)|=(5278614969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-153228333/1000000000 : ℝ)|^4827 ≤ (2311652671227/25000000000000 : ℝ)^3803
        have hw : |(-153228333/1000000000 : ℝ)|=(153228333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2726276409/5000000000 : ℝ)|^4827 ≤ (46310180417671/100000000000000 : ℝ)^3803
        have hw : |(2726276409/5000000000 : ℝ)|=(2726276409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s3_6 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639307469/5000000000 : ℝ)*x 0 + (2726276391/5000000000 : ℝ)*x 1 + (-61291337/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639307469/5000000000 : ℝ)^4827 ≤ (5555401068541/12500000000000 : ℝ)^3803 := by
    have hnat : (2639307469 : ℕ)^4827*12500000000000^3803 ≤ 5555401068541^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639307469 5000000000 5555401068541 12500000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2726276391/5000000000 : ℝ)^4827 ≤ (46310180029583/100000000000000 : ℝ)^3803 := by
    have hnat : (2726276391 : ℕ)^4827*100000000000000^3803 ≤ 46310180029583^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726276391 5000000000 46310180029583 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (61291337/400000000 : ℝ)^4827 ≤ (9246611412551/100000000000000 : ℝ)^3803 := by
    have hnat : (61291337 : ℕ)^4827*100000000000000^3803 ≤ 9246611412551^3803*400000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61291337 400000000 9246611412551 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639307469/5000000000 : ℝ), (2726276391/5000000000 : ℝ), (-61291337/400000000 : ℝ)] ![(5555401068541/12500000000000 : ℝ), (46310180029583/100000000000000 : ℝ), (9246611412551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639307469/5000000000 : ℝ)|^4827 ≤ (5555401068541/12500000000000 : ℝ)^3803
        have hw : |(2639307469/5000000000 : ℝ)|=(2639307469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2726276391/5000000000 : ℝ)|^4827 ≤ (46310180029583/100000000000000 : ℝ)^3803
        have hw : |(2726276391/5000000000 : ℝ)|=(2726276391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-61291337/400000000 : ℝ)|^4827 ≤ (9246611412551/100000000000000 : ℝ)^3803
        have hw : |(-61291337/400000000 : ℝ)|=(61291337/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s3_7 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4198871253/10000000000 : ℝ)*x 0 + (4546471311/10000000000 : ℝ)*x 1 + (483992593/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4198871253/10000000000 : ℝ)^4827 ≤ (33239678369719/100000000000000 : ℝ)^3803 := by
    have hnat : (4198871253 : ℕ)^4827*100000000000000^3803 ≤ 33239678369719^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4198871253 10000000000 33239678369719 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4546471311/10000000000 : ℝ)^4827 ≤ (9192624226531/25000000000000 : ℝ)^3803 := by
    have hnat : (4546471311 : ℕ)^4827*25000000000000^3803 ≤ 9192624226531^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4546471311 10000000000 9192624226531 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (483992593/1250000000 : ℝ)^4827 ≤ (29989824714023/100000000000000 : ℝ)^3803 := by
    have hnat : (483992593 : ℕ)^4827*100000000000000^3803 ≤ 29989824714023^3803*1250000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483992593 1250000000 29989824714023 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4198871253/10000000000 : ℝ), (4546471311/10000000000 : ℝ), (483992593/1250000000 : ℝ)] ![(33239678369719/100000000000000 : ℝ), (9192624226531/25000000000000 : ℝ), (29989824714023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4198871253/10000000000 : ℝ)|^4827 ≤ (33239678369719/100000000000000 : ℝ)^3803
        have hw : |(4198871253/10000000000 : ℝ)|=(4198871253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4546471311/10000000000 : ℝ)|^4827 ≤ (9192624226531/25000000000000 : ℝ)^3803
        have hw : |(4546471311/10000000000 : ℝ)|=(4546471311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(483992593/1250000000 : ℝ)|^4827 ≤ (29989824714023/100000000000000 : ℝ)^3803
        have hw : |(483992593/1250000000 : ℝ)|=(483992593/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1627_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8213/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10439/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5267/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (102/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8213/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10439/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8213/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10439/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8213/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10439/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8213/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10439/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8213/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10439/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8213/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10439/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10439/100000 : ℝ) ^ (4823/1024 : ℝ) ≤ (2387381044299319/100000000000000000000 : ℝ) := by
    have hpowers : (10439/100000 : ℝ)^4823 ≤ (2387381044299319/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10439 : ℕ)^4823*100000000000000000000^1024 ≤ 2387381044299319^1024*100000^4823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10439 100000 2387381044299319 100000000000000000000 4823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10439/100000 : ℝ)) (X := (2387381044299319/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8213/50000 : ℝ) ^ (4823/1024 : ℝ) ≤ (20192286906819083/100000000000000000000 : ℝ) := by
    have hpowers : (8213/50000 : ℝ)^4823 ≤ (20192286906819083/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8213 : ℕ)^4823*100000000000000000000^1024 ≤ 20192286906819083^1024*50000^4823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8213 50000 20192286906819083 100000000000000000000 4823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8213/50000 : ℝ)) (X := (20192286906819083/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002387381044299319/50000000000000000000 : ℝ) ≤ (10000101373925709/10000000000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (50002387381044299319/50000000000000000000 : ℝ)^1024 ≤ (10000101373925709/10000000000000000 : ℝ)^4823 := by
      have hnat : (50002387381044299319 : ℕ)^1024*10000000000000000^4823 ≤ 10000101373925709^4823*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002387381044299319 50000000000000000000 10000101373925709 10000000000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000101373925709/10000000000000000 : ℝ)) (X := (50002387381044299319/50000000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50011289833975559201/50000000000000000000 : ℝ) ≤ (5000239679909783/5000000000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (50011289833975559201/50000000000000000000 : ℝ)^1024 ≤ (5000239679909783/5000000000000000 : ℝ)^4823 := by
      have hnat : (50011289833975559201 : ℕ)^1024*5000000000000000^4823 ≤ 5000239679909783^4823*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011289833975559201 50000000000000000000 5000239679909783 5000000000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000239679909783/5000000000000000 : ℝ)) (X := (50011289833975559201/50000000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020192286906819083/50000000000000000000 : ℝ) ≤ (10000857345713423/10000000000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (50020192286906819083/50000000000000000000 : ℝ)^1024 ≤ (10000857345713423/10000000000000000 : ℝ)^4823 := by
      have hnat : (50020192286906819083 : ℕ)^1024*10000000000000000^4823 ≤ 10000857345713423^4823*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020192286906819083 50000000000000000000 10000857345713423 10000000000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000857345713423/10000000000000000 : ℝ)) (X := (50020192286906819083/50000000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2387381044299319/100000000000000000000 : ℝ) ≤ ((59862715336201273337/59870000000000000000 : ℝ)+2*(377985893857/598700000000000 : ℝ)*(10439/100000 : ℝ))^(4823/1024 : ℝ) := by
    rw [show (59862715336201273337/59870000000000000000 : ℝ)+2*(377985893857/598700000000000 : ℝ)*(10439/100000 : ℝ)=(10000101373925709/10000000000000000 : ℝ) by norm_num, show 1+2*(2387381044299319/100000000000000000000 : ℝ)=(50002387381044299319/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20192286906819083/100000000000000000000 : ℝ)+(2387381044299319/100000000000000000000 : ℝ) ≤ ((59862715336201273337/59870000000000000000 : ℝ)+(377985893857/598700000000000 : ℝ)*((8213/50000 : ℝ)+(10439/100000 : ℝ)))^(4823/1024 : ℝ) := by
    rw [show (59862715336201273337/59870000000000000000 : ℝ)+(377985893857/598700000000000 : ℝ)*((8213/50000 : ℝ)+(10439/100000 : ℝ))=(5000239679909783/5000000000000000 : ℝ) by norm_num, show 1+(20192286906819083/100000000000000000000 : ℝ)+(2387381044299319/100000000000000000000 : ℝ)=(50011289833975559201/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20192286906819083/100000000000000000000 : ℝ) ≤ ((59862715336201273337/59870000000000000000 : ℝ)+2*(377985893857/598700000000000 : ℝ)*(8213/50000 : ℝ))^(4823/1024 : ℝ) := by
    rw [show (59862715336201273337/59870000000000000000 : ℝ)+2*(377985893857/598700000000000 : ℝ)*(8213/50000 : ℝ)=(10000857345713423/10000000000000000 : ℝ) by norm_num, show 1+2*(20192286906819083/100000000000000000000 : ℝ)=(50020192286906819083/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (59862715336201273337/59870000000000000000 : ℝ)*(X 1 0+X 2 0)+(377985893857/598700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (10439/100000 : ℝ)) (hi := (8213/50000 : ℝ)) (c := (59862715336201273337/59870000000000000000 : ℝ)) (alpha := (377985893857/598700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (59862715336201273337/59870000000000000000 : ℝ)*(X 0 1+X 2 1)+(377985893857/598700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (10439/100000 : ℝ)) (hi := (8213/50000 : ℝ)) (c := (59862715336201273337/59870000000000000000 : ℝ)) (alpha := (377985893857/598700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (59862715336201273337/59870000000000000000 : ℝ)*(X 0 2+X 1 2)+(377985893857/598700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (10439/100000 : ℝ)) (hi := (8213/50000 : ℝ)) (c := (59862715336201273337/59870000000000000000 : ℝ)) (alpha := (377985893857/598700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1662340139/10000000000 : ℝ)*X 0 0+(5454620047/10000000000 : ℝ)*X 0 1+(259101521/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070242593/2000000000 : ℝ)*X 1 0+(-1802805877/10000000000 : ℝ)*X 1 1+(1295507601/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351212877/10000000000 : ℝ)*X 2 0+(5182030647/10000000000 : ℝ)*X 2 1+(-1802805671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((209935017/500000000 : ℝ)*X 0 0+(3866746901/10000000000 : ℝ)*X 0 1+(4551610957/10000000000 : ℝ)*X 0 2+(209935017/500000000 : ℝ)*X 1 0+(3866746901/10000000000 : ℝ)*X 1 1+(4551610957/10000000000 : ℝ)*X 1 2+(209935017/500000000 : ℝ)*X 2 0+(3866746901/10000000000 : ℝ)*X 2 1+(4551610957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1662408299/10000000000 : ℝ)*X 0 0+(162002377/312500000 : ℝ)*X 0 1+(5452552737/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278614969/10000000000 : ℝ)*X 1 0+(-153228333/1000000000 : ℝ)*X 1 1+(2726276409/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639307469/5000000000 : ℝ)*X 2 0+(2726276391/5000000000 : ℝ)*X 2 1+(-61291337/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4198871253/10000000000 : ℝ)*X 0 0+(4546471311/10000000000 : ℝ)*X 0 1+(483992593/1250000000 : ℝ)*X 0 2+(4198871253/10000000000 : ℝ)*X 1 0+(4546471311/10000000000 : ℝ)*X 1 1+(483992593/1250000000 : ℝ)*X 1 2+(4198871253/10000000000 : ℝ)*X 2 0+(4546471311/10000000000 : ℝ)*X 2 1+(483992593/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32383785145989397657635992523/2993500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76934753/5000000000000 : ℝ)*(base19) + (1313382653/100000000000000 : ℝ)*(base23) + (88286189/100000000000000 : ℝ)*(lower2) + (9993583/5000000000000 : ℝ)*(upper3) + (2294981/1000000000000 : ℝ)*(upper5) + (2564357276466593/100000000000000 : ℝ)*(major0) + (2564357276466593/100000000000000 : ℝ)*(major1) + (2564357276466593/100000000000000 : ℝ)*(major2) + (917133968121947/25000000000000 : ℝ)*(sp0) + (3668554132427429/100000000000000 : ℝ)*(sp1) + (917138589434959/25000000000000 : ℝ)*(sp2) + (1460151061637747/100000000000000 : ℝ)*(sp3) + (19798634701/100000000000000 : ℝ)*(sp4) + (3729785903/50000000000000 : ℝ)*(sp7) + (730079260604777/50000000000000 : ℝ)*(f.failure) + (3668555671122489/100000000000000 : ℝ)*(f.sum) + (4634257421309/1870937500000000000000000000 : ℝ)*base66 + (12210943761368769159/5987000000000000000000000000000000 : ℝ)*base68 + (7825361650517769159/5987000000000000000000000000000000 : ℝ)*base70 + (25095154974858769159/5987000000000000000000000000000000 : ℝ)*base72 + (3687376564599/29935000000000000000000000000 : ℝ)*base74 + (33447138113829230841/5987000000000000000000000000000000 : ℝ)*base75 + (25290637631427769159/5987000000000000000000000000000000 : ℝ)*base78 + (81884514109527230841/5987000000000000000000000000000000 : ℝ)*base79 + (1109858475589/7483750000000000000000000000 : ℝ)*base81 + (60134457/5000000000000000000000 : ℝ)*base89 + (60134457/5000000000000000000000 : ℝ)*base91 + (60134457/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7869789974032237833005816307/748375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1607187289/100000000000000 : ℝ)*(base19) + (823486497/50000000000000 : ℝ)*(base23) + (227628261/100000000000000 : ℝ)*(upper3) + (37436783/100000000000000 : ℝ)*(lower4) + (237106837/100000000000000 : ℝ)*(upper5) + (1301807608893063/50000000000000 : ℝ)*(major0) + (1301807608893063/50000000000000 : ℝ)*(major1) + (1301807608893063/50000000000000 : ℝ)*(major2) + (985873731/5000000000000 : ℝ)*(sp1) + (4761019933/25000000000000 : ℝ)*(sp2) + (372471788555877/10000000000000 : ℝ)*(sp4) + (1862348280448431/50000000000000 : ℝ)*(sp5) + (931174298626511/25000000000000 : ℝ)*(sp6) + (370628049871389/25000000000000 : ℝ)*(sp7) + (370628049871389/25000000000000 : ℝ)*(f.failure) + (372471788555877/10000000000000 : ℝ)*(f.sum) + (4479394475363/7483750000000000000000000000 : ℝ)*base65 + (17050038312839261231/2993500000000000000000000000000000 : ℝ)*base67 + (38140197871566261231/2993500000000000000000000000000000 : ℝ)*base69 + (7227370821164261231/2993500000000000000000000000000000 : ℝ)*base71 + (25612278595239/14967500000000000000000000000 : ℝ)*base74 + (22645663770744738769/2993500000000000000000000000000000 : ℝ)*base76 + (11831317968441261231/2993500000000000000000000000000000 : ℝ)*base77 + (18123867435097261231/2993500000000000000000000000000000 : ℝ)*base79 + (53416404649731/14967500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (592851/2500000000000000000000 : ℝ)*base90 + (592851/2500000000000000000000 : ℝ)*base92 + (592851/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1627_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8213/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10439/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5267/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (102/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1627_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1627_s4_0 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-831209117/5000000000 : ℝ)*x 0 + (1363557053/2500000000 : ℝ)*x 1 + (2591185097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (831209117/5000000000 : ℝ)^4827 ≤ (5127267367759/50000000000000 : ℝ)^3803 := by
    have hnat : (831209117 : ℕ)^4827*50000000000000^3803 ≤ 5127267367759^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831209117 5000000000 5127267367759 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363557053/2500000000 : ℝ)^4827 ≤ (46328242278223/100000000000000 : ℝ)^3803 := by
    have hnat : (1363557053 : ℕ)^4827*100000000000000^3803 ≤ 46328242278223^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363557053 2500000000 46328242278223 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591185097/5000000000 : ℝ)^4827 ≤ (43417222973387/100000000000000 : ℝ)^3803 := by
    have hnat : (2591185097 : ℕ)^4827*100000000000000^3803 ≤ 43417222973387^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591185097 5000000000 43417222973387 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-831209117/5000000000 : ℝ), (1363557053/2500000000 : ℝ), (2591185097/5000000000 : ℝ)] ![(5127267367759/50000000000000 : ℝ), (46328242278223/100000000000000 : ℝ), (43417222973387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-831209117/5000000000 : ℝ)|^4827 ≤ (5127267367759/50000000000000 : ℝ)^3803
        have hw : |(-831209117/5000000000 : ℝ)|=(831209117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363557053/2500000000 : ℝ)|^4827 ≤ (46328242278223/100000000000000 : ℝ)^3803
        have hw : |(1363557053/2500000000 : ℝ)|=(1363557053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591185097/5000000000 : ℝ)|^4827 ≤ (43417222973387/100000000000000 : ℝ)^3803
        have hw : |(2591185097/5000000000 : ℝ)|=(2591185097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s4_1 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267555383/500000000 : ℝ)*x 0 + (-1802495773/10000000000 : ℝ)*x 1 + (259118499/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267555383/500000000 : ℝ)^4827 ≤ (1808773248951/4000000000000 : ℝ)^3803 := by
    have hnat : (267555383 : ℕ)^4827*4000000000000^3803 ≤ 1808773248951^3803*500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267555383 500000000 1808773248951 4000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1802495773/10000000000 : ℝ)^4827 ≤ (11363448056953/100000000000000 : ℝ)^3803 := by
    have hnat : (1802495773 : ℕ)^4827*100000000000000^3803 ≤ 11363448056953^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1802495773 10000000000 11363448056953 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259118499/500000000 : ℝ)^4827 ≤ (21708610348887/50000000000000 : ℝ)^3803 := by
    have hnat : (259118499 : ℕ)^4827*50000000000000^3803 ≤ 21708610348887^3803*500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259118499 500000000 21708610348887 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267555383/500000000 : ℝ), (-1802495773/10000000000 : ℝ), (259118499/500000000 : ℝ)] ![(1808773248951/4000000000000 : ℝ), (11363448056953/100000000000000 : ℝ), (21708610348887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267555383/500000000 : ℝ)|^4827 ≤ (1808773248951/4000000000000 : ℝ)^3803
        have hw : |(267555383/500000000 : ℝ)|=(267555383/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1802495773/10000000000 : ℝ)|^4827 ≤ (11363448056953/100000000000000 : ℝ)^3803
        have hw : |(-1802495773/10000000000 : ℝ)|=(1802495773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259118499/500000000 : ℝ)|^4827 ≤ (21708610348887/50000000000000 : ℝ)^3803
        have hw : |(259118499/500000000 : ℝ)|=(259118499/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s4_2 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351107491/10000000000 : ℝ)*x 0 + (5182370171/10000000000 : ℝ)*x 1 + (-1802495747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351107491/10000000000 : ℝ)^4827 ≤ (11304832352777/25000000000000 : ℝ)^3803 := by
    have hnat : (5351107491 : ℕ)^4827*25000000000000^3803 ≤ 11304832352777^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351107491 10000000000 11304832352777 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182370171/10000000000 : ℝ)^4827 ≤ (10854305682203/25000000000000 : ℝ)^3803 := by
    have hnat : (5182370171 : ℕ)^4827*25000000000000^3803 ≤ 10854305682203^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182370171 10000000000 10854305682203 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1802495747/10000000000 : ℝ)^4827 ≤ (5681723924453/50000000000000 : ℝ)^3803 := by
    have hnat : (1802495747 : ℕ)^4827*50000000000000^3803 ≤ 5681723924453^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1802495747 10000000000 5681723924453 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351107491/10000000000 : ℝ), (5182370171/10000000000 : ℝ), (-1802495747/10000000000 : ℝ)] ![(11304832352777/25000000000000 : ℝ), (10854305682203/25000000000000 : ℝ), (5681723924453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351107491/10000000000 : ℝ)|^4827 ≤ (11304832352777/25000000000000 : ℝ)^3803
        have hw : |(5351107491/10000000000 : ℝ)|=(5351107491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182370171/10000000000 : ℝ)|^4827 ≤ (10854305682203/25000000000000 : ℝ)^3803
        have hw : |(5182370171/10000000000 : ℝ)|=(5182370171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1802495747/10000000000 : ℝ)|^4827 ≤ (5681723924453/50000000000000 : ℝ)^3803
        have hw : |(-1802495747/10000000000 : ℝ)|=(1802495747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s4_3 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4198751131/10000000000 : ℝ)*x 0 + (3867660237/10000000000 : ℝ)*x 1 + (35552243/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4198751131/10000000000 : ℝ)^4827 ≤ (1038702231273/3125000000000 : ℝ)^3803 := by
    have hnat : (4198751131 : ℕ)^4827*3125000000000^3803 ≤ 1038702231273^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4198751131 10000000000 1038702231273 3125000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3867660237/10000000000 : ℝ)^4827 ≤ (1497387472989/5000000000000 : ℝ)^3803 := by
    have hnat : (3867660237 : ℕ)^4827*5000000000000^3803 ≤ 1497387472989^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3867660237 10000000000 1497387472989 5000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35552243/78125000 : ℝ)^4827 ≤ (36813779122989/100000000000000 : ℝ)^3803 := by
    have hnat : (35552243 : ℕ)^4827*100000000000000^3803 ≤ 36813779122989^3803*78125000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35552243 78125000 36813779122989 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4198751131/10000000000 : ℝ), (3867660237/10000000000 : ℝ), (35552243/78125000 : ℝ)] ![(1038702231273/3125000000000 : ℝ), (1497387472989/5000000000000 : ℝ), (36813779122989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4198751131/10000000000 : ℝ)|^4827 ≤ (1038702231273/3125000000000 : ℝ)^3803
        have hw : |(4198751131/10000000000 : ℝ)|=(4198751131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3867660237/10000000000 : ℝ)|^4827 ≤ (1497387472989/5000000000000 : ℝ)^3803
        have hw : |(3867660237/10000000000 : ℝ)|=(3867660237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35552243/78125000 : ℝ)|^4827 ≤ (36813779122989/100000000000000 : ℝ)^3803
        have hw : |(35552243/78125000 : ℝ)|=(35552243/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s4_4 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-166248601/1000000000 : ℝ)*x 0 + (40503163/78125000 : ℝ)*x 1 + (5452171931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166248601/1000000000 : ℝ)^4827 ≤ (2051013076319/20000000000000 : ℝ)^3803 := by
    have hnat : (166248601 : ℕ)^4827*20000000000000^3803 ≤ 2051013076319^3803*1000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166248601 1000000000 2051013076319 20000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40503163/78125000 : ℝ)^4827 ≤ (10859715049049/25000000000000 : ℝ)^3803 := by
    have hnat : (40503163 : ℕ)^4827*25000000000000^3803 ≤ 10859715049049^3803*78125000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40503163 78125000 10859715049049 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452171931/10000000000 : ℝ)^4827 ≤ (11576518602797/25000000000000 : ℝ)^3803 := by
    have hnat : (5452171931 : ℕ)^4827*25000000000000^3803 ≤ 11576518602797^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452171931 10000000000 11576518602797 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-166248601/1000000000 : ℝ), (40503163/78125000 : ℝ), (5452171931/10000000000 : ℝ)] ![(2051013076319/20000000000000 : ℝ), (10859715049049/25000000000000 : ℝ), (11576518602797/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-166248601/1000000000 : ℝ)|^4827 ≤ (2051013076319/20000000000000 : ℝ)^3803
        have hw : |(-166248601/1000000000 : ℝ)|=(166248601/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40503163/78125000 : ℝ)|^4827 ≤ (10859715049049/25000000000000 : ℝ)^3803
        have hw : |(40503163/78125000 : ℝ)|=(40503163/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452171931/10000000000 : ℝ)|^4827 ≤ (11576518602797/25000000000000 : ℝ)^3803
        have hw : |(5452171931/10000000000 : ℝ)|=(5452171931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s4_5 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639352511/5000000000 : ℝ)*x 0 + (-47896681/312500000 : ℝ)*x 1 + (5452171899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639352511/5000000000 : ℝ)^4827 ≤ (22222085617607/50000000000000 : ℝ)^3803 := by
    have hnat : (2639352511 : ℕ)^4827*50000000000000^3803 ≤ 22222085617607^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639352511 5000000000 22222085617607 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47896681/312500000 : ℝ)^4827 ≤ (924975468889/10000000000000 : ℝ)^3803 := by
    have hnat : (47896681 : ℕ)^4827*10000000000000^3803 ≤ 924975468889^3803*312500000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47896681 312500000 924975468889 10000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452171899/10000000000 : ℝ)^4827 ≤ (11576518516557/25000000000000 : ℝ)^3803 := by
    have hnat : (5452171899 : ℕ)^4827*25000000000000^3803 ≤ 11576518516557^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452171899 10000000000 11576518516557 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639352511/5000000000 : ℝ), (-47896681/312500000 : ℝ), (5452171899/10000000000 : ℝ)] ![(22222085617607/50000000000000 : ℝ), (924975468889/10000000000000 : ℝ), (11576518516557/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639352511/5000000000 : ℝ)|^4827 ≤ (22222085617607/50000000000000 : ℝ)^3803
        have hw : |(2639352511/5000000000 : ℝ)|=(2639352511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-47896681/312500000 : ℝ)|^4827 ≤ (924975468889/10000000000000 : ℝ)^3803
        have hw : |(-47896681/312500000 : ℝ)|=(47896681/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452171899/10000000000 : ℝ)|^4827 ≤ (11576518516557/25000000000000 : ℝ)^3803
        have hw : |(5452171899/10000000000 : ℝ)|=(5452171899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s4_6 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278704833/10000000000 : ℝ)*x 0 + (2726086059/5000000000 : ℝ)*x 1 + (-766346873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278704833/10000000000 : ℝ)^4827 ≤ (11111042303863/25000000000000 : ℝ)^3803 := by
    have hnat : (5278704833 : ℕ)^4827*25000000000000^3803 ≤ 11111042303863^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278704833 10000000000 11111042303863 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2726086059/5000000000 : ℝ)^4827 ≤ (46306076427051/100000000000000 : ℝ)^3803 := by
    have hnat : (2726086059 : ℕ)^4827*100000000000000^3803 ≤ 46306076427051^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726086059 5000000000 46306076427051 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (766346873/5000000000 : ℝ)^4827 ≤ (9249754336533/100000000000000 : ℝ)^3803 := by
    have hnat : (766346873 : ℕ)^4827*100000000000000^3803 ≤ 9249754336533^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766346873 5000000000 9249754336533 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278704833/10000000000 : ℝ), (2726086059/5000000000 : ℝ), (-766346873/5000000000 : ℝ)] ![(11111042303863/25000000000000 : ℝ), (46306076427051/100000000000000 : ℝ), (9249754336533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278704833/10000000000 : ℝ)|^4827 ≤ (11111042303863/25000000000000 : ℝ)^3803
        have hw : |(5278704833/10000000000 : ℝ)|=(5278704833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2726086059/5000000000 : ℝ)|^4827 ≤ (46306076427051/100000000000000 : ℝ)^3803
        have hw : |(2726086059/5000000000 : ℝ)|=(2726086059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-766346873/5000000000 : ℝ)|^4827 ≤ (9249754336533/100000000000000 : ℝ)^3803
        have hw : |(-766346873/5000000000 : ℝ)|=(766346873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s4_7 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4198920671/10000000000 : ℝ)*x 0 + (454557517/1000000000 : ℝ)*x 1 + (154913037/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4198920671/10000000000 : ℝ)^4827 ≤ (33240174917541/100000000000000 : ℝ)^3803 := by
    have hnat : (4198920671 : ℕ)^4827*100000000000000^3803 ≤ 33240174917541^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4198920671 10000000000 33240174917541 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (454557517/1000000000 : ℝ)^4827 ≤ (36761297901453/100000000000000 : ℝ)^3803 := by
    have hnat : (454557517 : ℕ)^4827*100000000000000^3803 ≤ 36761297901453^3803*1000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454557517 1000000000 36761297901453 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (154913037/400000000 : ℝ)^4827 ≤ (7499631791563/25000000000000 : ℝ)^3803 := by
    have hnat : (154913037 : ℕ)^4827*25000000000000^3803 ≤ 7499631791563^3803*400000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154913037 400000000 7499631791563 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4198920671/10000000000 : ℝ), (454557517/1000000000 : ℝ), (154913037/400000000 : ℝ)] ![(33240174917541/100000000000000 : ℝ), (36761297901453/100000000000000 : ℝ), (7499631791563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4198920671/10000000000 : ℝ)|^4827 ≤ (33240174917541/100000000000000 : ℝ)^3803
        have hw : |(4198920671/10000000000 : ℝ)|=(4198920671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(454557517/1000000000 : ℝ)|^4827 ≤ (36761297901453/100000000000000 : ℝ)^3803
        have hw : |(454557517/1000000000 : ℝ)|=(454557517/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(154913037/400000000 : ℝ)|^4827 ≤ (7499631791563/25000000000000 : ℝ)^3803
        have hw : |(154913037/400000000 : ℝ)|=(154913037/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1627_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (102/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5267/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5271/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2039/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (102/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5267/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (102/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5267/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (102/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5267/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (102/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5267/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (102/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5267/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (102/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5267/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5267/50000 : ℝ) ^ (4823/1024 : ℝ) ≤ (1245726471749287/50000000000000000000 : ℝ) := by
    have hpowers : (5267/50000 : ℝ)^4823 ≤ (1245726471749287/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5267 : ℕ)^4823*50000000000000000000^1024 ≤ 1245726471749287^1024*50000^4823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5267 50000 1245726471749287 50000000000000000000 4823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5267/50000 : ℝ)) (X := (1245726471749287/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (102/625 : ℝ) ^ (4823/1024 : ℝ) ≤ (19585861559891747/100000000000000000000 : ℝ) := by
    have hpowers : (102/625 : ℝ)^4823 ≤ (19585861559891747/100000000000000000000 : ℝ)^1024 := by
      have hnat : (102 : ℕ)^4823*100000000000000000000^1024 ≤ 19585861559891747^1024*625^4823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102 625 19585861559891747 100000000000000000000 4823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (102/625 : ℝ)) (X := (19585861559891747/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001245726471749287/25000000000000000000 : ℝ) ≤ (10000105792981463/10000000000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (25001245726471749287/25000000000000000000 : ℝ)^1024 ≤ (10000105792981463/10000000000000000 : ℝ)^4823 := by
      have hnat : (25001245726471749287 : ℕ)^1024*10000000000000000^4823 ≤ 10000105792981463^4823*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001245726471749287 25000000000000000000 10000105792981463 10000000000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000105792981463/10000000000000000 : ℝ)) (X := (25001245726471749287/25000000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100022077314503390321/100000000000000000000 : ℝ) ≤ (10000468695928313/10000000000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (100022077314503390321/100000000000000000000 : ℝ)^1024 ≤ (10000468695928313/10000000000000000 : ℝ)^4823 := by
      have hnat : (100022077314503390321 : ℕ)^1024*10000000000000000^4823 ≤ 10000468695928313^4823*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100022077314503390321 100000000000000000000 10000468695928313 10000000000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000468695928313/10000000000000000 : ℝ)) (X := (100022077314503390321/100000000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50019585861559891747/50000000000000000000 : ℝ) ≤ (10000831598875163/10000000000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (50019585861559891747/50000000000000000000 : ℝ)^1024 ≤ (10000831598875163/10000000000000000 : ℝ)^4823 := by
      have hnat : (50019585861559891747 : ℕ)^1024*10000000000000000^4823 ≤ 10000831598875163^4823*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019585861559891747 50000000000000000000 10000831598875163 10000000000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000831598875163/10000000000000000 : ℝ)) (X := (50019585861559891747/50000000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1245726471749287/50000000000000000000 : ℝ) ≤ ((28926483239453254559/28930000000000000000 : ℝ)+2*(7258058937/11572000000000 : ℝ)*(5267/50000 : ℝ))^(4823/1024 : ℝ) := by
    rw [show (28926483239453254559/28930000000000000000 : ℝ)+2*(7258058937/11572000000000 : ℝ)*(5267/50000 : ℝ)=(10000105792981463/10000000000000000 : ℝ) by norm_num, show 1+2*(1245726471749287/50000000000000000000 : ℝ)=(25001245726471749287/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19585861559891747/100000000000000000000 : ℝ)+(1245726471749287/50000000000000000000 : ℝ) ≤ ((28926483239453254559/28930000000000000000 : ℝ)+(7258058937/11572000000000 : ℝ)*((102/625 : ℝ)+(5267/50000 : ℝ)))^(4823/1024 : ℝ) := by
    rw [show (28926483239453254559/28930000000000000000 : ℝ)+(7258058937/11572000000000 : ℝ)*((102/625 : ℝ)+(5267/50000 : ℝ))=(10000468695928313/10000000000000000 : ℝ) by norm_num, show 1+(19585861559891747/100000000000000000000 : ℝ)+(1245726471749287/50000000000000000000 : ℝ)=(100022077314503390321/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19585861559891747/100000000000000000000 : ℝ) ≤ ((28926483239453254559/28930000000000000000 : ℝ)+2*(7258058937/11572000000000 : ℝ)*(102/625 : ℝ))^(4823/1024 : ℝ) := by
    rw [show (28926483239453254559/28930000000000000000 : ℝ)+2*(7258058937/11572000000000 : ℝ)*(102/625 : ℝ)=(10000831598875163/10000000000000000 : ℝ) by norm_num, show 1+2*(19585861559891747/100000000000000000000 : ℝ)=(50019585861559891747/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28926483239453254559/28930000000000000000 : ℝ)*(X 1 0+X 2 0)+(7258058937/11572000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (5267/50000 : ℝ)) (hi := (102/625 : ℝ)) (c := (28926483239453254559/28930000000000000000 : ℝ)) (alpha := (7258058937/11572000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28926483239453254559/28930000000000000000 : ℝ)*(X 0 1+X 2 1)+(7258058937/11572000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (5267/50000 : ℝ)) (hi := (102/625 : ℝ)) (c := (28926483239453254559/28930000000000000000 : ℝ)) (alpha := (7258058937/11572000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28926483239453254559/28930000000000000000 : ℝ)*(X 0 2+X 1 2)+(7258058937/11572000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (5267/50000 : ℝ)) (hi := (102/625 : ℝ)) (c := (28926483239453254559/28930000000000000000 : ℝ)) (alpha := (7258058937/11572000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-831209117/5000000000 : ℝ)*X 0 0+(1363557053/2500000000 : ℝ)*X 0 1+(2591185097/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267555383/500000000 : ℝ)*X 1 0+(-1802495773/10000000000 : ℝ)*X 1 1+(259118499/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351107491/10000000000 : ℝ)*X 2 0+(5182370171/10000000000 : ℝ)*X 2 1+(-1802495747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4198751131/10000000000 : ℝ)*X 0 0+(3867660237/10000000000 : ℝ)*X 0 1+(35552243/78125000 : ℝ)*X 0 2+(4198751131/10000000000 : ℝ)*X 1 0+(3867660237/10000000000 : ℝ)*X 1 1+(35552243/78125000 : ℝ)*X 1 2+(4198751131/10000000000 : ℝ)*X 2 0+(3867660237/10000000000 : ℝ)*X 2 1+(35552243/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-166248601/1000000000 : ℝ)*X 0 0+(40503163/78125000 : ℝ)*X 0 1+(5452171931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639352511/5000000000 : ℝ)*X 1 0+(-47896681/312500000 : ℝ)*X 1 1+(5452171899/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278704833/10000000000 : ℝ)*X 2 0+(2726086059/5000000000 : ℝ)*X 2 1+(-766346873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4198920671/10000000000 : ℝ)*X 0 0+(454557517/1000000000 : ℝ)*X 0 1+(154913037/400000000 : ℝ)*X 0 2+(4198920671/10000000000 : ℝ)*X 1 0+(454557517/1000000000 : ℝ)*X 1 1+(154913037/400000000 : ℝ)*X 1 2+(4198920671/10000000000 : ℝ)*X 2 0+(454557517/1000000000 : ℝ)*X 2 1+(154913037/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9822184704684964722972333/3287500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (504798613/100000000000000 : ℝ)*(base19) + (34649963/10000000000000 : ℝ)*(base23) + (5635641/25000000000000 : ℝ)*(lower2) + (35011233/50000000000000 : ℝ)*(upper3) + (21507381/50000000000000 : ℝ)*(upper5) + (128561863079581/5000000000000 : ℝ)*(major0) + (128561863079581/5000000000000 : ℝ)*(major1) + (128561863079581/5000000000000 : ℝ)*(major2) + (229899681364449/6250000000000 : ℝ)*(sp0) + (919599474466587/25000000000000 : ℝ)*(sp1) + (3678398056165331/100000000000000 : ℝ)*(sp2) + (366018389716091/25000000000000 : ℝ)*(sp3) + (3500833777/100000000000000 : ℝ)*(sp4) + (61551567/2500000000000 : ℝ)*(sp7) + (366019005231761/25000000000000 : ℝ)*(f.failure) + (1839199201332481/50000000000000 : ℝ)*(f.sum) + (5825332917733/1446500000000000000000000000 : ℝ)*base65 + (376458448251959779/144650000000000000000000000000000 : ℝ)*base67 + (985785039584209779/144650000000000000000000000000000 : ℝ)*base69 + (104426924144040221/144650000000000000000000000000000 : ℝ)*base72 + (2318937713537/723250000000000000000000000 : ℝ)*base73 + (1001697992304159779/144650000000000000000000000000000 : ℝ)*base75 + (1485338943005309779/144650000000000000000000000000000 : ℝ)*base77 + (629554395369709779/144650000000000000000000000000000 : ℝ)*base79 + (11472143257793/2893000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1507999/2500000000000000000000 : ℝ)*base90 + (1507999/2500000000000000000000 : ℝ)*base92 + (1507999/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17136329920235163870934125003/1446500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (424797377/20000000000000 : ℝ)*(base19) + (1063294937/50000000000000 : ℝ)*(base23) + (282409251/50000000000000 : ℝ)*(lower1) + (38719937/100000000000000 : ℝ)*(upper2) + (389183623/100000000000000 : ℝ)*(upper3) + (205768129/100000000000000 : ℝ)*(upper5) + (2610496939700839/100000000000000 : ℝ)*(major0) + (2610496939700839/100000000000000 : ℝ)*(major1) + (2610496939700839/100000000000000 : ℝ)*(major2) + (459061881/10000000000000 : ℝ)*(sp2) + (933640699092409/25000000000000 : ℝ)*(sp4) + (116705021011961/3125000000000 : ℝ)*(sp5) + (3734556079160953/100000000000000 : ℝ)*(sp6) + (1486430688140229/100000000000000 : ℝ)*(sp7) + (1486430688140229/100000000000000 : ℝ)*(f.failure) + (933640699092409/25000000000000 : ℝ)*(f.sum) + (2758724460677/723250000000000000000000000 : ℝ)*base65 + (5255503849831624999/2893000000000000000000000000000000 : ℝ)*base68 + (32905931416582624999/2893000000000000000000000000000000 : ℝ)*base70 + (7770477764548624999/2893000000000000000000000000000000 : ℝ)*base72 + (3795363794263/2893000000000000000000000000 : ℝ)*base74 + (2600439273141375001/2893000000000000000000000000000000 : ℝ)*base75 + (3761277669056375001/2893000000000000000000000000000000 : ℝ)*base77 + (16064085875611624999/2893000000000000000000000000000000 : ℝ)*base80 + (18916444211067/1446500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (16858411/10000000000000000000000 : ℝ)*base90 + (16858411/10000000000000000000000 : ℝ)*base92 + (16858411/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1627_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (102/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5267/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5271/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2039/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1627_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1627_s5_0 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41805471/78125000 : ℝ)*x 0 + (5182395939/10000000000 : ℝ)*x 1 + (-901235579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41805471/78125000 : ℝ)^4827 ≤ (22609626076439/50000000000000 : ℝ)^3803 := by
    have hnat : (41805471 : ℕ)^4827*50000000000000^3803 ≤ 22609626076439^3803*78125000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41805471 78125000 22609626076439 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182395939/10000000000 : ℝ)^4827 ≤ (43417496738289/100000000000000 : ℝ)^3803 := by
    have hnat : (5182395939 : ℕ)^4827*100000000000000^3803 ≤ 43417496738289^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182395939 10000000000 43417496738289 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901235579/5000000000 : ℝ)^4827 ≤ (1136325109339/10000000000000 : ℝ)^3803 := by
    have hnat : (901235579 : ℕ)^4827*10000000000000^3803 ≤ 1136325109339^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901235579 5000000000 1136325109339 10000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41805471/78125000 : ℝ), (5182395939/10000000000 : ℝ), (-901235579/5000000000 : ℝ)] ![(22609626076439/50000000000000 : ℝ), (43417496738289/100000000000000 : ℝ), (1136325109339/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41805471/78125000 : ℝ)|^4827 ≤ (22609626076439/50000000000000 : ℝ)^3803
        have hw : |(41805471/78125000 : ℝ)|=(41805471/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182395939/10000000000 : ℝ)|^4827 ≤ (43417496738289/100000000000000 : ℝ)^3803
        have hw : |(5182395939/10000000000 : ℝ)|=(5182395939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-901235579/5000000000 : ℝ)|^4827 ≤ (1136325109339/10000000000000 : ℝ)^3803
        have hw : |(-901235579/5000000000 : ℝ)|=(901235579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s5_1 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262422249/625000000 : ℝ)*x 0 + (1933865379/5000000000 : ℝ)*x 1 + (910122971/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262422249/625000000 : ℝ)^4827 ≤ (16619260081409/50000000000000 : ℝ)^3803 := by
    have hnat : (262422249 : ℕ)^4827*50000000000000^3803 ≤ 16619260081409^3803*625000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262422249 625000000 16619260081409 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1933865379/5000000000 : ℝ)^4827 ≤ (3743555318073/12500000000000 : ℝ)^3803 := by
    have hnat : (1933865379 : ℕ)^4827*12500000000000^3803 ≤ 3743555318073^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933865379 5000000000 3743555318073 12500000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (910122971/2000000000 : ℝ)^4827 ≤ (1150407414823/3125000000000 : ℝ)^3803 := by
    have hnat : (910122971 : ℕ)^4827*3125000000000^3803 ≤ 1150407414823^3803*2000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910122971 2000000000 1150407414823 3125000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262422249/625000000 : ℝ), (1933865379/5000000000 : ℝ), (910122971/2000000000 : ℝ)] ![(16619260081409/50000000000000 : ℝ), (3743555318073/12500000000000 : ℝ), (1150407414823/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262422249/625000000 : ℝ)|^4827 ≤ (16619260081409/50000000000000 : ℝ)^3803
        have hw : |(262422249/625000000 : ℝ)|=(262422249/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1933865379/5000000000 : ℝ)|^4827 ≤ (3743555318073/12500000000000 : ℝ)^3803
        have hw : |(1933865379/5000000000 : ℝ)|=(1933865379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(910122971/2000000000 : ℝ)|^4827 ≤ (1150407414823/3125000000000 : ℝ)^3803
        have hw : |(910122971/2000000000 : ℝ)|=(910122971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s5_2 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1662490703/10000000000 : ℝ)*x 0 + (2592215573/5000000000 : ℝ)*x 1 + (1090428519/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1662490703/10000000000 : ℝ)^4827 ≤ (10255102125231/100000000000000 : ℝ)^3803 := by
    have hnat : (1662490703 : ℕ)^4827*100000000000000^3803 ≤ 10255102125231^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1662490703 10000000000 10255102125231 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592215573/5000000000 : ℝ)^4827 ≤ (8687827940189/20000000000000 : ℝ)^3803 := by
    have hnat : (2592215573 : ℕ)^4827*20000000000000^3803 ≤ 8687827940189^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592215573 5000000000 8687827940189 20000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090428519/2000000000 : ℝ)^4827 ≤ (370446065351/800000000000 : ℝ)^3803 := by
    have hnat : (1090428519 : ℕ)^4827*800000000000^3803 ≤ 370446065351^3803*2000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090428519 2000000000 370446065351 800000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1662490703/10000000000 : ℝ), (2592215573/5000000000 : ℝ), (1090428519/2000000000 : ℝ)] ![(10255102125231/100000000000000 : ℝ), (8687827940189/20000000000000 : ℝ), (370446065351/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1662490703/10000000000 : ℝ)|^4827 ≤ (10255102125231/100000000000000 : ℝ)^3803
        have hw : |(-1662490703/10000000000 : ℝ)|=(1662490703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592215573/5000000000 : ℝ)|^4827 ≤ (8687827940189/20000000000000 : ℝ)^3803
        have hw : |(2592215573/5000000000 : ℝ)|=(2592215573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1090428519/2000000000 : ℝ)|^4827 ≤ (370446065351/800000000000 : ℝ)^3803
        have hw : |(1090428519/2000000000 : ℝ)|=(1090428519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s5_3 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319678081/2500000000 : ℝ)*x 0 + (-383181139/2500000000 : ℝ)*x 1 + (5452142799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319678081/2500000000 : ℝ)^4827 ≤ (44444249268573/100000000000000 : ℝ)^3803 := by
    have hnat : (1319678081 : ℕ)^4827*100000000000000^3803 ≤ 44444249268573^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319678081 2500000000 44444249268573 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (383181139/2500000000 : ℝ)^4827 ≤ (184999806803/2000000000000 : ℝ)^3803 := by
    have hnat : (383181139 : ℕ)^4827*2000000000000^3803 ≤ 184999806803^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383181139 2500000000 184999806803 2000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452142799/10000000000 : ℝ)^4827 ≤ (9261152073599/20000000000000 : ℝ)^3803 := by
    have hnat : (5452142799 : ℕ)^4827*20000000000000^3803 ≤ 9261152073599^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452142799 10000000000 9261152073599 20000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319678081/2500000000 : ℝ), (-383181139/2500000000 : ℝ), (5452142799/10000000000 : ℝ)] ![(44444249268573/100000000000000 : ℝ), (184999806803/2000000000000 : ℝ), (9261152073599/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319678081/2500000000 : ℝ)|^4827 ≤ (44444249268573/100000000000000 : ℝ)^3803
        have hw : |(1319678081/2500000000 : ℝ)|=(1319678081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-383181139/2500000000 : ℝ)|^4827 ≤ (184999806803/2000000000000 : ℝ)^3803
        have hw : |(-383181139/2500000000 : ℝ)|=(383181139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452142799/10000000000 : ℝ)|^4827 ≤ (9261152073599/20000000000000 : ℝ)^3803
        have hw : |(5452142799/10000000000 : ℝ)|=(5452142799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s5_4 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639355641/5000000000 : ℝ)*x 0 + (5452143547/10000000000 : ℝ)*x 1 + (-766362479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639355641/5000000000 : ℝ)^4827 ≤ (22222119066581/50000000000000 : ℝ)^3803 := by
    have hnat : (2639355641 : ℕ)^4827*50000000000000^3803 ≤ 22222119066581^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639355641 5000000000 22222119066581 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5452143547/10000000000 : ℝ)^4827 ≤ (9261153686287/20000000000000 : ℝ)^3803 := by
    have hnat : (5452143547 : ℕ)^4827*20000000000000^3803 ≤ 9261153686287^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452143547 10000000000 9261153686287 20000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (766362479/5000000000 : ℝ)^4827 ≤ (4624996709733/50000000000000 : ℝ)^3803 := by
    have hnat : (766362479 : ℕ)^4827*50000000000000^3803 ≤ 4624996709733^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766362479 5000000000 4624996709733 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639355641/5000000000 : ℝ), (5452143547/10000000000 : ℝ), (-766362479/5000000000 : ℝ)] ![(22222119066581/50000000000000 : ℝ), (9261153686287/20000000000000 : ℝ), (4624996709733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639355641/5000000000 : ℝ)|^4827 ≤ (22222119066581/50000000000000 : ℝ)^3803
        have hw : |(2639355641/5000000000 : ℝ)|=(2639355641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5452143547/10000000000 : ℝ)|^4827 ≤ (9261153686287/20000000000000 : ℝ)^3803
        have hw : |(5452143547/10000000000 : ℝ)|=(5452143547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-766362479/5000000000 : ℝ)|^4827 ≤ (4624996709733/50000000000000 : ℝ)^3803
        have hw : |(-766362479/5000000000 : ℝ)|=(766362479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_s5_5 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1049731091/2500000000 : ℝ)*x 0 + (2272753103/5000000000 : ℝ)*x 1 + (1936447077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049731091/2500000000 : ℝ)^4827 ≤ (33240212024551/100000000000000 : ℝ)^3803 := by
    have hnat : (1049731091 : ℕ)^4827*100000000000000^3803 ≤ 33240212024551^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049731091 2500000000 33240212024551 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2272753103/5000000000 : ℝ)^4827 ≤ (91901474993/250000000000 : ℝ)^3803 := by
    have hnat : (2272753103 : ℕ)^4827*250000000000^3803 ≤ 91901474993^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272753103 5000000000 91901474993 250000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1936447077/5000000000 : ℝ)^4827 ≤ (5999839593223/20000000000000 : ℝ)^3803 := by
    have hnat : (1936447077 : ℕ)^4827*20000000000000^3803 ≤ 5999839593223^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936447077 5000000000 5999839593223 20000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049731091/2500000000 : ℝ), (2272753103/5000000000 : ℝ), (1936447077/5000000000 : ℝ)] ![(33240212024551/100000000000000 : ℝ), (91901474993/250000000000 : ℝ), (5999839593223/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049731091/2500000000 : ℝ)|^4827 ≤ (33240212024551/100000000000000 : ℝ)^3803
        have hw : |(1049731091/2500000000 : ℝ)|=(1049731091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2272753103/5000000000 : ℝ)|^4827 ≤ (91901474993/250000000000 : ℝ)^3803
        have hw : |(2272753103/5000000000 : ℝ)|=(2272753103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1936447077/5000000000 : ℝ)|^4827 ≤ (5999839593223/20000000000000 : ℝ)^3803
        have hw : |(1936447077/5000000000 : ℝ)|=(1936447077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1627_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2039/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5271/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5271/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16311/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2039/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5271/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2039/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5271/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2039/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5271/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2039/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5271/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2039/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5271/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2039/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5271/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5271/50000 : ℝ) ^ (4823/1024 : ℝ) ≤ (500075466413477/20000000000000000000 : ℝ) := by
    have hpowers : (5271/50000 : ℝ)^4823 ≤ (500075466413477/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5271 : ℕ)^4823*20000000000000000000^1024 ≤ 500075466413477^1024*50000^4823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5271 50000 500075466413477 20000000000000000000 4823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5271/50000 : ℝ)) (X := (500075466413477/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2039/12500 : ℝ) ^ (4823/1024 : ℝ) ≤ (2442585342171763/12500000000000000000 : ℝ) := by
    have hpowers : (2039/12500 : ℝ)^4823 ≤ (2442585342171763/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2039 : ℕ)^4823*12500000000000000000^1024 ≤ 2442585342171763^1024*12500^4823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2039 12500 2442585342171763 12500000000000000000 4823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2039/12500 : ℝ)) (X := (2442585342171763/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000500075466413477/10000000000000000000 : ℝ) ≤ (5000053085962317/5000000000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (10000500075466413477/10000000000000000000 : ℝ)^1024 ≤ (5000053085962317/5000000000000000 : ℝ)^4823 := by
      have hnat : (10000500075466413477 : ℕ)^1024*5000000000000000^4823 ≤ 5000053085962317^4823*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000500075466413477 10000000000000000000 5000053085962317 5000000000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000053085962317/5000000000000000 : ℝ)) (X := (10000500075466413477/10000000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100022041060069441489/100000000000000000000 : ℝ) ≤ (2000093585264489/2000000000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (100022041060069441489/100000000000000000000 : ℝ)^1024 ≤ (2000093585264489/2000000000000000 : ℝ)^4823 := by
      have hnat : (100022041060069441489 : ℕ)^1024*2000000000000000^4823 ≤ 2000093585264489^4823*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100022041060069441489 100000000000000000000 2000093585264489 2000000000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000093585264489/2000000000000000 : ℝ)) (X := (100022041060069441489/100000000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252442585342171763/6250000000000000000 : ℝ) ≤ (78131481880627/78125000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (6252442585342171763/6250000000000000000 : ℝ)^1024 ≤ (78131481880627/78125000000000 : ℝ)^4823 := by
      have hnat : (6252442585342171763 : ℕ)^1024*78125000000000^4823 ≤ 78131481880627^4823*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252442585342171763 6250000000000000000 78131481880627 78125000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78131481880627/78125000000000 : ℝ)) (X := (6252442585342171763/6250000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(500075466413477/20000000000000000000 : ℝ) ≤ ((3605811586392605691/3606250000000000000 : ℝ)+2*(361754397811/577000000000000 : ℝ)*(5271/50000 : ℝ))^(4823/1024 : ℝ) := by
    rw [show (3605811586392605691/3606250000000000000 : ℝ)+2*(361754397811/577000000000000 : ℝ)*(5271/50000 : ℝ)=(5000053085962317/5000000000000000 : ℝ) by norm_num, show 1+2*(500075466413477/20000000000000000000 : ℝ)=(10000500075466413477/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2442585342171763/12500000000000000000 : ℝ)+(500075466413477/20000000000000000000 : ℝ) ≤ ((3605811586392605691/3606250000000000000 : ℝ)+(361754397811/577000000000000 : ℝ)*((2039/12500 : ℝ)+(5271/50000 : ℝ)))^(4823/1024 : ℝ) := by
    rw [show (3605811586392605691/3606250000000000000 : ℝ)+(361754397811/577000000000000 : ℝ)*((2039/12500 : ℝ)+(5271/50000 : ℝ))=(2000093585264489/2000000000000000 : ℝ) by norm_num, show 1+(2442585342171763/12500000000000000000 : ℝ)+(500075466413477/20000000000000000000 : ℝ)=(100022041060069441489/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2442585342171763/12500000000000000000 : ℝ) ≤ ((3605811586392605691/3606250000000000000 : ℝ)+2*(361754397811/577000000000000 : ℝ)*(2039/12500 : ℝ))^(4823/1024 : ℝ) := by
    rw [show (3605811586392605691/3606250000000000000 : ℝ)+2*(361754397811/577000000000000 : ℝ)*(2039/12500 : ℝ)=(78131481880627/78125000000000 : ℝ) by norm_num, show 1+2*(2442585342171763/12500000000000000000 : ℝ)=(6252442585342171763/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3605811586392605691/3606250000000000000 : ℝ)*(X 1 0+X 2 0)+(361754397811/577000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (5271/50000 : ℝ)) (hi := (2039/12500 : ℝ)) (c := (3605811586392605691/3606250000000000000 : ℝ)) (alpha := (361754397811/577000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3605811586392605691/3606250000000000000 : ℝ)*(X 0 1+X 2 1)+(361754397811/577000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (5271/50000 : ℝ)) (hi := (2039/12500 : ℝ)) (c := (3605811586392605691/3606250000000000000 : ℝ)) (alpha := (361754397811/577000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3605811586392605691/3606250000000000000 : ℝ)*(X 0 2+X 1 2)+(361754397811/577000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (5271/50000 : ℝ)) (hi := (2039/12500 : ℝ)) (c := (3605811586392605691/3606250000000000000 : ℝ)) (alpha := (361754397811/577000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((41805471/78125000 : ℝ)*X 2 0+(5182395939/10000000000 : ℝ)*X 2 1+(-901235579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s5_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((262422249/625000000 : ℝ)*X 0 0+(1933865379/5000000000 : ℝ)*X 0 1+(910122971/2000000000 : ℝ)*X 0 2+(262422249/625000000 : ℝ)*X 1 0+(1933865379/5000000000 : ℝ)*X 1 1+(910122971/2000000000 : ℝ)*X 1 2+(262422249/625000000 : ℝ)*X 2 0+(1933865379/5000000000 : ℝ)*X 2 1+(910122971/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s5_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-1662490703/10000000000 : ℝ)*X 0 0+(2592215573/5000000000 : ℝ)*X 0 1+(1090428519/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s5_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1319678081/2500000000 : ℝ)*X 1 0+(-383181139/2500000000 : ℝ)*X 1 1+(5452142799/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s5_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2639355641/5000000000 : ℝ)*X 2 0+(5452143547/10000000000 : ℝ)*X 2 1+(-766362479/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s5_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1049731091/2500000000 : ℝ)*X 0 0+(2272753103/5000000000 : ℝ)*X 0 1+(1936447077/5000000000 : ℝ)*X 0 2+(1049731091/2500000000 : ℝ)*X 1 0+(2272753103/5000000000 : ℝ)*X 1 1+(1936447077/5000000000 : ℝ)*X 1 2+(1049731091/2500000000 : ℝ)*X 2 0+(2272753103/5000000000 : ℝ)*X 2 1+(1936447077/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_s5_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (428376143086642916211612807/45078125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47366483/4000000000000 : ℝ)*(base19) + (281809603/50000000000000 : ℝ)*(base23) + (267463201/100000000000000 : ℝ)*(lower1) + (347277797/100000000000000 : ℝ)*(upper3) + (5674981/10000000000000 : ℝ)*(lower4) + (1305521096891059/50000000000000 : ℝ)*(major0) + (1305521096891059/50000000000000 : ℝ)*(major1) + (1305521096891059/50000000000000 : ℝ)*(major2) + (67774561/10000000000000 : ℝ)*(sp0) + (171425813/12500000000000 : ℝ)*(sp1) + (373534291211647/10000000000000 : ℝ)*(sp2) + (1867670863977197/50000000000000 : ℝ)*(sp3) + (3735341670751653/100000000000000 : ℝ)*(sp4) + (148673978727553/10000000000000 : ℝ)*(sp5) + (743370579341017/50000000000000 : ℝ)*(f.failure) + (373534291211647/10000000000000 : ℝ)*(f.sum) + (43306597811701/14425000000000000000000000000 : ℝ)*base66 + (1923076755588026981/180312500000000000000000000000000 : ℝ)*base68 + (1272174660139901981/180312500000000000000000000000000 : ℝ)*base70 + (2393028953200526981/180312500000000000000000000000000 : ℝ)*base72 + (36393210313051/14425000000000000000000000000 : ℝ)*base74 + (790696057668848019/180312500000000000000000000000000 : ℝ)*base75 + (1321113184166151981/180312500000000000000000000000000 : ℝ)*base78 + (4201331749430839481/180312500000000000000000000000000 : ℝ)*base80 + (49374861818799/14425000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (72352297/5000000000000000000000 : ℝ)*base89 + (72352297/5000000000000000000000 : ℝ)*base91 + (72352297/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1627_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2039/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5271/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5271/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16311/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1627_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1627_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8213/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10439/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5271/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16311/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1627_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1627_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1627_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8213/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10439/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5271/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16311/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1627_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1412_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:48:51.849983+00:00
-- url     : https://prove2.me/submissions/6b3e45b7-52e5-458f-9d8c-0dfdee9b7752

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
theorem support_rectangle_w1412_s6_0 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-248125463/1250000000 : ℝ)*x 0 + (2704550609/5000000000 : ℝ)*x 1 + (1049302167/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (248125463/1250000000 : ℝ)^1093 ≤ (6052693014611/50000000000000 : ℝ)^837 := by
    have hnat : (248125463 : ℕ)^1093*50000000000000^837 ≤ 6052693014611^837*1250000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248125463 1250000000 6052693014611 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704550609/5000000000 : ℝ)^1093 ≤ (44822935005143/100000000000000 : ℝ)^837 := by
    have hnat : (2704550609 : ℕ)^1093*100000000000000^837 ≤ 44822935005143^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704550609 5000000000 44822935005143 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049302167/2000000000 : ℝ)^1093 ≤ (4307167895081/10000000000000 : ℝ)^837 := by
    have hnat : (1049302167 : ℕ)^1093*10000000000000^837 ≤ 4307167895081^837*2000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049302167 2000000000 4307167895081 10000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-248125463/1250000000 : ℝ), (2704550609/5000000000 : ℝ), (1049302167/2000000000 : ℝ)] ![(6052693014611/50000000000000 : ℝ), (44822935005143/100000000000000 : ℝ), (4307167895081/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-248125463/1250000000 : ℝ)|^1093 ≤ (6052693014611/50000000000000 : ℝ)^837
        have hw : |(-248125463/1250000000 : ℝ)|=(248125463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704550609/5000000000 : ℝ)|^1093 ≤ (44822935005143/100000000000000 : ℝ)^837
        have hw : |(2704550609/5000000000 : ℝ)|=(2704550609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049302167/2000000000 : ℝ)|^1093 ≤ (4307167895081/10000000000000 : ℝ)^837
        have hw : |(1049302167/2000000000 : ℝ)|=(1049302167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s6_1 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336920359/2500000000 : ℝ)*x 0 + (-258474129/1250000000 : ℝ)*x 1 + (163953463/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336920359/2500000000 : ℝ)^1093 ≤ (11039866221929/25000000000000 : ℝ)^837 := by
    have hnat : (1336920359 : ℕ)^1093*25000000000000^837 ≤ 11039866221929^837*2500000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336920359 2500000000 11039866221929 25000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258474129/1250000000 : ℝ)^1093 ≤ (12768856343611/100000000000000 : ℝ)^837 := by
    have hnat : (258474129 : ℕ)^1093*100000000000000^837 ≤ 12768856343611^837*1250000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258474129 1250000000 12768856343611 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163953463/312500000 : ℝ)^1093 ≤ (43071678747121/100000000000000 : ℝ)^837 := by
    have hnat : (163953463 : ℕ)^1093*100000000000000^837 ≤ 43071678747121^837*312500000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163953463 312500000 43071678747121 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336920359/2500000000 : ℝ), (-258474129/1250000000 : ℝ), (163953463/312500000 : ℝ)] ![(11039866221929/25000000000000 : ℝ), (12768856343611/100000000000000 : ℝ), (43071678747121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336920359/2500000000 : ℝ)|^1093 ≤ (11039866221929/25000000000000 : ℝ)^837
        have hw : |(1336920359/2500000000 : ℝ)|=(1336920359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-258474129/1250000000 : ℝ)|^1093 ≤ (12768856343611/100000000000000 : ℝ)^837
        have hw : |(-258474129/1250000000 : ℝ)|=(258474129/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163953463/312500000 : ℝ)|^1093 ≤ (43071678747121/100000000000000 : ℝ)^837
        have hw : |(163953463/312500000 : ℝ)|=(163953463/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s6_2 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5347681451/10000000000 : ℝ)*x 0 + (5246510779/10000000000 : ℝ)*x 1 + (-1033896531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347681451/10000000000 : ℝ)^1093 ≤ (22079732524733/50000000000000 : ℝ)^837 := by
    have hnat : (5347681451 : ℕ)^1093*50000000000000^837 ≤ 22079732524733^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347681451 10000000000 22079732524733 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246510779/10000000000 : ℝ)^1093 ≤ (43071678350461/100000000000000 : ℝ)^837 := by
    have hnat : (5246510779 : ℕ)^1093*100000000000000^837 ≤ 43071678350461^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246510779 10000000000 43071678350461 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1033896531/5000000000 : ℝ)^1093 ≤ (510754263421/4000000000000 : ℝ)^837 := by
    have hnat : (1033896531 : ℕ)^1093*4000000000000^837 ≤ 510754263421^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033896531 5000000000 510754263421 4000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347681451/10000000000 : ℝ), (5246510779/10000000000 : ℝ), (-1033896531/5000000000 : ℝ)] ![(22079732524733/50000000000000 : ℝ), (43071678350461/100000000000000 : ℝ), (510754263421/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347681451/10000000000 : ℝ)|^1093 ≤ (22079732524733/50000000000000 : ℝ)^837
        have hw : |(5347681451/10000000000 : ℝ)|=(5347681451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246510779/10000000000 : ℝ)|^1093 ≤ (43071678350461/100000000000000 : ℝ)^837
        have hw : |(5246510779/10000000000 : ℝ)|=(5246510779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1033896531/5000000000 : ℝ)|^1093 ≤ (510754263421/4000000000000 : ℝ)^837
        have hw : |(-1033896531/5000000000 : ℝ)|=(1033896531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s6_3 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2154321179/5000000000 : ℝ)*x 0 + (1034270109/2500000000 : ℝ)*x 1 + (2243314141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154321179/5000000000 : ℝ)^1093 ≤ (16652211786921/50000000000000 : ℝ)^837 := by
    have hnat : (2154321179 : ℕ)^1093*50000000000000^837 ≤ 16652211786921^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154321179 5000000000 16652211786921 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034270109/2500000000 : ℝ)^1093 ≤ (3158334964713/10000000000000 : ℝ)^837 := by
    have hnat : (1034270109 : ℕ)^1093*10000000000000^837 ≤ 3158334964713^837*2500000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034270109 2500000000 3158334964713 10000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243314141/5000000000 : ℝ)^1093 ≤ (351122267723/1000000000000 : ℝ)^837 := by
    have hnat : (2243314141 : ℕ)^1093*1000000000000^837 ≤ 351122267723^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243314141 5000000000 351122267723 1000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154321179/5000000000 : ℝ), (1034270109/2500000000 : ℝ), (2243314141/5000000000 : ℝ)] ![(16652211786921/50000000000000 : ℝ), (3158334964713/10000000000000 : ℝ), (351122267723/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154321179/5000000000 : ℝ)|^1093 ≤ (16652211786921/50000000000000 : ℝ)^837
        have hw : |(2154321179/5000000000 : ℝ)|=(2154321179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1034270109/2500000000 : ℝ)|^1093 ≤ (3158334964713/10000000000000 : ℝ)^837
        have hw : |(1034270109/2500000000 : ℝ)|=(1034270109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2243314141/5000000000 : ℝ)|^1093 ≤ (351122267723/1000000000000 : ℝ)^837
        have hw : |(2243314141/5000000000 : ℝ)|=(2243314141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s6_4 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-7940061/40000000 : ℝ)*x 0 + (524709633/1000000000 : ℝ)*x 1 + (2704256323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7940061/40000000 : ℝ)^1093 ≤ (6052738988789/50000000000000 : ℝ)^837 := by
    have hnat : (7940061 : ℕ)^1093*50000000000000^837 ≤ 6052738988789^837*40000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7940061 40000000 6052738988789 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524709633/1000000000 : ℝ)^1093 ≤ (2692372241871/6250000000000 : ℝ)^837 := by
    have hnat : (524709633 : ℕ)^1093*6250000000000^837 ≤ 2692372241871^837*1000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524709633 1000000000 2692372241871 6250000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704256323/5000000000 : ℝ)^1093 ≤ (2801035383563/6250000000000 : ℝ)^837 := by
    have hnat : (2704256323 : ℕ)^1093*6250000000000^837 ≤ 2801035383563^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704256323 5000000000 2801035383563 6250000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7940061/40000000 : ℝ), (524709633/1000000000 : ℝ), (2704256323/5000000000 : ℝ)] ![(6052738988789/50000000000000 : ℝ), (2692372241871/6250000000000 : ℝ), (2801035383563/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7940061/40000000 : ℝ)|^1093 ≤ (6052738988789/50000000000000 : ℝ)^837
        have hw : |(-7940061/40000000 : ℝ)|=(7940061/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524709633/1000000000 : ℝ)|^1093 ≤ (2692372241871/6250000000000 : ℝ)^837
        have hw : |(524709633/1000000000 : ℝ)|=(524709633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704256323/5000000000 : ℝ)|^1093 ≤ (2801035383563/6250000000000 : ℝ)^837
        have hw : |(2704256323/5000000000 : ℝ)|=(2704256323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s6_5 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305483637/10000000000 : ℝ)*x 0 + (-1905791243/10000000000 : ℝ)*x 1 + (1081702529/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305483637/10000000000 : ℝ)^1093 ≤ (21852491058097/50000000000000 : ℝ)^837 := by
    have hnat : (5305483637 : ℕ)^1093*50000000000000^837 ≤ 21852491058097^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305483637 10000000000 21852491058097 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1905791243/10000000000 : ℝ)^1093 ≤ (358701616693/3125000000000 : ℝ)^837 := by
    have hnat : (1905791243 : ℕ)^1093*3125000000000^837 ≤ 358701616693^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1905791243 10000000000 358701616693 3125000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081702529/2000000000 : ℝ)^1093 ≤ (44816566126187/100000000000000 : ℝ)^837 := by
    have hnat : (1081702529 : ℕ)^1093*100000000000000^837 ≤ 44816566126187^837*2000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081702529 2000000000 44816566126187 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305483637/10000000000 : ℝ), (-1905791243/10000000000 : ℝ), (1081702529/2000000000 : ℝ)] ![(21852491058097/50000000000000 : ℝ), (358701616693/3125000000000 : ℝ), (44816566126187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305483637/10000000000 : ℝ)|^1093 ≤ (21852491058097/50000000000000 : ℝ)^837
        have hw : |(5305483637/10000000000 : ℝ)|=(5305483637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1905791243/10000000000 : ℝ)|^1093 ≤ (358701616693/3125000000000 : ℝ)^837
        have hw : |(-1905791243/10000000000 : ℝ)|=(1905791243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081702529/2000000000 : ℝ)|^1093 ≤ (44816566126187/100000000000000 : ℝ)^837
        have hw : |(1081702529/2000000000 : ℝ)|=(1081702529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s6_6 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305483671/10000000000 : ℝ)*x 0 + (1352128153/2500000000 : ℝ)*x 1 + (-952895621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305483671/10000000000 : ℝ)^1093 ≤ (2185249124097/5000000000000 : ℝ)^837 := by
    have hnat : (5305483671 : ℕ)^1093*5000000000000^837 ≤ 2185249124097^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305483671 10000000000 2185249124097 5000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352128153/2500000000 : ℝ)^1093 ≤ (2801035360569/6250000000000 : ℝ)^837 := by
    have hnat : (1352128153 : ℕ)^1093*6250000000000^837 ≤ 2801035360569^837*2500000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352128153 2500000000 2801035360569 6250000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (952895621/5000000000 : ℝ)^1093 ≤ (11478451726311/100000000000000 : ℝ)^837 := by
    have hnat : (952895621 : ℕ)^1093*100000000000000^837 ≤ 11478451726311^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952895621 5000000000 11478451726311 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305483671/10000000000 : ℝ), (1352128153/2500000000 : ℝ), (-952895621/5000000000 : ℝ)] ![(2185249124097/5000000000000 : ℝ), (2801035360569/6250000000000 : ℝ), (11478451726311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305483671/10000000000 : ℝ)|^1093 ≤ (2185249124097/5000000000000 : ℝ)^837
        have hw : |(5305483671/10000000000 : ℝ)|=(5305483671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352128153/2500000000 : ℝ)|^1093 ≤ (2801035360569/6250000000000 : ℝ)^837
        have hw : |(1352128153/2500000000 : ℝ)|=(1352128153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-952895621/5000000000 : ℝ)|^1093 ≤ (11478451726311/100000000000000 : ℝ)^837
        have hw : |(-952895621/5000000000 : ℝ)|=(952895621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s6_7 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (172346679/400000000 : ℝ)*x 0 + (1121342363/2500000000 : ℝ)*x 1 + (2069172923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172346679/400000000 : ℝ)^1093 ≤ (33304672053983/100000000000000 : ℝ)^837 := by
    have hnat : (172346679 : ℕ)^1093*100000000000000^837 ≤ 33304672053983^837*400000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172346679 400000000 33304672053983 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121342363/2500000000 : ℝ)^1093 ≤ (4387420326529/12500000000000 : ℝ)^837 := by
    have hnat : (1121342363 : ℕ)^1093*12500000000000^837 ≤ 4387420326529^837*2500000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121342363 2500000000 4387420326529 12500000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2069172923/5000000000 : ℝ)^1093 ≤ (15797982661207/50000000000000 : ℝ)^837 := by
    have hnat : (2069172923 : ℕ)^1093*50000000000000^837 ≤ 15797982661207^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069172923 5000000000 15797982661207 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172346679/400000000 : ℝ), (1121342363/2500000000 : ℝ), (2069172923/5000000000 : ℝ)] ![(33304672053983/100000000000000 : ℝ), (4387420326529/12500000000000 : ℝ), (15797982661207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172346679/400000000 : ℝ)|^1093 ≤ (33304672053983/100000000000000 : ℝ)^837
        have hw : |(172346679/400000000 : ℝ)|=(172346679/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121342363/2500000000 : ℝ)|^1093 ≤ (4387420326529/12500000000000 : ℝ)^837
        have hw : |(1121342363/2500000000 : ℝ)|=(1121342363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2069172923/5000000000 : ℝ)|^1093 ≤ (15797982661207/50000000000000 : ℝ)^837
        have hw : |(2069172923/5000000000 : ℝ)|=(2069172923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1412_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157493367/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2261/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3687/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11301/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11301/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11301/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11301/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11301/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11301/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11301/100000 : ℝ) ^ (4371/1024 : ℝ) ≤ (9081918451056087/100000000000000000000 : ℝ) := by
    have hpowers : (11301/100000 : ℝ)^4371 ≤ (9081918451056087/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11301 : ℕ)^4371*100000000000000000000^1024 ≤ 9081918451056087^1024*100000^4371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11301 100000 9081918451056087 100000000000000000000 4371 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11301/100000 : ℝ)) (X := (9081918451056087/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14753/100000 : ℝ) ^ (4371/1024 : ℝ) ≤ (14167404508228819/50000000000000000000 : ℝ) := by
    have hpowers : (14753/100000 : ℝ)^4371 ≤ (14167404508228819/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14753 : ℕ)^4371*50000000000000000000^1024 ≤ 14167404508228819^1024*100000^4371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14753 100000 14167404508228819 50000000000000000000 4371 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14753/100000 : ℝ)) (X := (14167404508228819/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009081918451056087/50000000000000000000 : ℝ) ≤ (1000042549704061/1000000000000000 : ℝ) ^ (4371/1024 : ℝ) := by
    have hpowers : (50009081918451056087/50000000000000000000 : ℝ)^1024 ≤ (1000042549704061/1000000000000000 : ℝ)^4371 := by
      have hnat : (50009081918451056087 : ℕ)^1024*1000000000000000^4371 ≤ 1000042549704061^4371*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009081918451056087 50000000000000000000 1000042549704061 1000000000000000 1024 4371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000042549704061/1000000000000000 : ℝ)) (X := (50009081918451056087/50000000000000000000 : ℝ)) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001496669098700549/4000000000000000000 : ℝ) ≤ (5000438220559907/5000000000000000 : ℝ) ^ (4371/1024 : ℝ) := by
    have hpowers : (4001496669098700549/4000000000000000000 : ℝ)^1024 ≤ (5000438220559907/5000000000000000 : ℝ)^4371 := by
      have hnat : (4001496669098700549 : ℕ)^1024*5000000000000000^4371 ≤ 5000438220559907^4371*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001496669098700549 4000000000000000000 5000438220559907 5000000000000000 1024 4371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000438220559907/5000000000000000 : ℝ)) (X := (4001496669098700549/4000000000000000000 : ℝ)) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014167404508228819/25000000000000000000 : ℝ) ≤ (5000663692599509/5000000000000000 : ℝ) ^ (4371/1024 : ℝ) := by
    have hpowers : (25014167404508228819/25000000000000000000 : ℝ)^1024 ≤ (5000663692599509/5000000000000000 : ℝ)^4371 := by
      have hnat : (25014167404508228819 : ℕ)^1024*5000000000000000^4371 ≤ 5000663692599509^4371*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014167404508228819 25000000000000000000 5000663692599509 5000000000000000 1024 4371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000663692599509/5000000000000000 : ℝ)) (X := (25014167404508228819/25000000000000000000 : ℝ)) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9081918451056087/100000000000000000000 : ℝ) ≤ ((2156954786106626057/2157500000000000000 : ℝ)+2*(112736019801/86300000000000 : ℝ)*(11301/100000 : ℝ))^(4371/1024 : ℝ) := by
    rw [show (2156954786106626057/2157500000000000000 : ℝ)+2*(112736019801/86300000000000 : ℝ)*(11301/100000 : ℝ)=(1000042549704061/1000000000000000 : ℝ) by norm_num, show 1+2*(9081918451056087/100000000000000000000 : ℝ)=(50009081918451056087/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14167404508228819/50000000000000000000 : ℝ)+(9081918451056087/100000000000000000000 : ℝ) ≤ ((2156954786106626057/2157500000000000000 : ℝ)+(112736019801/86300000000000 : ℝ)*((14753/100000 : ℝ)+(11301/100000 : ℝ)))^(4371/1024 : ℝ) := by
    rw [show (2156954786106626057/2157500000000000000 : ℝ)+(112736019801/86300000000000 : ℝ)*((14753/100000 : ℝ)+(11301/100000 : ℝ))=(5000438220559907/5000000000000000 : ℝ) by norm_num, show 1+(14167404508228819/50000000000000000000 : ℝ)+(9081918451056087/100000000000000000000 : ℝ)=(4001496669098700549/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14167404508228819/50000000000000000000 : ℝ) ≤ ((2156954786106626057/2157500000000000000 : ℝ)+2*(112736019801/86300000000000 : ℝ)*(14753/100000 : ℝ))^(4371/1024 : ℝ) := by
    rw [show (2156954786106626057/2157500000000000000 : ℝ)+2*(112736019801/86300000000000 : ℝ)*(14753/100000 : ℝ)=(5000663692599509/5000000000000000 : ℝ) by norm_num, show 1+2*(14167404508228819/50000000000000000000 : ℝ)=(25014167404508228819/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2156954786106626057/2157500000000000000 : ℝ)*(X 1 0+X 2 0)+(112736019801/86300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4371/1024 : ℝ)) (lo := (11301/100000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (2156954786106626057/2157500000000000000 : ℝ)) (alpha := (112736019801/86300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2156954786106626057/2157500000000000000 : ℝ)*(X 0 1+X 2 1)+(112736019801/86300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4371/1024 : ℝ)) (lo := (11301/100000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (2156954786106626057/2157500000000000000 : ℝ)) (alpha := (112736019801/86300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2156954786106626057/2157500000000000000 : ℝ)*(X 0 2+X 1 2)+(112736019801/86300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4371/1024 : ℝ)) (lo := (11301/100000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (2156954786106626057/2157500000000000000 : ℝ)) (alpha := (112736019801/86300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-248125463/1250000000 : ℝ)*X 0 0+(2704550609/5000000000 : ℝ)*X 0 1+(1049302167/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336920359/2500000000 : ℝ)*X 1 0+(-258474129/1250000000 : ℝ)*X 1 1+(163953463/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347681451/10000000000 : ℝ)*X 2 0+(5246510779/10000000000 : ℝ)*X 2 1+(-1033896531/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2154321179/5000000000 : ℝ)*X 0 0+(1034270109/2500000000 : ℝ)*X 0 1+(2243314141/5000000000 : ℝ)*X 0 2+(2154321179/5000000000 : ℝ)*X 1 0+(1034270109/2500000000 : ℝ)*X 1 1+(2243314141/5000000000 : ℝ)*X 1 2+(2154321179/5000000000 : ℝ)*X 2 0+(1034270109/2500000000 : ℝ)*X 2 1+(2243314141/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-7940061/40000000 : ℝ)*X 0 0+(524709633/1000000000 : ℝ)*X 0 1+(2704256323/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305483637/10000000000 : ℝ)*X 1 0+(-1905791243/10000000000 : ℝ)*X 1 1+(1081702529/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305483671/10000000000 : ℝ)*X 2 0+(1352128153/2500000000 : ℝ)*X 2 1+(-952895621/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((172346679/400000000 : ℝ)*X 0 0+(1121342363/2500000000 : ℝ)*X 0 1+(2069172923/5000000000 : ℝ)*X 0 2+(172346679/400000000 : ℝ)*X 1 0+(1121342363/2500000000 : ℝ)*X 1 1+(2069172923/5000000000 : ℝ)*X 1 2+(172346679/400000000 : ℝ)*X 2 0+(1121342363/2500000000 : ℝ)*X 2 1+(2069172923/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (81477148699189795246219311/26968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (282102003/50000000000000 : ℝ)*(base19) + (47033401/10000000000000 : ℝ)*(base23) + (62249661/100000000000000 : ℝ)*(lower2) + (115574519/100000000000000 : ℝ)*(upper3) + (282531/10000000000000 : ℝ)*(lower4) + (2252823648765841/50000000000000 : ℝ)*(major0) + (2252823648765841/50000000000000 : ℝ)*(major1) + (2252823648765841/50000000000000 : ℝ)*(major2) + (1230087373875233/20000000000000 : ℝ)*(sp0) + (6150445004667431/100000000000000 : ℝ)*(sp1) + (1537611274634357/25000000000000 : ℝ)*(sp2) + (715210667726077/25000000000000 : ℝ)*(sp3) + (1087436909/12500000000000 : ℝ)*(sp4) + (6254581983/100000000000000 : ℝ)*(sp7) + (715212231371573/25000000000000 : ℝ)*(f.failure) + (6150445568871437/100000000000000 : ℝ)*(f.sum) + (6220817887353/4315000000000000000000000000 : ℝ)*base66 + (602708155797106063/107875000000000000000000000000000 : ℝ)*base68 + (496242718184731063/107875000000000000000000000000000 : ℝ)*base70 + (250067638218768937/107875000000000000000000000000000 : ℝ)*base71 + (7558030965751/2157500000000000000000000000 : ℝ)*base73 + (3467151730606063/107875000000000000000000000000000 : ℝ)*base76 + (486970727738231063/107875000000000000000000000000000 : ℝ)*base78 + (340756984992856063/107875000000000000000000000000000 : ℝ)*base80 + (1942292775547/1078750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (9856291/2500000000000000000000 : ℝ)*base89 + (9856291/2500000000000000000000 : ℝ)*base91 + (9856291/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (123310828156345167383424489/26968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (747326999/100000000000000 : ℝ)*(base19) + (821571793/100000000000000 : ℝ)*(base23) + (125259257/50000000000000 : ℝ)*(lower1) + (22999053/25000000000000 : ℝ)*(upper3) + (8240693/50000000000000 : ℝ)*(lower4) + (106520217/100000000000000 : ℝ)*(upper5) + (1134598331020709/25000000000000 : ℝ)*(major0) + (1134598331020709/25000000000000 : ℝ)*(major1) + (1134598331020709/25000000000000 : ℝ)*(major2) + (87471947/20000000000000 : ℝ)*(sp2) + (1239029113331599/20000000000000 : ℝ)*(sp4) + (1548786204832749/25000000000000 : ℝ)*(sp5) + (3097572153863233/50000000000000 : ℝ)*(sp6) + (2881640929095659/100000000000000 : ℝ)*(sp7) + (2881640929095659/100000000000000 : ℝ)*(f.failure) + (1239029113331599/20000000000000 : ℝ)*(f.sum) + (31895508263489/4315000000000000000000000000 : ℝ)*base66 + (8580406112135587/53937500000000000000000000000000 : ℝ)*base68 + (1030174077989413/53937500000000000000000000000000 : ℝ)*base69 + (8344891083175698087/53937500000000000000000000000000 : ℝ)*base72 + (4337845622241/1078750000000000000000000000 : ℝ)*base74 + (3256360070793885587/53937500000000000000000000000000 : ℝ)*base76 + (49648768019260587/53937500000000000000000000000000 : ℝ)*base78 + (614094891810301913/53937500000000000000000000000000 : ℝ)*base79 + (29260987307/539375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (993853/10000000000000000000000 : ℝ)*base89 + (993853/10000000000000000000000 : ℝ)*base91 + (993853/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1412_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157493367/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1412_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1412_box_0 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1823103849/10000000000 : ℝ)*x 0 + (5386985329/10000000000 : ℝ)*x 1 + (538698501/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1823103849/10000000000 : ℝ)^1093 ≤ (10832468677849/100000000000000 : ℝ)^837 := by
    have hnat : (1823103849 : ℕ)^1093*100000000000000^837 ≤ 10832468677849^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1823103849 10000000000 10832468677849 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386985329/10000000000 : ℝ)^1093 ≤ (2786485461063/6250000000000 : ℝ)^837 := by
    have hnat : (5386985329 : ℕ)^1093*6250000000000^837 ≤ 2786485461063^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386985329 10000000000 2786485461063 6250000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538698501/1000000000 : ℝ)^1093 ≤ (44583763929413/100000000000000 : ℝ)^837 := by
    have hnat : (538698501 : ℕ)^1093*100000000000000^837 ≤ 44583763929413^837*1000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538698501 1000000000 44583763929413 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1823103849/10000000000 : ℝ), (5386985329/10000000000 : ℝ), (538698501/1000000000 : ℝ)] ![(10832468677849/100000000000000 : ℝ), (2786485461063/6250000000000 : ℝ), (44583763929413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1823103849/10000000000 : ℝ)|^1093 ≤ (10832468677849/100000000000000 : ℝ)^837
        have hw : |(-1823103849/10000000000 : ℝ)|=(1823103849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386985329/10000000000 : ℝ)|^1093 ≤ (2786485461063/6250000000000 : ℝ)^837
        have hw : |(5386985329/10000000000 : ℝ)|=(5386985329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538698501/1000000000 : ℝ)|^1093 ≤ (44583763929413/100000000000000 : ℝ)^837
        have hw : |(538698501/1000000000 : ℝ)|=(538698501/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_box_1 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2642966279/5000000000 : ℝ)*x 0 + (-245233183/1250000000 : ℝ)*x 1 + (1077397007/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642966279/5000000000 : ℝ)^1093 ≤ (43494785181499/100000000000000 : ℝ)^837 := by
    have hnat : (2642966279 : ℕ)^1093*100000000000000^837 ≤ 43494785181499^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642966279 5000000000 43494785181499 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245233183/1250000000 : ℝ)^1093 ≤ (11921450603639/100000000000000 : ℝ)^837 := by
    have hnat : (245233183 : ℕ)^1093*100000000000000^837 ≤ 11921450603639^837*1250000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245233183 1250000000 11921450603639 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077397007/2000000000 : ℝ)^1093 ≤ (111459410499/250000000000 : ℝ)^837 := by
    have hnat : (1077397007 : ℕ)^1093*250000000000^837 ≤ 111459410499^837*2000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077397007 2000000000 111459410499 250000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642966279/5000000000 : ℝ), (-245233183/1250000000 : ℝ), (1077397007/2000000000 : ℝ)] ![(43494785181499/100000000000000 : ℝ), (11921450603639/100000000000000 : ℝ), (111459410499/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642966279/5000000000 : ℝ)|^1093 ≤ (43494785181499/100000000000000 : ℝ)^837
        have hw : |(2642966279/5000000000 : ℝ)|=(2642966279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-245233183/1250000000 : ℝ)|^1093 ≤ (11921450603639/100000000000000 : ℝ)^837
        have hw : |(-245233183/1250000000 : ℝ)|=(245233183/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077397007/2000000000 : ℝ)|^1093 ≤ (111459410499/250000000000 : ℝ)^837
        have hw : |(1077397007/2000000000 : ℝ)|=(1077397007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_box_2 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2642965961/5000000000 : ℝ)*x 0 + (336686583/625000000 : ℝ)*x 1 + (-980932963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642965961/5000000000 : ℝ)^1093 ≤ (21747389173809/50000000000000 : ℝ)^837 := by
    have hnat : (2642965961 : ℕ)^1093*50000000000000^837 ≤ 21747389173809^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642965961 5000000000 21747389173809 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336686583/625000000 : ℝ)^1093 ≤ (44583767366201/100000000000000 : ℝ)^837 := by
    have hnat : (336686583 : ℕ)^1093*100000000000000^837 ≤ 44583767366201^837*625000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336686583 625000000 44583767366201 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (980932963/5000000000 : ℝ)^1093 ≤ (5960727134837/50000000000000 : ℝ)^837 := by
    have hnat : (980932963 : ℕ)^1093*50000000000000^837 ≤ 5960727134837^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980932963 5000000000 5960727134837 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642965961/5000000000 : ℝ), (336686583/625000000 : ℝ), (-980932963/5000000000 : ℝ)] ![(21747389173809/50000000000000 : ℝ), (44583767366201/100000000000000 : ℝ), (5960727134837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642965961/5000000000 : ℝ)|^1093 ≤ (21747389173809/50000000000000 : ℝ)^837
        have hw : |(2642965961/5000000000 : ℝ)|=(2642965961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336686583/625000000 : ℝ)|^1093 ≤ (44583767366201/100000000000000 : ℝ)^837
        have hw : |(336686583/625000000 : ℝ)|=(336686583/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-980932963/5000000000 : ℝ)|^1093 ≤ (5960727134837/50000000000000 : ℝ)^837
        have hw : |(-980932963/5000000000 : ℝ)|=(980932963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_box_3 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2227645987/5000000000 : ℝ)*x 0 + (4239062433/10000000000 : ℝ)*x 1 + (1059765653/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2227645987/5000000000 : ℝ)^1093 ≤ (34792325517673/100000000000000 : ℝ)^837 := by
    have hnat : (2227645987 : ℕ)^1093*100000000000000^837 ≤ 34792325517673^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2227645987 5000000000 34792325517673 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4239062433/10000000000 : ℝ)^1093 ≤ (32603836329169/100000000000000 : ℝ)^837 := by
    have hnat : (4239062433 : ℕ)^1093*100000000000000^837 ≤ 32603836329169^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239062433 10000000000 32603836329169 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059765653/2500000000 : ℝ)^1093 ≤ (3260383812699/10000000000000 : ℝ)^837 := by
    have hnat : (1059765653 : ℕ)^1093*10000000000000^837 ≤ 3260383812699^837*2500000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059765653 2500000000 3260383812699 10000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2227645987/5000000000 : ℝ), (4239062433/10000000000 : ℝ), (1059765653/2500000000 : ℝ)] ![(34792325517673/100000000000000 : ℝ), (32603836329169/100000000000000 : ℝ), (3260383812699/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2227645987/5000000000 : ℝ)|^1093 ≤ (34792325517673/100000000000000 : ℝ)^837
        have hw : |(2227645987/5000000000 : ℝ)|=(2227645987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4239062433/10000000000 : ℝ)|^1093 ≤ (32603836329169/100000000000000 : ℝ)^837
        have hw : |(4239062433/10000000000 : ℝ)|=(4239062433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1059765653/2500000000 : ℝ)|^1093 ≤ (3260383812699/10000000000000 : ℝ)^837
        have hw : |(1059765653/2500000000 : ℝ)|=(1059765653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_box_4 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-429930423/2000000000 : ℝ)*x 0 + (2633131051/5000000000 : ℝ)*x 1 + (5266262011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429930423/2000000000 : ℝ)^1093 ≤ (6716455839303/50000000000000 : ℝ)^837 := by
    have hnat : (429930423 : ℕ)^1093*50000000000000^837 ≤ 6716455839303^837*2000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429930423 2000000000 6716455839303 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633131051/5000000000 : ℝ)^1093 ≤ (43283544640991/100000000000000 : ℝ)^837 := by
    have hnat : (2633131051 : ℕ)^1093*100000000000000^837 ≤ 43283544640991^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633131051 5000000000 43283544640991 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266262011/10000000000 : ℝ)^1093 ≤ (43283543664301/100000000000000 : ℝ)^837 := by
    have hnat : (5266262011 : ℕ)^1093*100000000000000^837 ≤ 43283543664301^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266262011 10000000000 43283543664301 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-429930423/2000000000 : ℝ), (2633131051/5000000000 : ℝ), (5266262011/10000000000 : ℝ)] ![(6716455839303/50000000000000 : ℝ), (43283544640991/100000000000000 : ℝ), (43283543664301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-429930423/2000000000 : ℝ)|^1093 ≤ (6716455839303/50000000000000 : ℝ)^837
        have hw : |(-429930423/2000000000 : ℝ)|=(429930423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633131051/5000000000 : ℝ)|^1093 ≤ (43283544640991/100000000000000 : ℝ)^837
        have hw : |(2633131051/5000000000 : ℝ)|=(2633131051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266262011/10000000000 : ℝ)|^1093 ≤ (43283543664301/100000000000000 : ℝ)^837
        have hw : |(5266262011/10000000000 : ℝ)|=(5266262011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_box_5 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2685239509/5000000000 : ℝ)*x 0 + (-402154301/2000000000 : ℝ)*x 1 + (526626197/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685239509/5000000000 : ℝ)^1093 ≤ (22202729447559/50000000000000 : ℝ)^837 := by
    have hnat : (2685239509 : ℕ)^1093*50000000000000^837 ≤ 22202729447559^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685239509 5000000000 22202729447559 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402154301/2000000000 : ℝ)^1093 ≤ (6155498932961/50000000000000 : ℝ)^837 := by
    have hnat : (402154301 : ℕ)^1093*50000000000000^837 ≤ 6155498932961^837*2000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402154301 2000000000 6155498932961 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526626197/1000000000 : ℝ)^1093 ≤ (8656708644851/20000000000000 : ℝ)^837 := by
    have hnat : (526626197 : ℕ)^1093*20000000000000^837 ≤ 8656708644851^837*1000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526626197 1000000000 8656708644851 20000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685239509/5000000000 : ℝ), (-402154301/2000000000 : ℝ), (526626197/1000000000 : ℝ)] ![(22202729447559/50000000000000 : ℝ), (6155498932961/50000000000000 : ℝ), (8656708644851/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685239509/5000000000 : ℝ)|^1093 ≤ (22202729447559/50000000000000 : ℝ)^837
        have hw : |(2685239509/5000000000 : ℝ)|=(2685239509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-402154301/2000000000 : ℝ)|^1093 ≤ (6155498932961/50000000000000 : ℝ)^837
        have hw : |(-402154301/2000000000 : ℝ)|=(402154301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526626197/1000000000 : ℝ)|^1093 ≤ (8656708644851/20000000000000 : ℝ)^837
        have hw : |(526626197/1000000000 : ℝ)|=(526626197/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_box_6 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (16782747/31250000 : ℝ)*x 0 + (5266262169/10000000000 : ℝ)*x 1 + (-251346401/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16782747/31250000 : ℝ)^1093 ≤ (2220272956633/5000000000000 : ℝ)^837 := by
    have hnat : (16782747 : ℕ)^1093*5000000000000^837 ≤ 2220272956633^837*31250000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16782747 31250000 2220272956633 5000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266262169/10000000000 : ℝ)^1093 ≤ (10820886340023/25000000000000 : ℝ)^837 := by
    have hnat : (5266262169 : ℕ)^1093*25000000000000^837 ≤ 10820886340023^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266262169 10000000000 10820886340023 25000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251346401/1250000000 : ℝ)^1093 ≤ (1231099549137/10000000000000 : ℝ)^837 := by
    have hnat : (251346401 : ℕ)^1093*10000000000000^837 ≤ 1231099549137^837*1250000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251346401 1250000000 1231099549137 10000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16782747/31250000 : ℝ), (5266262169/10000000000 : ℝ), (-251346401/1250000000 : ℝ)] ![(2220272956633/5000000000000 : ℝ), (10820886340023/25000000000000 : ℝ), (1231099549137/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16782747/31250000 : ℝ)|^1093 ≤ (2220272956633/5000000000000 : ℝ)^837
        have hw : |(16782747/31250000 : ℝ)|=(16782747/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266262169/10000000000 : ℝ)|^1093 ≤ (10820886340023/25000000000000 : ℝ)^837
        have hw : |(5266262169/10000000000 : ℝ)|=(5266262169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-251346401/1250000000 : ℝ)|^1093 ≤ (1231099549137/10000000000000 : ℝ)^837
        have hw : |(-251346401/1250000000 : ℝ)|=(251346401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_box_7 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (260060709/625000000 : ℝ)*x 0 + (877234267/2000000000 : ℝ)*x 1 + (4386171561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260060709/625000000 : ℝ)^1093 ≤ (3977716523221/12500000000000 : ℝ)^837 := by
    have hnat : (260060709 : ℕ)^1093*12500000000000^837 ≤ 3977716523221^837*625000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260060709 625000000 3977716523221 12500000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (877234267/2000000000 : ℝ)^1093 ≤ (17044566377443/50000000000000 : ℝ)^837 := by
    have hnat : (877234267 : ℕ)^1093*50000000000000^837 ≤ 17044566377443^837*2000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877234267 2000000000 17044566377443 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4386171561/10000000000 : ℝ)^1093 ≤ (34089135048569/100000000000000 : ℝ)^837 := by
    have hnat : (4386171561 : ℕ)^1093*100000000000000^837 ≤ 34089135048569^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4386171561 10000000000 34089135048569 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(260060709/625000000 : ℝ), (877234267/2000000000 : ℝ), (4386171561/10000000000 : ℝ)] ![(3977716523221/12500000000000 : ℝ), (17044566377443/50000000000000 : ℝ), (34089135048569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(260060709/625000000 : ℝ)|^1093 ≤ (3977716523221/12500000000000 : ℝ)^837
        have hw : |(260060709/625000000 : ℝ)|=(260060709/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(877234267/2000000000 : ℝ)|^1093 ≤ (17044566377443/50000000000000 : ℝ)^837
        have hw : |(877234267/2000000000 : ℝ)|=(877234267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4386171561/10000000000 : ℝ)|^1093 ≤ (34089135048569/100000000000000 : ℝ)^837
        have hw : |(4386171561/10000000000 : ℝ)|=(4386171561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_box_8 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-416181709/2000000000 : ℝ)*x 0 + (1295708737/2500000000 : ℝ)*x 1 + (5400970253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416181709/2000000000 : ℝ)^1093 ≤ (12874719626201/100000000000000 : ℝ)^837 := by
    have hnat : (416181709 : ℕ)^1093*100000000000000^837 ≤ 12874719626201^837*2000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416181709 2000000000 12874719626201 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295708737/2500000000 : ℝ)^1093 ≤ (21195155395827/50000000000000 : ℝ)^837 := by
    have hnat : (1295708737 : ℕ)^1093*50000000000000^837 ≤ 21195155395827^837*2500000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295708737 2500000000 21195155395827 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400970253/10000000000 : ℝ)^1093 ≤ (44734969561747/100000000000000 : ℝ)^837 := by
    have hnat : (5400970253 : ℕ)^1093*100000000000000^837 ≤ 44734969561747^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400970253 10000000000 44734969561747 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-416181709/2000000000 : ℝ), (1295708737/2500000000 : ℝ), (5400970253/10000000000 : ℝ)] ![(12874719626201/100000000000000 : ℝ), (21195155395827/50000000000000 : ℝ), (44734969561747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-416181709/2000000000 : ℝ)|^1093 ≤ (12874719626201/100000000000000 : ℝ)^837
        have hw : |(-416181709/2000000000 : ℝ)|=(416181709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295708737/2500000000 : ℝ)|^1093 ≤ (21195155395827/50000000000000 : ℝ)^837
        have hw : |(1295708737/2500000000 : ℝ)|=(1295708737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400970253/10000000000 : ℝ)|^1093 ≤ (44734969561747/100000000000000 : ℝ)^837
        have hw : |(5400970253/10000000000 : ℝ)|=(5400970253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_box_9 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (131903351/250000000 : ℝ)*x 0 + (-1956072727/10000000000 : ℝ)*x 1 + (5400969901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131903351/250000000 : ℝ)^1093 ≤ (43389529029989/100000000000000 : ℝ)^837 := by
    have hnat : (131903351 : ℕ)^1093*100000000000000^837 ≤ 43389529029989^837*250000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131903351 250000000 43389529029989 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1956072727/10000000000 : ℝ)^1093 ≤ (1484438149413/12500000000000 : ℝ)^837 := by
    have hnat : (1956072727 : ℕ)^1093*12500000000000^837 ≤ 1484438149413^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956072727 10000000000 1484438149413 12500000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400969901/10000000000 : ℝ)^1093 ≤ (8946993150897/20000000000000 : ℝ)^837 := by
    have hnat : (5400969901 : ℕ)^1093*20000000000000^837 ≤ 8946993150897^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400969901 10000000000 8946993150897 20000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131903351/250000000 : ℝ), (-1956072727/10000000000 : ℝ), (5400969901/10000000000 : ℝ)] ![(43389529029989/100000000000000 : ℝ), (1484438149413/12500000000000 : ℝ), (8946993150897/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131903351/250000000 : ℝ)|^1093 ≤ (43389529029989/100000000000000 : ℝ)^837
        have hw : |(131903351/250000000 : ℝ)|=(131903351/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1956072727/10000000000 : ℝ)|^1093 ≤ (1484438149413/12500000000000 : ℝ)^837
        have hw : |(-1956072727/10000000000 : ℝ)|=(1956072727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400969901/10000000000 : ℝ)|^1093 ≤ (8946993150897/20000000000000 : ℝ)^837
        have hw : |(5400969901/10000000000 : ℝ)|=(5400969901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_box_10 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5276133971/10000000000 : ℝ)*x 0 + (1080193987/2000000000 : ℝ)*x 1 + (-78242911/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276133971/10000000000 : ℝ)^1093 ≤ (21694764144499/50000000000000 : ℝ)^837 := by
    have hnat : (5276133971 : ℕ)^1093*50000000000000^837 ≤ 21694764144499^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276133971 10000000000 21694764144499 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080193987/2000000000 : ℝ)^1093 ≤ (5591870765279/12500000000000 : ℝ)^837 := by
    have hnat : (1080193987 : ℕ)^1093*12500000000000^837 ≤ 5591870765279^837*2000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080193987 2000000000 5591870765279 12500000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78242911/400000000 : ℝ)^1093 ≤ (5937752787923/50000000000000 : ℝ)^837 := by
    have hnat : (78242911 : ℕ)^1093*50000000000000^837 ≤ 5937752787923^837*400000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78242911 400000000 5937752787923 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276133971/10000000000 : ℝ), (1080193987/2000000000 : ℝ), (-78242911/400000000 : ℝ)] ![(21694764144499/50000000000000 : ℝ), (5591870765279/12500000000000 : ℝ), (5937752787923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276133971/10000000000 : ℝ)|^1093 ≤ (21694764144499/50000000000000 : ℝ)^837
        have hw : |(5276133971/10000000000 : ℝ)|=(5276133971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080193987/2000000000 : ℝ)|^1093 ≤ (5591870765279/12500000000000 : ℝ)^837
        have hw : |(1080193987/2000000000 : ℝ)|=(1080193987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-78242911/400000000 : ℝ)|^1093 ≤ (5937752787923/50000000000000 : ℝ)^837
        have hw : |(-78242911/400000000 : ℝ)|=(78242911/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_box_11 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4488828977/10000000000 : ℝ)*x 0 + (4222007339/10000000000 : ℝ)*x 1 + (4222006351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4488828977/10000000000 : ℝ)^1093 ≤ (35134718634583/100000000000000 : ℝ)^837 := by
    have hnat : (4488828977 : ℕ)^1093*100000000000000^837 ≤ 35134718634583^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488828977 10000000000 35134718634583 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4222007339/10000000000 : ℝ)^1093 ≤ (16216322813963/50000000000000 : ℝ)^837 := by
    have hnat : (4222007339 : ℕ)^1093*50000000000000^837 ≤ 16216322813963^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222007339 10000000000 16216322813963 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4222006351/10000000000 : ℝ)^1093 ≤ (16216317858491/50000000000000 : ℝ)^837 := by
    have hnat : (4222006351 : ℕ)^1093*50000000000000^837 ≤ 16216317858491^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222006351 10000000000 16216317858491 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4488828977/10000000000 : ℝ), (4222007339/10000000000 : ℝ), (4222006351/10000000000 : ℝ)] ![(35134718634583/100000000000000 : ℝ), (16216322813963/50000000000000 : ℝ), (16216317858491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4488828977/10000000000 : ℝ)|^1093 ≤ (35134718634583/100000000000000 : ℝ)^837
        have hw : |(4488828977/10000000000 : ℝ)|=(4488828977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4222007339/10000000000 : ℝ)|^1093 ≤ (16216322813963/50000000000000 : ℝ)^837
        have hw : |(4222007339/10000000000 : ℝ)|=(4222007339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4222006351/10000000000 : ℝ)|^1093 ≤ (16216317858491/50000000000000 : ℝ)^837
        have hw : |(4222006351/10000000000 : ℝ)|=(4222006351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_box_12 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-946028081/5000000000 : ℝ)*x 0 + (1093670969/2000000000 : ℝ)*x 1 + (2627572397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (946028081/5000000000 : ℝ)^1093 ≤ (2274108719597/20000000000000 : ℝ)^837 := by
    have hnat : (946028081 : ℕ)^1093*20000000000000^837 ≤ 2274108719597^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946028081 5000000000 2274108719597 20000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093670969/2000000000 : ℝ)^1093 ≤ (45465193603919/100000000000000 : ℝ)^837 := by
    have hnat : (1093670969 : ℕ)^1093*100000000000000^837 ≤ 45465193603919^837*2000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093670969 2000000000 45465193603919 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627572397/5000000000 : ℝ)^1093 ≤ (43164262783349/100000000000000 : ℝ)^837 := by
    have hnat : (2627572397 : ℕ)^1093*100000000000000^837 ≤ 43164262783349^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627572397 5000000000 43164262783349 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-946028081/5000000000 : ℝ), (1093670969/2000000000 : ℝ), (2627572397/5000000000 : ℝ)] ![(2274108719597/20000000000000 : ℝ), (45465193603919/100000000000000 : ℝ), (43164262783349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-946028081/5000000000 : ℝ)|^1093 ≤ (2274108719597/20000000000000 : ℝ)^837
        have hw : |(-946028081/5000000000 : ℝ)|=(946028081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093670969/2000000000 : ℝ)|^1093 ≤ (45465193603919/100000000000000 : ℝ)^837
        have hw : |(1093670969/2000000000 : ℝ)|=(1093670969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627572397/5000000000 : ℝ)|^1093 ≤ (43164262783349/100000000000000 : ℝ)^837
        have hw : |(2627572397/5000000000 : ℝ)|=(2627572397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_box_13 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5378263439/10000000000 : ℝ)*x 0 + (-2015174687/10000000000 : ℝ)*x 1 + (1051028861/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378263439/10000000000 : ℝ)^1093 ≤ (11122382201303/25000000000000 : ℝ)^837 := by
    have hnat : (5378263439 : ℕ)^1093*25000000000000^837 ≤ 11122382201303^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378263439 10000000000 11122382201303 25000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015174687/10000000000 : ℝ)^1093 ≤ (12346213637889/100000000000000 : ℝ)^837 := by
    have hnat : (2015174687 : ℕ)^1093*100000000000000^837 ≤ 12346213637889^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015174687 10000000000 12346213637889 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051028861/2000000000 : ℝ)^1093 ≤ (43164257538377/100000000000000 : ℝ)^837 := by
    have hnat : (1051028861 : ℕ)^1093*100000000000000^837 ≤ 43164257538377^837*2000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051028861 2000000000 43164257538377 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378263439/10000000000 : ℝ), (-2015174687/10000000000 : ℝ), (1051028861/2000000000 : ℝ)] ![(11122382201303/25000000000000 : ℝ), (12346213637889/100000000000000 : ℝ), (43164257538377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378263439/10000000000 : ℝ)|^1093 ≤ (11122382201303/25000000000000 : ℝ)^837
        have hw : |(5378263439/10000000000 : ℝ)|=(5378263439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2015174687/10000000000 : ℝ)|^1093 ≤ (12346213637889/100000000000000 : ℝ)^837
        have hw : |(-2015174687/10000000000 : ℝ)|=(2015174687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051028861/2000000000 : ℝ)|^1093 ≤ (43164257538377/100000000000000 : ℝ)^837
        have hw : |(1051028861/2000000000 : ℝ)|=(1051028861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_box_14 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2689131799/5000000000 : ℝ)*x 0 + (5255144149/10000000000 : ℝ)*x 1 + (-1007587341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689131799/5000000000 : ℝ)^1093 ≤ (8897906104551/20000000000000 : ℝ)^837 := by
    have hnat : (2689131799 : ℕ)^1093*20000000000000^837 ≤ 8897906104551^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689131799 5000000000 8897906104551 20000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255144149/10000000000 : ℝ)^1093 ≤ (21582127932567/50000000000000 : ℝ)^837 := by
    have hnat : (5255144149 : ℕ)^1093*50000000000000^837 ≤ 21582127932567^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255144149 10000000000 21582127932567 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007587341/5000000000 : ℝ)^1093 ≤ (6173106798943/50000000000000 : ℝ)^837 := by
    have hnat : (1007587341 : ℕ)^1093*50000000000000^837 ≤ 6173106798943^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007587341 5000000000 6173106798943 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689131799/5000000000 : ℝ), (5255144149/10000000000 : ℝ), (-1007587341/5000000000 : ℝ)] ![(8897906104551/20000000000000 : ℝ), (21582127932567/50000000000000 : ℝ), (6173106798943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689131799/5000000000 : ℝ)|^1093 ≤ (8897906104551/20000000000000 : ℝ)^837
        have hw : |(2689131799/5000000000 : ℝ)|=(2689131799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255144149/10000000000 : ℝ)|^1093 ≤ (21582127932567/50000000000000 : ℝ)^837
        have hw : |(5255144149/10000000000 : ℝ)|=(5255144149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1007587341/5000000000 : ℝ)|^1093 ≤ (6173106798943/50000000000000 : ℝ)^837
        have hw : |(-1007587341/5000000000 : ℝ)|=(1007587341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_box_15 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (103335447/250000000 : ℝ)*x 0 + (4399707977/10000000000 : ℝ)*x 1 + (4399707487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103335447/250000000 : ℝ)^1093 ≤ (15773420977161/50000000000000 : ℝ)^837 := by
    have hnat : (103335447 : ℕ)^1093*50000000000000^837 ≤ 15773420977161^837*250000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103335447 250000000 15773420977161 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4399707977/10000000000 : ℝ)^1093 ≤ (17113290750939/50000000000000 : ℝ)^837 := by
    have hnat : (4399707977 : ℕ)^1093*50000000000000^837 ≤ 17113290750939^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4399707977 10000000000 17113290750939 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4399707487/10000000000 : ℝ)^1093 ≤ (17113288262079/50000000000000 : ℝ)^837 := by
    have hnat : (4399707487 : ℕ)^1093*50000000000000^837 ≤ 17113288262079^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4399707487 10000000000 17113288262079 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103335447/250000000 : ℝ), (4399707977/10000000000 : ℝ), (4399707487/10000000000 : ℝ)] ![(15773420977161/50000000000000 : ℝ), (17113290750939/50000000000000 : ℝ), (17113288262079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103335447/250000000 : ℝ)|^1093 ≤ (15773420977161/50000000000000 : ℝ)^837
        have hw : |(103335447/250000000 : ℝ)|=(103335447/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4399707977/10000000000 : ℝ)|^1093 ≤ (17113290750939/50000000000000 : ℝ)^837
        have hw : |(4399707977/10000000000 : ℝ)|=(4399707977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4399707487/10000000000 : ℝ)|^1093 ≤ (17113288262079/50000000000000 : ℝ)^837
        have hw : |(4399707487/10000000000 : ℝ)|=(4399707487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1412_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157493367/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62889/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59079/100000 : ℝ) ∧ (40177/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84621/100000 : ℝ) := by
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
  have lower0 : (2261/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2261/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2261/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2261/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2261/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2261/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2261/20000 : ℝ) ^ (4371/1024 : ℝ) ≤ (1819129577924779/20000000000000000000 : ℝ) := by
    have hpowers : (2261/20000 : ℝ)^4371 ≤ (1819129577924779/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2261 : ℕ)^4371*20000000000000000000^1024 ≤ 1819129577924779^1024*20000^4371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2261 20000 1819129577924779 20000000000000000000 4371 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2261/20000 : ℝ)) (X := (1819129577924779/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3687/25000 : ℝ) ^ (4371/1024 : ℝ) ≤ (3536730062358593/12500000000000000000 : ℝ) := by
    have hpowers : (3687/25000 : ℝ)^4371 ≤ (3536730062358593/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3687 : ℕ)^4371*12500000000000000000^1024 ≤ 3536730062358593^1024*25000^4371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3687 25000 3536730062358593 12500000000000000000 4371 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3687/25000 : ℝ)) (X := (3536730062358593/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001819129577924779/10000000000000000000 : ℝ) ≤ (5000213070116931/5000000000000000 : ℝ) ^ (4371/1024 : ℝ) := by
    have hpowers : (10001819129577924779/10000000000000000000 : ℝ)^1024 ≤ (5000213070116931/5000000000000000 : ℝ)^4371 := by
      have hnat : (10001819129577924779 : ℕ)^1024*5000000000000000^4371 ≤ 5000213070116931^4371*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001819129577924779 10000000000000000000 5000213070116931 5000000000000000 1024 4371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000213070116931/5000000000000000 : ℝ)) (X := (10001819129577924779/10000000000000000000 : ℝ)) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037389488388492639/100000000000000000000 : ℝ) ≤ (5000437901584491/5000000000000000 : ℝ) ^ (4371/1024 : ℝ) := by
    have hpowers : (100037389488388492639/100000000000000000000 : ℝ)^1024 ≤ (5000437901584491/5000000000000000 : ℝ)^4371 := by
      have hnat : (100037389488388492639 : ℕ)^1024*5000000000000000^4371 ≤ 5000437901584491^4371*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037389488388492639 100000000000000000000 5000437901584491 5000000000000000 1024 4371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000437901584491/5000000000000000 : ℝ)) (X := (100037389488388492639/100000000000000000000 : ℝ)) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253536730062358593/6250000000000000000 : ℝ) ≤ (5000662733052051/5000000000000000 : ℝ) ^ (4371/1024 : ℝ) := by
    have hpowers : (6253536730062358593/6250000000000000000 : ℝ)^1024 ≤ (5000662733052051/5000000000000000 : ℝ)^4371 := by
      have hnat : (6253536730062358593 : ℕ)^1024*5000000000000000^4371 ≤ 5000662733052051^4371*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253536730062358593 6250000000000000000 5000662733052051 5000000000000000 1024 4371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000662733052051/5000000000000000 : ℝ)) (X := (6253536730062358593/6250000000000000000 : ℝ)) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1819129577924779/20000000000000000000 : ℝ) ≤ ((17210650160931061833/17215000000000000000 : ℝ)+2*(5620786689/4303750000000 : ℝ)*(2261/20000 : ℝ))^(4371/1024 : ℝ) := by
    rw [show (17210650160931061833/17215000000000000000 : ℝ)+2*(5620786689/4303750000000 : ℝ)*(2261/20000 : ℝ)=(5000213070116931/5000000000000000 : ℝ) by norm_num, show 1+2*(1819129577924779/20000000000000000000 : ℝ)=(10001819129577924779/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3536730062358593/12500000000000000000 : ℝ)+(1819129577924779/20000000000000000000 : ℝ) ≤ ((17210650160931061833/17215000000000000000 : ℝ)+(5620786689/4303750000000 : ℝ)*((3687/25000 : ℝ)+(2261/20000 : ℝ)))^(4371/1024 : ℝ) := by
    rw [show (17210650160931061833/17215000000000000000 : ℝ)+(5620786689/4303750000000 : ℝ)*((3687/25000 : ℝ)+(2261/20000 : ℝ))=(5000437901584491/5000000000000000 : ℝ) by norm_num, show 1+(3536730062358593/12500000000000000000 : ℝ)+(1819129577924779/20000000000000000000 : ℝ)=(100037389488388492639/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3536730062358593/12500000000000000000 : ℝ) ≤ ((17210650160931061833/17215000000000000000 : ℝ)+2*(5620786689/4303750000000 : ℝ)*(3687/25000 : ℝ))^(4371/1024 : ℝ) := by
    rw [show (17210650160931061833/17215000000000000000 : ℝ)+2*(5620786689/4303750000000 : ℝ)*(3687/25000 : ℝ)=(5000662733052051/5000000000000000 : ℝ) by norm_num, show 1+2*(3536730062358593/12500000000000000000 : ℝ)=(6253536730062358593/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17210650160931061833/17215000000000000000 : ℝ)*(X 1 0+X 2 0)+(5620786689/4303750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4371/1024 : ℝ)) (lo := (2261/20000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (17210650160931061833/17215000000000000000 : ℝ)) (alpha := (5620786689/4303750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17210650160931061833/17215000000000000000 : ℝ)*(X 0 1+X 2 1)+(5620786689/4303750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4371/1024 : ℝ)) (lo := (2261/20000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (17210650160931061833/17215000000000000000 : ℝ)) (alpha := (5620786689/4303750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17210650160931061833/17215000000000000000 : ℝ)*(X 0 2+X 1 2)+(5620786689/4303750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4371/1024 : ℝ)) (lo := (2261/20000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (17210650160931061833/17215000000000000000 : ℝ)) (alpha := (5620786689/4303750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1823103849/10000000000 : ℝ)*X 0 0+(5386985329/10000000000 : ℝ)*X 0 1+(538698501/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642966279/5000000000 : ℝ)*X 1 0+(-245233183/1250000000 : ℝ)*X 1 1+(1077397007/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642965961/5000000000 : ℝ)*X 2 0+(336686583/625000000 : ℝ)*X 2 1+(-980932963/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2227645987/5000000000 : ℝ)*X 0 0+(4239062433/10000000000 : ℝ)*X 0 1+(1059765653/2500000000 : ℝ)*X 0 2+(2227645987/5000000000 : ℝ)*X 1 0+(4239062433/10000000000 : ℝ)*X 1 1+(1059765653/2500000000 : ℝ)*X 1 2+(2227645987/5000000000 : ℝ)*X 2 0+(4239062433/10000000000 : ℝ)*X 2 1+(1059765653/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-429930423/2000000000 : ℝ)*X 0 0+(2633131051/5000000000 : ℝ)*X 0 1+(5266262011/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2685239509/5000000000 : ℝ)*X 1 0+(-402154301/2000000000 : ℝ)*X 1 1+(526626197/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((16782747/31250000 : ℝ)*X 2 0+(5266262169/10000000000 : ℝ)*X 2 1+(-251346401/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((260060709/625000000 : ℝ)*X 0 0+(877234267/2000000000 : ℝ)*X 0 1+(4386171561/10000000000 : ℝ)*X 0 2+(260060709/625000000 : ℝ)*X 1 0+(877234267/2000000000 : ℝ)*X 1 1+(4386171561/10000000000 : ℝ)*X 1 2+(260060709/625000000 : ℝ)*X 2 0+(877234267/2000000000 : ℝ)*X 2 1+(4386171561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-416181709/2000000000 : ℝ)*X 0 0+(1295708737/2500000000 : ℝ)*X 0 1+(5400970253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((131903351/250000000 : ℝ)*X 1 0+(-1956072727/10000000000 : ℝ)*X 1 1+(5400969901/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276133971/10000000000 : ℝ)*X 2 0+(1080193987/2000000000 : ℝ)*X 2 1+(-78242911/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4488828977/10000000000 : ℝ)*X 0 0+(4222007339/10000000000 : ℝ)*X 0 1+(4222006351/10000000000 : ℝ)*X 0 2+(4488828977/10000000000 : ℝ)*X 1 0+(4222007339/10000000000 : ℝ)*X 1 1+(4222006351/10000000000 : ℝ)*X 1 2+(4488828977/10000000000 : ℝ)*X 2 0+(4222007339/10000000000 : ℝ)*X 2 1+(4222006351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-946028081/5000000000 : ℝ)*X 0 0+(1093670969/2000000000 : ℝ)*X 0 1+(2627572397/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5378263439/10000000000 : ℝ)*X 1 0+(-2015174687/10000000000 : ℝ)*X 1 1+(1051028861/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2689131799/5000000000 : ℝ)*X 2 0+(5255144149/10000000000 : ℝ)*X 2 1+(-1007587341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((103335447/250000000 : ℝ)*X 0 0+(4399707977/10000000000 : ℝ)*X 0 1+(4399707487/10000000000 : ℝ)*X 0 2+(103335447/250000000 : ℝ)*X 1 0+(4399707977/10000000000 : ℝ)*X 1 1+(4399707487/10000000000 : ℝ)*X 1 2+(103335447/250000000 : ℝ)*X 2 0+(4399707977/10000000000 : ℝ)*X 2 1+(4399707487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62889/100000 : ℝ) ≤ (-270649286003837928055899969/430375000000000000000000000 : ℝ) := by norm_num
    linear_combination (56886223/100000000000000 : ℝ)*(upper0) + (22548693/100000000000000 : ℝ)*(lower1) + (102562699/100000000000000 : ℝ)*(lower2) + (3256861/10000000000000 : ℝ)*(lower3) + (749532952694539/25000000000000 : ℝ)*(major0) + (749532952694539/25000000000000 : ℝ)*(major1) + (749532952694539/25000000000000 : ℝ)*(major2) + (54572351/2000000000000 : ℝ)*(sp1) + (2056784022084141/50000000000000 : ℝ)*(sp4) + (4113567252699341/100000000000000 : ℝ)*(sp5) + (4113479490181483/100000000000000 : ℝ)*(sp6) + (237956990498063/12500000000000 : ℝ)*(sp7) + (30267947/1562500000000 : ℝ)*(sp8) + (5655695963/6250000000000 : ℝ)*(sp14) + (237956990498063/12500000000000 : ℝ)*(f.failure) + (411356998131689/10000000000000 : ℝ)*(f.sum) + (6818367376427/1721500000000000000000000000 : ℝ)*base66 + (1557408085168929987/430375000000000000000000000000000 : ℝ)*base67 + (341875386721820013/430375000000000000000000000000000 : ℝ)*base70 + (4427291735295820013/430375000000000000000000000000000 : ℝ)*base72 + (75537516647039/3443000000000000000000000000 : ℝ)*base73 + (1205480645447929987/430375000000000000000000000000000 : ℝ)*base75 + (2793921460025570013/430375000000000000000000000000000 : ℝ)*base78 + (16204729174912304987/430375000000000000000000000000000 : ℝ)*base79 + (131321377783/53796875000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1151879/1250000000000000000000 : ℝ)*base90 + (1151879/1250000000000000000000 : ℝ)*base92 + (1151879/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59079/100000 : ℝ) ≤ (254272157131478994478122411565233/430375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36216863/50000000000000 : ℝ)*(lower0) + (145193697/50000000000000 : ℝ)*(upper2) + (70665093/100000000000000 : ℝ)*(lower5) + (1534582858803911/50000000000000 : ℝ)*(major0) + (1534582858803911/50000000000000 : ℝ)*(major1) + (1534582858803911/50000000000000 : ℝ)*(major2) + (1042469444647961/25000000000000 : ℝ)*(sp0) + (4169876814245437/100000000000000 : ℝ)*(sp1) + (833974188011461/20000000000000 : ℝ)*(sp2) + (1948752623431141/100000000000000 : ℝ)*(sp3) + (1029610409/50000000000000 : ℝ)*(sp5) + (1218650089/20000000000000 : ℝ)*(sp7) + (158668179/2000000000000 : ℝ)*(sp10) + (1094874411/100000000000000 : ℝ)*(sp12) + (974379358340793/50000000000000 : ℝ)*(f.failure) + (833975774693251/20000000000000 : ℝ)*(f.sum) + (1036782033773/172150000000000000000000000 : ℝ)*base65 + (7306698021064978863/860750000000000000000000000000000 : ℝ)*base67 + (5070666106035978863/860750000000000000000000000000000 : ℝ)*base69 + (268692252301228863/860750000000000000000000000000000 : ℝ)*base71 + (42991607054559/1721500000000000000000000000 : ℝ)*base73 + (3336253150890228863/860750000000000000000000000000000 : ℝ)*base75 + (5605173467833728863/860750000000000000000000000000000 : ℝ)*base77 + (10268787253235728863/860750000000000000000000000000000 : ℝ)*base79 + (14118755949877/3443000000000000000000000000 : ℝ)*base81 + (76979969/5000000000000000000000 : ℝ)*base90 + (76979969/5000000000000000000000 : ℝ)*base92 + (76979969/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40177/50000 : ℝ) ≤ (691670235649764270606889224739869/860750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38375693/100000000000000 : ℝ)*(upper1) + (44459519/50000000000000 : ℝ)*(upper4) + (53362021/20000000000000 : ℝ)*(lower5) + (3377968707936877/100000000000000 : ℝ)*(major0) + (3377968707936877/100000000000000 : ℝ)*(major1) + (3377968707936877/100000000000000 : ℝ)*(major2) + (90713637/312500000000 : ℝ)*(sp1) + (76033416201/50000000000000 : ℝ)*(sp2) + (65274460401/100000000000000 : ℝ)*(sp3) + (12143884369/100000000000000 : ℝ)*(sp4) + (4584307342762447/100000000000000 : ℝ)*(sp8) + (143259076821343/3125000000000 : ℝ)*(sp9) + (2292083709907207/50000000000000 : ℝ)*(sp10) + (2144767090407941/100000000000000 : ℝ)*(sp11) + (1072416182434171/50000000000000 : ℝ)*(f.failure) + (143259983957713/3125000000000 : ℝ)*(f.sum) + (1347101797953/688600000000000000000000000 : ℝ)*base65 + (6953026137399084459/1721500000000000000000000000000000 : ℝ)*base68 + (223475759579584459/1721500000000000000000000000000000 : ℝ)*base70 + (4618427107696584459/1721500000000000000000000000000000 : ℝ)*base72 + (479326408911/430375000000000000000000000 : ℝ)*base73 + (11581837433238584459/1721500000000000000000000000000000 : ℝ)*base76 + (8792356861173584459/1721500000000000000000000000000000 : ℝ)*base78 + (6254371806167084459/1721500000000000000000000000000000 : ℝ)*base80 + (1789307138761/688600000000000000000000000 : ℝ)*base81 + (3356243/5000000000000000000000 : ℝ)*base90 + (3356243/5000000000000000000000 : ℝ)*base92 + (3356243/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-84621/100000 : ℝ) ≤ (-182088105622675116930258294387021/215187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106565491/100000000000000 : ℝ)*(lower0) + (21421991/100000000000000 : ℝ)*(lower1) + (41406841/100000000000000 : ℝ)*(lower2) + (853813340302507/25000000000000 : ℝ)*(major0) + (853813340302507/25000000000000 : ℝ)*(major1) + (853813340302507/25000000000000 : ℝ)*(major2) + (1477036349/100000000000000 : ℝ)*(sp0) + (121539179843/50000000000000 : ℝ)*(sp5) + (142840399479/50000000000000 : ℝ)*(sp6) + (8560332961/50000000000000 : ℝ)*(sp7) + (938041040694963/20000000000000 : ℝ)*(sp12) + (4689963602151477/100000000000000 : ℝ)*(sp13) + (2344960499856103/50000000000000 : ℝ)*(sp14) + (542122259234069/25000000000000 : ℝ)*(sp15) + (1084253078801099/50000000000000 : ℝ)*(f.failure) + (1172551670127791/25000000000000 : ℝ)*(f.sum) + (4262544210041/3443000000000000000000000000 : ℝ)*base65 + (4149887065012834669/430375000000000000000000000000000 : ℝ)*base68 + (6544176049831334669/430375000000000000000000000000000 : ℝ)*base70 + (4876704270760709669/430375000000000000000000000000000 : ℝ)*base72 + (49568838863427/3443000000000000000000000000 : ℝ)*base74 + (5864759522845709669/430375000000000000000000000000000 : ℝ)*base76 + (3323007378679584669/430375000000000000000000000000000 : ℝ)*base78 + (14630099364300334669/430375000000000000000000000000000 : ℝ)*base80 + (847056894429/1721500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (4810333/5000000000000000000000 : ℝ)*base89 + (4810333/5000000000000000000000 : ℝ)*base91 + (4810333/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1412_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157493367/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62889/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59079/100000 : ℝ) else (40177/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84621/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1412_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1412_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157493367/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62889/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59079/100000 : ℝ) else (40177/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84621/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1412_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1412_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157493367/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62889/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59079/100000 : ℝ) else (40177/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84621/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1412_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

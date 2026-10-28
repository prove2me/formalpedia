-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1115_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:07:13.523749+00:00
-- url     : https://prove2.me/submissions/6ab80e21-1876-471a-8a27-3a36402fc3ec

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
theorem support_rectangle_w1115_s3_0 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-543937873/2500000000 : ℝ)*x 0 + (2716018381/5000000000 : ℝ)*x 1 + (5229466537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543937873/2500000000 : ℝ)^2077 ≤ (2642006164209/20000000000000 : ℝ)^1565 := by
    have hnat : (543937873 : ℕ)^2077*20000000000000^1565 ≤ 2642006164209^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543937873 2500000000 2642006164209 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716018381/5000000000 : ℝ)^2077 ≤ (44489140136137/100000000000000 : ℝ)^1565 := by
    have hnat : (2716018381 : ℕ)^2077*100000000000000^1565 ≤ 44489140136137^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716018381 5000000000 44489140136137 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229466537/10000000000 : ℝ)^2077 ≤ (8460165805839/20000000000000 : ℝ)^1565 := by
    have hnat : (5229466537 : ℕ)^2077*20000000000000^1565 ≤ 8460165805839^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229466537 10000000000 8460165805839 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-543937873/2500000000 : ℝ), (2716018381/5000000000 : ℝ), (5229466537/10000000000 : ℝ)] ![(2642006164209/20000000000000 : ℝ), (44489140136137/100000000000000 : ℝ), (8460165805839/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-543937873/2500000000 : ℝ)|^2077 ≤ (2642006164209/20000000000000 : ℝ)^1565
        have hw : |(-543937873/2500000000 : ℝ)|=(543937873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716018381/5000000000 : ℝ)|^2077 ≤ (44489140136137/100000000000000 : ℝ)^1565
        have hw : |(2716018381/5000000000 : ℝ)|=(2716018381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229466537/10000000000 : ℝ)|^2077 ≤ (8460165805839/20000000000000 : ℝ)^1565
        have hw : |(5229466537/10000000000 : ℝ)|=(5229466537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s3_1 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5354455183/10000000000 : ℝ)*x 0 + (-2279361457/10000000000 : ℝ)*x 1 + (5229466543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354455183/10000000000 : ℝ)^2077 ≤ (1745913442591/4000000000000 : ℝ)^1565 := by
    have hnat : (5354455183 : ℕ)^2077*4000000000000^1565 ≤ 1745913442591^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354455183 10000000000 1745913442591 4000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2279361457/10000000000 : ℝ)^2077 ≤ (7025667414919/50000000000000 : ℝ)^1565 := by
    have hnat : (2279361457 : ℕ)^2077*50000000000000^1565 ≤ 7025667414919^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279361457 10000000000 7025667414919 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229466543/10000000000 : ℝ)^2077 ≤ (42300829093607/100000000000000 : ℝ)^1565 := by
    have hnat : (5229466543 : ℕ)^2077*100000000000000^1565 ≤ 42300829093607^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229466543 10000000000 42300829093607 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354455183/10000000000 : ℝ), (-2279361457/10000000000 : ℝ), (5229466543/10000000000 : ℝ)] ![(1745913442591/4000000000000 : ℝ), (7025667414919/50000000000000 : ℝ), (42300829093607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354455183/10000000000 : ℝ)|^2077 ≤ (1745913442591/4000000000000 : ℝ)^1565
        have hw : |(5354455183/10000000000 : ℝ)|=(5354455183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2279361457/10000000000 : ℝ)|^2077 ≤ (7025667414919/50000000000000 : ℝ)^1565
        have hw : |(-2279361457/10000000000 : ℝ)|=(2279361457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229466543/10000000000 : ℝ)|^2077 ≤ (42300829093607/100000000000000 : ℝ)^1565
        have hw : |(5229466543/10000000000 : ℝ)|=(5229466543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s3_2 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (53544553/100000000 : ℝ)*x 0 + (1045893329/2000000000 : ℝ)*x 1 + (-142460073/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53544553/100000000 : ℝ)^2077 ≤ (21823918665273/50000000000000 : ℝ)^1565 := by
    have hnat : (53544553 : ℕ)^2077*50000000000000^1565 ≤ 21823918665273^1565*100000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53544553 100000000 21823918665273 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045893329/2000000000 : ℝ)^2077 ≤ (21150415094303/50000000000000 : ℝ)^1565 := by
    have hnat : (1045893329 : ℕ)^2077*50000000000000^1565 ≤ 21150415094303^1565*2000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045893329 2000000000 21150415094303 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (142460073/625000000 : ℝ)^2077 ≤ (14051332465419/100000000000000 : ℝ)^1565 := by
    have hnat : (142460073 : ℕ)^2077*100000000000000^1565 ≤ 14051332465419^1565*625000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142460073 625000000 14051332465419 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53544553/100000000 : ℝ), (1045893329/2000000000 : ℝ), (-142460073/625000000 : ℝ)] ![(21823918665273/50000000000000 : ℝ), (21150415094303/50000000000000 : ℝ), (14051332465419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53544553/100000000 : ℝ)|^2077 ≤ (21823918665273/50000000000000 : ℝ)^1565
        have hw : |(53544553/100000000 : ℝ)|=(53544553/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045893329/2000000000 : ℝ)|^2077 ≤ (21150415094303/50000000000000 : ℝ)^1565
        have hw : |(1045893329/2000000000 : ℝ)|=(1045893329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-142460073/625000000 : ℝ)|^2077 ≤ (14051332465419/100000000000000 : ℝ)^1565
        have hw : |(-142460073/625000000 : ℝ)|=(142460073/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s3_3 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (545756579/1250000000 : ℝ)*x 0 + (1042554009/2500000000 : ℝ)*x 1 + (2285545173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545756579/1250000000 : ℝ)^2077 ≤ (3329214020829/10000000000000 : ℝ)^1565 := by
    have hnat : (545756579 : ℕ)^2077*10000000000000^1565 ≤ 3329214020829^1565*1250000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545756579 1250000000 3329214020829 10000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042554009/2500000000 : ℝ)^2077 ≤ (7831247429613/25000000000000 : ℝ)^1565 := by
    have hnat : (1042554009 : ℕ)^2077*25000000000000^1565 ≤ 7831247429613^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042554009 2500000000 7831247429613 25000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2285545173/5000000000 : ℝ)^2077 ≤ (1769143503133/5000000000000 : ℝ)^1565 := by
    have hnat : (2285545173 : ℕ)^2077*5000000000000^1565 ≤ 1769143503133^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285545173 5000000000 1769143503133 5000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545756579/1250000000 : ℝ), (1042554009/2500000000 : ℝ), (2285545173/5000000000 : ℝ)] ![(3329214020829/10000000000000 : ℝ), (7831247429613/25000000000000 : ℝ), (1769143503133/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545756579/1250000000 : ℝ)|^2077 ≤ (3329214020829/10000000000000 : ℝ)^1565
        have hw : |(545756579/1250000000 : ℝ)|=(545756579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042554009/2500000000 : ℝ)|^2077 ≤ (7831247429613/25000000000000 : ℝ)^1565
        have hw : |(1042554009/2500000000 : ℝ)|=(1042554009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2285545173/5000000000 : ℝ)|^2077 ≤ (1769143503133/5000000000000 : ℝ)^1565
        have hw : |(2285545173/5000000000 : ℝ)|=(2285545173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s3_4 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2175771383/10000000000 : ℝ)*x 0 + (5230267863/10000000000 : ℝ)*x 1 + (678903819/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175771383/10000000000 : ℝ)^2077 ≤ (6605095549531/50000000000000 : ℝ)^1565 := by
    have hnat : (2175771383 : ℕ)^2077*50000000000000^1565 ≤ 6605095549531^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175771383 10000000000 6605095549531 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230267863/10000000000 : ℝ)^2077 ≤ (42309431709123/100000000000000 : ℝ)^1565 := by
    have hnat : (5230267863 : ℕ)^2077*100000000000000^1565 ≤ 42309431709123^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230267863 10000000000 42309431709123 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678903819/1250000000 : ℝ)^2077 ≤ (2224018858531/5000000000000 : ℝ)^1565 := by
    have hnat : (678903819 : ℕ)^2077*5000000000000^1565 ≤ 2224018858531^1565*1250000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678903819 1250000000 2224018858531 5000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2175771383/10000000000 : ℝ), (5230267863/10000000000 : ℝ), (678903819/1250000000 : ℝ)] ![(6605095549531/50000000000000 : ℝ), (42309431709123/100000000000000 : ℝ), (2224018858531/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2175771383/10000000000 : ℝ)|^2077 ≤ (6605095549531/50000000000000 : ℝ)^1565
        have hw : |(-2175771383/10000000000 : ℝ)|=(2175771383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230267863/10000000000 : ℝ)|^2077 ≤ (42309431709123/100000000000000 : ℝ)^1565
        have hw : |(5230267863/10000000000 : ℝ)|=(5230267863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678903819/1250000000 : ℝ)|^2077 ≤ (2224018858531/5000000000000 : ℝ)^1565
        have hw : |(678903819/1250000000 : ℝ)|=(678903819/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s3_5 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1325809247/2500000000 : ℝ)*x 0 + (-51939941/250000000 : ℝ)*x 1 + (5431230753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325809247/2500000000 : ℝ)^2077 ≤ (21547298837111/50000000000000 : ℝ)^1565 := by
    have hnat : (1325809247 : ℕ)^2077*50000000000000^1565 ≤ 21547298837111^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325809247 2500000000 21547298837111 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51939941/250000000 : ℝ)^2077 ≤ (12425022956881/100000000000000 : ℝ)^1565 := by
    have hnat : (51939941 : ℕ)^2077*100000000000000^1565 ≤ 12425022956881^1565*250000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51939941 250000000 12425022956881 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431230753/10000000000 : ℝ)^2077 ≤ (44480379355303/100000000000000 : ℝ)^1565 := by
    have hnat : (5431230753 : ℕ)^2077*100000000000000^1565 ≤ 44480379355303^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431230753 10000000000 44480379355303 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325809247/2500000000 : ℝ), (-51939941/250000000 : ℝ), (5431230753/10000000000 : ℝ)] ![(21547298837111/50000000000000 : ℝ), (12425022956881/100000000000000 : ℝ), (44480379355303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325809247/2500000000 : ℝ)|^2077 ≤ (21547298837111/50000000000000 : ℝ)^1565
        have hw : |(1325809247/2500000000 : ℝ)|=(1325809247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-51939941/250000000 : ℝ)|^2077 ≤ (12425022956881/100000000000000 : ℝ)^1565
        have hw : |(-51939941/250000000 : ℝ)|=(51939941/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431230753/10000000000 : ℝ)|^2077 ≤ (44480379355303/100000000000000 : ℝ)^1565
        have hw : |(5431230753/10000000000 : ℝ)|=(5431230753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s3_6 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2651618907/5000000000 : ℝ)*x 0 + (5431230909/10000000000 : ℝ)*x 1 + (-2077596303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651618907/5000000000 : ℝ)^2077 ≤ (430946065823/1000000000000 : ℝ)^1565 := by
    have hnat : (2651618907 : ℕ)^2077*1000000000000^1565 ≤ 430946065823^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651618907 5000000000 430946065823 1000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431230909/10000000000 : ℝ)^2077 ≤ (22240190525439/50000000000000 : ℝ)^1565 := by
    have hnat : (5431230909 : ℕ)^2077*50000000000000^1565 ≤ 22240190525439^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431230909 10000000000 22240190525439 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2077596303/10000000000 : ℝ)^2077 ≤ (3106253086269/25000000000000 : ℝ)^1565 := by
    have hnat : (2077596303 : ℕ)^2077*25000000000000^1565 ≤ 3106253086269^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077596303 10000000000 3106253086269 25000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651618907/5000000000 : ℝ), (5431230909/10000000000 : ℝ), (-2077596303/10000000000 : ℝ)] ![(430946065823/1000000000000 : ℝ), (22240190525439/50000000000000 : ℝ), (3106253086269/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651618907/5000000000 : ℝ)|^2077 ≤ (430946065823/1000000000000 : ℝ)^1565
        have hw : |(2651618907/5000000000 : ℝ)|=(2651618907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431230909/10000000000 : ℝ)|^2077 ≤ (22240190525439/50000000000000 : ℝ)^1565
        have hw : |(5431230909/10000000000 : ℝ)|=(5431230909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2077596303/10000000000 : ℝ)|^2077 ≤ (3106253086269/25000000000000 : ℝ)^1565
        have hw : |(-2077596303/10000000000 : ℝ)|=(2077596303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s3_7 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (873218159/2000000000 : ℝ)*x 0 + (228475267/500000000 : ℝ)*x 1 + (521476303/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873218159/2000000000 : ℝ)^2077 ≤ (16646263206707/50000000000000 : ℝ)^1565 := by
    have hnat : (873218159 : ℕ)^2077*50000000000000^1565 ≤ 16646263206707^1565*2000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873218159 2000000000 16646263206707 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (228475267/500000000 : ℝ)^2077 ≤ (3536658829017/10000000000000 : ℝ)^1565 := by
    have hnat : (228475267 : ℕ)^2077*10000000000000^1565 ≤ 3536658829017^1565*500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228475267 500000000 3536658829017 10000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521476303/1250000000 : ℝ)^2077 ≤ (31340885274057/100000000000000 : ℝ)^1565 := by
    have hnat : (521476303 : ℕ)^2077*100000000000000^1565 ≤ 31340885274057^1565*1250000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521476303 1250000000 31340885274057 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873218159/2000000000 : ℝ), (228475267/500000000 : ℝ), (521476303/1250000000 : ℝ)] ![(16646263206707/50000000000000 : ℝ), (3536658829017/10000000000000 : ℝ), (31340885274057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873218159/2000000000 : ℝ)|^2077 ≤ (16646263206707/50000000000000 : ℝ)^1565
        have hw : |(873218159/2000000000 : ℝ)|=(873218159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(228475267/500000000 : ℝ)|^2077 ≤ (3536658829017/10000000000000 : ℝ)^1565
        have hw : |(228475267/500000000 : ℝ)|=(228475267/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521476303/1250000000 : ℝ)|^2077 ≤ (31340885274057/100000000000000 : ℝ)^1565
        have hw : |(521476303/1250000000 : ℝ)|=(521476303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1115_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3317/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4473/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10553/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14839/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3317/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4473/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3317/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4473/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3317/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4473/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3317/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4473/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3317/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4473/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3317/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4473/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4473/50000 : ℝ) ^ (8307/2048 : ℝ) ≤ (5593029121746121/100000000000000000000 : ℝ) := by
    have hpowers : (4473/50000 : ℝ)^8307 ≤ (5593029121746121/100000000000000000000 : ℝ)^2048 := by
      have hnat : (4473 : ℕ)^8307*100000000000000000000^2048 ≤ 5593029121746121^2048*50000^8307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4473 50000 5593029121746121 100000000000000000000 8307 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4473/50000 : ℝ)) (X := (5593029121746121/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3317/20000 : ℝ) ^ (8307/2048 : ℝ) ≤ (68398582051817169/100000000000000000000 : ℝ) := by
    have hpowers : (3317/20000 : ℝ)^8307 ≤ (68398582051817169/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3317 : ℕ)^8307*100000000000000000000^2048 ≤ 68398582051817169^2048*20000^8307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3317 20000 68398582051817169 100000000000000000000 8307 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3317/20000 : ℝ)) (X := (68398582051817169/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005593029121746121/50000000000000000000 : ℝ) ≤ (156254308881427/156250000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (50005593029121746121/50000000000000000000 : ℝ)^2048 ≤ (156254308881427/156250000000000 : ℝ)^8307 := by
      have hnat : (50005593029121746121 : ℕ)^2048*156250000000000^8307 ≤ 156254308881427^8307*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005593029121746121 50000000000000000000 156254308881427 156250000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156254308881427/156250000000000 : ℝ)) (X := (50005593029121746121/50000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10007399161117356329/10000000000000000000 : ℝ) ≤ (10001823673983039/10000000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (10007399161117356329/10000000000000000000 : ℝ)^2048 ≤ (10001823673983039/10000000000000000 : ℝ)^8307 := by
      have hnat : (10007399161117356329 : ℕ)^2048*10000000000000000^8307 ≤ 10001823673983039^8307*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007399161117356329 10000000000000000000 10001823673983039 10000000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001823673983039/10000000000000000 : ℝ)) (X := (10007399161117356329/10000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50068398582051817169/50000000000000000000 : ℝ) ≤ (40013486318219/40000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (50068398582051817169/50000000000000000000 : ℝ)^2048 ≤ (40013486318219/40000000000000 : ℝ)^8307 := by
      have hnat : (50068398582051817169 : ℕ)^2048*40000000000000^8307 ≤ 40013486318219^8307*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50068398582051817169 50000000000000000000 40013486318219 40000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40013486318219/40000000000000 : ℝ)) (X := (50068398582051817169/50000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5593029121746121/100000000000000000000 : ℝ) ≤ ((3818220573420254069/3819500000000000000 : ℝ)+2*(1547905571711/763900000000000 : ℝ)*(4473/50000 : ℝ))^(8307/2048 : ℝ) := by
    rw [show (3818220573420254069/3819500000000000000 : ℝ)+2*(1547905571711/763900000000000 : ℝ)*(4473/50000 : ℝ)=(156254308881427/156250000000000 : ℝ) by norm_num, show 1+2*(5593029121746121/100000000000000000000 : ℝ)=(50005593029121746121/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(68398582051817169/100000000000000000000 : ℝ)+(5593029121746121/100000000000000000000 : ℝ) ≤ ((3818220573420254069/3819500000000000000 : ℝ)+(1547905571711/763900000000000 : ℝ)*((3317/20000 : ℝ)+(4473/50000 : ℝ)))^(8307/2048 : ℝ) := by
    rw [show (3818220573420254069/3819500000000000000 : ℝ)+(1547905571711/763900000000000 : ℝ)*((3317/20000 : ℝ)+(4473/50000 : ℝ))=(10001823673983039/10000000000000000 : ℝ) by norm_num, show 1+(68398582051817169/100000000000000000000 : ℝ)+(5593029121746121/100000000000000000000 : ℝ)=(10007399161117356329/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(68398582051817169/100000000000000000000 : ℝ) ≤ ((3818220573420254069/3819500000000000000 : ℝ)+2*(1547905571711/763900000000000 : ℝ)*(3317/20000 : ℝ))^(8307/2048 : ℝ) := by
    rw [show (3818220573420254069/3819500000000000000 : ℝ)+2*(1547905571711/763900000000000 : ℝ)*(3317/20000 : ℝ)=(40013486318219/40000000000000 : ℝ) by norm_num, show 1+2*(68398582051817169/100000000000000000000 : ℝ)=(50068398582051817169/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3818220573420254069/3819500000000000000 : ℝ)*(X 1 0+X 2 0)+(1547905571711/763900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (4473/50000 : ℝ)) (hi := (3317/20000 : ℝ)) (c := (3818220573420254069/3819500000000000000 : ℝ)) (alpha := (1547905571711/763900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3818220573420254069/3819500000000000000 : ℝ)*(X 0 1+X 2 1)+(1547905571711/763900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (4473/50000 : ℝ)) (hi := (3317/20000 : ℝ)) (c := (3818220573420254069/3819500000000000000 : ℝ)) (alpha := (1547905571711/763900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3818220573420254069/3819500000000000000 : ℝ)*(X 0 2+X 1 2)+(1547905571711/763900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (4473/50000 : ℝ)) (hi := (3317/20000 : ℝ)) (c := (3818220573420254069/3819500000000000000 : ℝ)) (alpha := (1547905571711/763900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-543937873/2500000000 : ℝ)*X 0 0+(2716018381/5000000000 : ℝ)*X 0 1+(5229466537/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354455183/10000000000 : ℝ)*X 1 0+(-2279361457/10000000000 : ℝ)*X 1 1+(5229466543/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53544553/100000000 : ℝ)*X 2 0+(1045893329/2000000000 : ℝ)*X 2 1+(-142460073/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((545756579/1250000000 : ℝ)*X 0 0+(1042554009/2500000000 : ℝ)*X 0 1+(2285545173/5000000000 : ℝ)*X 0 2+(545756579/1250000000 : ℝ)*X 1 0+(1042554009/2500000000 : ℝ)*X 1 1+(2285545173/5000000000 : ℝ)*X 1 2+(545756579/1250000000 : ℝ)*X 2 0+(1042554009/2500000000 : ℝ)*X 2 1+(2285545173/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2175771383/10000000000 : ℝ)*X 0 0+(5230267863/10000000000 : ℝ)*X 0 1+(678903819/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325809247/2500000000 : ℝ)*X 1 0+(-51939941/250000000 : ℝ)*X 1 1+(5431230753/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651618907/5000000000 : ℝ)*X 2 0+(5431230909/10000000000 : ℝ)*X 2 1+(-2077596303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873218159/2000000000 : ℝ)*X 0 0+(228475267/500000000 : ℝ)*X 0 1+(521476303/1250000000 : ℝ)*X 0 2+(873218159/2000000000 : ℝ)*X 1 0+(228475267/500000000 : ℝ)*X 1 1+(521476303/1250000000 : ℝ)*X 1 2+(873218159/2000000000 : ℝ)*X 2 0+(228475267/500000000 : ℝ)*X 2 1+(521476303/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (229804452414638582791096527/47743750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1441871697/100000000000000 : ℝ)*(base19) + (1360446987/100000000000000 : ℝ)*(base23) + (50678443/50000000000000 : ℝ)*(lower2) + (39560109/100000000000000 : ℝ)*(upper3) + (3328323/1562500000000 : ℝ)*(upper5) + (928898444073163/25000000000000 : ℝ)*(major0) + (928898444073163/25000000000000 : ℝ)*(major1) + (928898444073163/25000000000000 : ℝ)*(major2) + (4936583682130167/100000000000000 : ℝ)*(sp0) + (4936614518143919/100000000000000 : ℝ)*(sp1) + (1234153649892157/25000000000000 : ℝ)*(sp2) + (1247280013264613/50000000000000 : ℝ)*(sp3) + (4034735681/12500000000000 : ℝ)*(sp4) + (2281119499/20000000000000 : ℝ)*(sp7) + (1247285716063361/50000000000000 : ℝ)*(f.failure) + (987323192003123/20000000000000 : ℝ)*(f.sum) + (67883110641817/38195000000000000000000000000 : ℝ)*base65 + (982644724260840247/95487500000000000000000000000000 : ℝ)*base67 + (1940554246636552747/95487500000000000000000000000000 : ℝ)*base69 + (1009074210941090247/95487500000000000000000000000000 : ℝ)*base71 + (9228048170237/38195000000000000000000000000 : ℝ)*base73 + (171087507038577747/95487500000000000000000000000000 : ℝ)*base75 + (695985382222377747/95487500000000000000000000000000 : ℝ)*base77 + (2163686052082115247/95487500000000000000000000000000 : ℝ)*base79 + (16339253914377/2387187500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (6208619/5000000000000000000000 : ℝ)*base89 + (6208619/5000000000000000000000 : ℝ)*base91 + (6208619/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79113815831361049826937/38195000000000000000000000000 : ℝ) := by norm_num
    linear_combination (650486653/100000000000000 : ℝ)*(base19) + (578695303/25000000000000 : ℝ)*(base23) + (27469879/12500000000000 : ℝ)*(upper2) + (30109539/12500000000000 : ℝ)*(upper3) + (35257617/100000000000000 : ℝ)*(upper5) + (1872635374069987/50000000000000 : ℝ)*(major0) + (1872635374069987/50000000000000 : ℝ)*(major1) + (1872635374069987/50000000000000 : ℝ)*(major2) + (3874189189/50000000000000 : ℝ)*(sp1) + (28459073861/50000000000000 : ℝ)*(sp2) + (995209100207883/20000000000000 : ℝ)*(sp4) + (311002318885899/6250000000000 : ℝ)*(sp5) + (4975986268110481/100000000000000 : ℝ)*(sp6) + (502899185239349/20000000000000 : ℝ)*(sp7) + (502899185239349/20000000000000 : ℝ)*(f.failure) + (995209100207883/20000000000000 : ℝ)*(f.sum) + (38482062780959/9548750000000000000000000000 : ℝ)*base66 + (1525805762717562897/190975000000000000000000000000000 : ℝ)*base68 + (1021678796880312103/190975000000000000000000000000000 : ℝ)*base69 + (106989923543662897/190975000000000000000000000000000 : ℝ)*base72 + (59914102904079/9548750000000000000000000000 : ℝ)*base74 + (1155164339397462103/190975000000000000000000000000000 : ℝ)*base75 + (1450041962867462897/190975000000000000000000000000000 : ℝ)*base78 + (2781641134692787103/190975000000000000000000000000000 : ℝ)*base79 + (245635086243519/38195000000000000000000000000 : ℝ)*base81 + (6653529/2000000000000000000000 : ℝ)*base90 + (6653529/2000000000000000000000 : ℝ)*base92 + (6653529/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1115_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3317/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4473/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10553/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14839/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1115_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1115_s4_0 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2178981521/10000000000 : ℝ)*x 0 + (675402581/1250000000 : ℝ)*x 1 + (164255329/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178981521/10000000000 : ℝ)^2077 ≤ (3309016019933/25000000000000 : ℝ)^1565 := by
    have hnat : (2178981521 : ℕ)^2077*25000000000000^1565 ≤ 3309016019933^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178981521 10000000000 3309016019933 25000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675402581/1250000000 : ℝ)^2077 ≤ (22088096347729/50000000000000 : ℝ)^1565 := by
    have hnat : (675402581 : ℕ)^2077*50000000000000^1565 ≤ 22088096347729^1565*1250000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675402581 1250000000 22088096347729 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164255329/312500000 : ℝ)^2077 ≤ (10646935803569/25000000000000 : ℝ)^1565 := by
    have hnat : (164255329 : ℕ)^2077*25000000000000^1565 ≤ 10646935803569^1565*312500000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164255329 312500000 10646935803569 25000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2178981521/10000000000 : ℝ), (675402581/1250000000 : ℝ), (164255329/312500000 : ℝ)] ![(3309016019933/25000000000000 : ℝ), (22088096347729/50000000000000 : ℝ), (10646935803569/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2178981521/10000000000 : ℝ)|^2077 ≤ (3309016019933/25000000000000 : ℝ)^1565
        have hw : |(-2178981521/10000000000 : ℝ)|=(2178981521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675402581/1250000000 : ℝ)|^2077 ≤ (22088096347729/50000000000000 : ℝ)^1565
        have hw : |(675402581/1250000000 : ℝ)|=(675402581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164255329/312500000 : ℝ)|^2077 ≤ (10646935803569/25000000000000 : ℝ)^1565
        have hw : |(164255329/312500000 : ℝ)|=(164255329/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s4_1 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (167102469/312500000 : ℝ)*x 0 + (-2253732191/10000000000 : ℝ)*x 1 + (5256170609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167102469/312500000 : ℝ)^2077 ≤ (21785108593883/50000000000000 : ℝ)^1565 := by
    have hnat : (167102469 : ℕ)^2077*50000000000000^1565 ≤ 21785108593883^1565*312500000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167102469 312500000 21785108593883 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253732191/10000000000 : ℝ)^2077 ≤ (2768407744413/20000000000000 : ℝ)^1565 := by
    have hnat : (2253732191 : ℕ)^2077*20000000000000^1565 ≤ 2768407744413^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253732191 10000000000 2768407744413 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256170609/10000000000 : ℝ)^2077 ≤ (8517548817057/20000000000000 : ℝ)^1565 := by
    have hnat : (5256170609 : ℕ)^2077*20000000000000^1565 ≤ 8517548817057^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256170609 10000000000 8517548817057 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167102469/312500000 : ℝ), (-2253732191/10000000000 : ℝ), (5256170609/10000000000 : ℝ)] ![(21785108593883/50000000000000 : ℝ), (2768407744413/20000000000000 : ℝ), (8517548817057/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167102469/312500000 : ℝ)|^2077 ≤ (21785108593883/50000000000000 : ℝ)^1565
        have hw : |(167102469/312500000 : ℝ)|=(167102469/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2253732191/10000000000 : ℝ)|^2077 ≤ (2768407744413/20000000000000 : ℝ)^1565
        have hw : |(-2253732191/10000000000 : ℝ)|=(2253732191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256170609/10000000000 : ℝ)|^2077 ≤ (8517548817057/20000000000000 : ℝ)^1565
        have hw : |(5256170609/10000000000 : ℝ)|=(5256170609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s4_2 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336819723/2500000000 : ℝ)*x 0 + (5132979/9765625 : ℝ)*x 1 + (-2253732493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336819723/2500000000 : ℝ)^2077 ≤ (43570215933363/100000000000000 : ℝ)^1565 := by
    have hnat : (1336819723 : ℕ)^2077*100000000000000^1565 ≤ 43570215933363^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336819723 2500000000 43570215933363 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5132979/9765625 : ℝ)^2077 ≤ (21293871435087/50000000000000 : ℝ)^1565 := by
    have hnat : (5132979 : ℕ)^2077*50000000000000^1565 ≤ 21293871435087^1565*9765625^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132979 9765625 21293871435087 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253732493/10000000000 : ℝ)^2077 ≤ (6921020591859/50000000000000 : ℝ)^1565 := by
    have hnat : (2253732493 : ℕ)^2077*50000000000000^1565 ≤ 6921020591859^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253732493 10000000000 6921020591859 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336819723/2500000000 : ℝ), (5132979/9765625 : ℝ), (-2253732493/10000000000 : ℝ)] ![(43570215933363/100000000000000 : ℝ), (21293871435087/50000000000000 : ℝ), (6921020591859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336819723/2500000000 : ℝ)|^2077 ≤ (43570215933363/100000000000000 : ℝ)^1565
        have hw : |(1336819723/2500000000 : ℝ)|=(1336819723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5132979/9765625 : ℝ)|^2077 ≤ (21293871435087/50000000000000 : ℝ)^1565
        have hw : |(5132979/9765625 : ℝ)|=(5132979/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2253732493/10000000000 : ℝ)|^2077 ≤ (6921020591859/50000000000000 : ℝ)^1565
        have hw : |(-2253732493/10000000000 : ℝ)|=(2253732493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s4_3 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2183988407/5000000000 : ℝ)*x 0 + (844980133/2000000000 : ℝ)*x 1 + (2257952471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183988407/5000000000 : ℝ)^2077 ≤ (16655807041133/50000000000000 : ℝ)^1565 := by
    have hnat : (2183988407 : ℕ)^2077*50000000000000^1565 ≤ 16655807041133^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183988407 5000000000 16655807041133 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844980133/2000000000 : ℝ)^2077 ≤ (31871310427799/100000000000000 : ℝ)^1565 := by
    have hnat : (844980133 : ℕ)^2077*100000000000000^1565 ≤ 31871310427799^1565*2000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844980133 2000000000 31871310427799 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257952471/5000000000 : ℝ)^2077 ≤ (8704268868871/25000000000000 : ℝ)^1565 := by
    have hnat : (2257952471 : ℕ)^2077*25000000000000^1565 ≤ 8704268868871^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257952471 5000000000 8704268868871 25000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183988407/5000000000 : ℝ), (844980133/2000000000 : ℝ), (2257952471/5000000000 : ℝ)] ![(16655807041133/50000000000000 : ℝ), (31871310427799/100000000000000 : ℝ), (8704268868871/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183988407/5000000000 : ℝ)|^2077 ≤ (16655807041133/50000000000000 : ℝ)^1565
        have hw : |(2183988407/5000000000 : ℝ)|=(2183988407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(844980133/2000000000 : ℝ)|^2077 ≤ (31871310427799/100000000000000 : ℝ)^1565
        have hw : |(844980133/2000000000 : ℝ)|=(844980133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2257952471/5000000000 : ℝ)|^2077 ≤ (8704268868871/25000000000000 : ℝ)^1565
        have hw : |(2257952471/5000000000 : ℝ)|=(2257952471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s4_4 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-544747247/2500000000 : ℝ)*x 0 + (5256593467/10000000000 : ℝ)*x 1 + (5402795951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544747247/2500000000 : ℝ)^2077 ≤ (2647224855319/20000000000000 : ℝ)^1565 := by
    have hnat : (544747247 : ℕ)^2077*20000000000000^1565 ≤ 2647224855319^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544747247 2500000000 2647224855319 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5256593467/10000000000 : ℝ)^2077 ≤ (42592291217721/100000000000000 : ℝ)^1565 := by
    have hnat : (5256593467 : ℕ)^2077*100000000000000^1565 ≤ 42592291217721^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256593467 10000000000 42592291217721 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402795951/10000000000 : ℝ)^2077 ≤ (5521448061899/12500000000000 : ℝ)^1565 := by
    have hnat : (5402795951 : ℕ)^2077*12500000000000^1565 ≤ 5521448061899^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402795951 10000000000 5521448061899 12500000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-544747247/2500000000 : ℝ), (5256593467/10000000000 : ℝ), (5402795951/10000000000 : ℝ)] ![(2647224855319/20000000000000 : ℝ), (42592291217721/100000000000000 : ℝ), (5521448061899/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-544747247/2500000000 : ℝ)|^2077 ≤ (2647224855319/20000000000000 : ℝ)^1565
        have hw : |(-544747247/2500000000 : ℝ)|=(544747247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5256593467/10000000000 : ℝ)|^2077 ≤ (42592291217721/100000000000000 : ℝ)^1565
        have hw : |(5256593467/10000000000 : ℝ)|=(5256593467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402795951/10000000000 : ℝ)|^2077 ≤ (5521448061899/12500000000000 : ℝ)^1565
        have hw : |(5402795951/10000000000 : ℝ)|=(5402795951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s4_5 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5310100139/10000000000 : ℝ)*x 0 + (-2107107253/10000000000 : ℝ)*x 1 + (1080559223/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310100139/10000000000 : ℝ)^2077 ≤ (43168629661129/100000000000000 : ℝ)^1565 := by
    have hnat : (5310100139 : ℕ)^2077*100000000000000^1565 ≤ 43168629661129^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310100139 10000000000 43168629661129 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107107253/10000000000 : ℝ)^2077 ≤ (12659784045713/100000000000000 : ℝ)^1565 := by
    have hnat : (2107107253 : ℕ)^2077*100000000000000^1565 ≤ 12659784045713^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107107253 10000000000 12659784045713 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080559223/2000000000 : ℝ)^2077 ≤ (44171586274661/100000000000000 : ℝ)^1565 := by
    have hnat : (1080559223 : ℕ)^2077*100000000000000^1565 ≤ 44171586274661^1565*2000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080559223 2000000000 44171586274661 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310100139/10000000000 : ℝ), (-2107107253/10000000000 : ℝ), (1080559223/2000000000 : ℝ)] ![(43168629661129/100000000000000 : ℝ), (12659784045713/100000000000000 : ℝ), (44171586274661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310100139/10000000000 : ℝ)|^2077 ≤ (43168629661129/100000000000000 : ℝ)^1565
        have hw : |(5310100139/10000000000 : ℝ)|=(5310100139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2107107253/10000000000 : ℝ)|^2077 ≤ (12659784045713/100000000000000 : ℝ)^1565
        have hw : |(-2107107253/10000000000 : ℝ)|=(2107107253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080559223/2000000000 : ℝ)|^2077 ≤ (44171586274661/100000000000000 : ℝ)^1565
        have hw : |(1080559223/2000000000 : ℝ)|=(1080559223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s4_6 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (663762543/1250000000 : ℝ)*x 0 + (108055923/200000000 : ℝ)*x 1 + (-2107106929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663762543/1250000000 : ℝ)^2077 ≤ (43168631872907/100000000000000 : ℝ)^1565 := by
    have hnat : (663762543 : ℕ)^2077*100000000000000^1565 ≤ 43168631872907^1565*1250000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663762543 1250000000 43168631872907 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108055923/200000000 : ℝ)^2077 ≤ (22085793327213/50000000000000 : ℝ)^1565 := by
    have hnat : (108055923 : ℕ)^2077*50000000000000^1565 ≤ 22085793327213^1565*200000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108055923 200000000 22085793327213 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107106929/10000000000 : ℝ)^2077 ≤ (12659781462223/100000000000000 : ℝ)^1565 := by
    have hnat : (2107106929 : ℕ)^2077*100000000000000^1565 ≤ 12659781462223^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107106929 10000000000 12659781462223 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663762543/1250000000 : ℝ), (108055923/200000000 : ℝ), (-2107106929/10000000000 : ℝ)] ![(43168631872907/100000000000000 : ℝ), (22085793327213/50000000000000 : ℝ), (12659781462223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663762543/1250000000 : ℝ)|^2077 ≤ (43168631872907/100000000000000 : ℝ)^1565
        have hw : |(663762543/1250000000 : ℝ)|=(663762543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108055923/200000000 : ℝ)|^2077 ≤ (22085793327213/50000000000000 : ℝ)^1565
        have hw : |(108055923/200000000 : ℝ)|=(108055923/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2107106929/10000000000 : ℝ)|^2077 ≤ (12659781462223/100000000000000 : ℝ)^1565
        have hw : |(-2107106929/10000000000 : ℝ)|=(2107106929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s4_7 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4367992313/10000000000 : ℝ)*x 0 + (4515067507/10000000000 : ℝ)*x 1 + (1056435207/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367992313/10000000000 : ℝ)^2077 ≤ (33311770952823/100000000000000 : ℝ)^1565 := by
    have hnat : (4367992313 : ℕ)^2077*100000000000000^1565 ≤ 33311770952823^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367992313 10000000000 33311770952823 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4515067507/10000000000 : ℝ)^2077 ≤ (34808506920553/100000000000000 : ℝ)^1565 := by
    have hnat : (4515067507 : ℕ)^2077*100000000000000^1565 ≤ 34808506920553^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515067507 10000000000 34808506920553 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056435207/2500000000 : ℝ)^2077 ≤ (31879722117639/100000000000000 : ℝ)^1565 := by
    have hnat : (1056435207 : ℕ)^2077*100000000000000^1565 ≤ 31879722117639^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056435207 2500000000 31879722117639 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367992313/10000000000 : ℝ), (4515067507/10000000000 : ℝ), (1056435207/2500000000 : ℝ)] ![(33311770952823/100000000000000 : ℝ), (34808506920553/100000000000000 : ℝ), (31879722117639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367992313/10000000000 : ℝ)|^2077 ≤ (33311770952823/100000000000000 : ℝ)^1565
        have hw : |(4367992313/10000000000 : ℝ)|=(4367992313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4515067507/10000000000 : ℝ)|^2077 ≤ (34808506920553/100000000000000 : ℝ)^1565
        have hw : |(4515067507/10000000000 : ℝ)|=(4515067507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056435207/2500000000 : ℝ)|^2077 ≤ (31879722117639/100000000000000 : ℝ)^1565
        have hw : |(1056435207/2500000000 : ℝ)|=(1056435207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1115_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14839/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10553/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11123/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14839/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10553/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14839/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10553/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14839/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10553/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14839/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10553/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14839/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10553/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14839/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10553/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10553/100000 : ℝ) ^ (8307/2048 : ℝ) ≤ (5465551952978101/50000000000000000000 : ℝ) := by
    have hpowers : (10553/100000 : ℝ)^8307 ≤ (5465551952978101/50000000000000000000 : ℝ)^2048 := by
      have hnat : (10553 : ℕ)^8307*50000000000000000000^2048 ≤ 5465551952978101^2048*100000^8307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10553 100000 5465551952978101 50000000000000000000 8307 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10553/100000 : ℝ)) (X := (5465551952978101/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14839/100000 : ℝ) ^ (8307/2048 : ℝ) ≤ (43560310578134737/100000000000000000000 : ℝ) := by
    have hpowers : (14839/100000 : ℝ)^8307 ≤ (43560310578134737/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14839 : ℕ)^8307*100000000000000000000^2048 ≤ 43560310578134737^2048*100000^8307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14839 100000 43560310578134737 100000000000000000000 8307 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14839/100000 : ℝ)) (X := (43560310578134737/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005465551952978101/25000000000000000000 : ℝ) ≤ (250013473610939/250000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (25005465551952978101/25000000000000000000 : ℝ)^2048 ≤ (250013473610939/250000000000000 : ℝ)^8307 := by
      have hnat : (25005465551952978101 : ℕ)^2048*250000000000000^8307 ≤ 250013473610939^8307*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005465551952978101 25000000000000000000 250013473610939 250000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250013473610939/250000000000000 : ℝ)) (X := (25005465551952978101/25000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100054491414484090939/100000000000000000000 : ℝ) ≤ (5000671575265387/5000000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (100054491414484090939/100000000000000000000 : ℝ)^2048 ≤ (5000671575265387/5000000000000000 : ℝ)^8307 := by
      have hnat : (100054491414484090939 : ℕ)^2048*5000000000000000^8307 ≤ 5000671575265387^8307*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100054491414484090939 100000000000000000000 5000671575265387 5000000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000671575265387/5000000000000000 : ℝ)) (X := (100054491414484090939/100000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50043560310578134737/50000000000000000000 : ℝ) ≤ (2500536839155997/2500000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (50043560310578134737/50000000000000000000 : ℝ)^2048 ≤ (2500536839155997/2500000000000000 : ℝ)^8307 := by
      have hnat : (50043560310578134737 : ℕ)^2048*2500000000000000^8307 ≤ 2500536839155997^8307*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50043560310578134737 50000000000000000000 2500536839155997 2500000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500536839155997/2500000000000000 : ℝ)) (X := (50043560310578134737/50000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5465551952978101/50000000000000000000 : ℝ) ≤ ((10711334085514001869/10715000000000000000 : ℝ)+2*(402103046607/214300000000000 : ℝ)*(10553/100000 : ℝ))^(8307/2048 : ℝ) := by
    rw [show (10711334085514001869/10715000000000000000 : ℝ)+2*(402103046607/214300000000000 : ℝ)*(10553/100000 : ℝ)=(250013473610939/250000000000000 : ℝ) by norm_num, show 1+2*(5465551952978101/50000000000000000000 : ℝ)=(25005465551952978101/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(43560310578134737/100000000000000000000 : ℝ)+(5465551952978101/50000000000000000000 : ℝ) ≤ ((10711334085514001869/10715000000000000000 : ℝ)+(402103046607/214300000000000 : ℝ)*((14839/100000 : ℝ)+(10553/100000 : ℝ)))^(8307/2048 : ℝ) := by
    rw [show (10711334085514001869/10715000000000000000 : ℝ)+(402103046607/214300000000000 : ℝ)*((14839/100000 : ℝ)+(10553/100000 : ℝ))=(5000671575265387/5000000000000000 : ℝ) by norm_num, show 1+(43560310578134737/100000000000000000000 : ℝ)+(5465551952978101/50000000000000000000 : ℝ)=(100054491414484090939/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(43560310578134737/100000000000000000000 : ℝ) ≤ ((10711334085514001869/10715000000000000000 : ℝ)+2*(402103046607/214300000000000 : ℝ)*(14839/100000 : ℝ))^(8307/2048 : ℝ) := by
    rw [show (10711334085514001869/10715000000000000000 : ℝ)+2*(402103046607/214300000000000 : ℝ)*(14839/100000 : ℝ)=(2500536839155997/2500000000000000 : ℝ) by norm_num, show 1+2*(43560310578134737/100000000000000000000 : ℝ)=(50043560310578134737/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10711334085514001869/10715000000000000000 : ℝ)*(X 1 0+X 2 0)+(402103046607/214300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (10553/100000 : ℝ)) (hi := (14839/100000 : ℝ)) (c := (10711334085514001869/10715000000000000000 : ℝ)) (alpha := (402103046607/214300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10711334085514001869/10715000000000000000 : ℝ)*(X 0 1+X 2 1)+(402103046607/214300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (10553/100000 : ℝ)) (hi := (14839/100000 : ℝ)) (c := (10711334085514001869/10715000000000000000 : ℝ)) (alpha := (402103046607/214300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10711334085514001869/10715000000000000000 : ℝ)*(X 0 2+X 1 2)+(402103046607/214300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (10553/100000 : ℝ)) (hi := (14839/100000 : ℝ)) (c := (10711334085514001869/10715000000000000000 : ℝ)) (alpha := (402103046607/214300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2178981521/10000000000 : ℝ)*X 0 0+(675402581/1250000000 : ℝ)*X 0 1+(164255329/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167102469/312500000 : ℝ)*X 1 0+(-2253732191/10000000000 : ℝ)*X 1 1+(5256170609/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336819723/2500000000 : ℝ)*X 2 0+(5132979/9765625 : ℝ)*X 2 1+(-2253732493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183988407/5000000000 : ℝ)*X 0 0+(844980133/2000000000 : ℝ)*X 0 1+(2257952471/5000000000 : ℝ)*X 0 2+(2183988407/5000000000 : ℝ)*X 1 0+(844980133/2000000000 : ℝ)*X 1 1+(2257952471/5000000000 : ℝ)*X 1 2+(2183988407/5000000000 : ℝ)*X 2 0+(844980133/2000000000 : ℝ)*X 2 1+(2257952471/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-544747247/2500000000 : ℝ)*X 0 0+(5256593467/10000000000 : ℝ)*X 0 1+(5402795951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310100139/10000000000 : ℝ)*X 1 0+(-2107107253/10000000000 : ℝ)*X 1 1+(1080559223/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663762543/1250000000 : ℝ)*X 2 0+(108055923/200000000 : ℝ)*X 2 1+(-2107106929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367992313/10000000000 : ℝ)*X 0 0+(4515067507/10000000000 : ℝ)*X 0 1+(1056435207/2500000000 : ℝ)*X 0 2+(4367992313/10000000000 : ℝ)*X 1 0+(4515067507/10000000000 : ℝ)*X 1 1+(1056435207/2500000000 : ℝ)*X 1 2+(4367992313/10000000000 : ℝ)*X 2 0+(4515067507/10000000000 : ℝ)*X 2 1+(1056435207/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2888203318959657206342483949/535750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1419526133/100000000000000 : ℝ)*(base19) + (336987513/25000000000000 : ℝ)*(base23) + (49619097/100000000000000 : ℝ)*(upper2) + (157714093/50000000000000 : ℝ)*(upper3) + (5118446033212107/100000000000000 : ℝ)*(major0) + (5118446033212107/100000000000000 : ℝ)*(major1) + (5118446033212107/100000000000000 : ℝ)*(major2) + (170011170366407/2500000000000 : ℝ)*(sp0) + (6800473565868379/100000000000000 : ℝ)*(sp1) + (6800471214721647/100000000000000 : ℝ)*(sp2) + (3436393965623713/100000000000000 : ℝ)*(sp3) + (28170738231/100000000000000 : ℝ)*(sp4) + (605680703/25000000000000 : ℝ)*(sp6) + (4587141507/20000000000000 : ℝ)*(sp7) + (214776056333203/6250000000000 : ℝ)*(f.failure) + (6800474985394511/100000000000000 : ℝ)*(f.sum) + (11531232415143/5357500000000000000000000000 : ℝ)*base66 + (1775178170068377983/1071500000000000000000000000000000 : ℝ)*base67 + (3406281280391622017/1071500000000000000000000000000000 : ℝ)*base70 + (7656717897514622017/1071500000000000000000000000000000 : ℝ)*base72 + (6452934635117/5357500000000000000000000000 : ℝ)*base73 + (4208250052126622017/1071500000000000000000000000000000 : ℝ)*base76 + (11888798171455377983/1071500000000000000000000000000000 : ℝ)*base77 + (15630368974174122017/1071500000000000000000000000000000 : ℝ)*base80 + (8705066384639/2678750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2134337/625000000000000000000 : ℝ)*base89 + (2134337/625000000000000000000 : ℝ)*base91 + (2134337/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (425064267752120204492561967/53575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (220563447/20000000000000 : ℝ)*(base19) + (990258843/50000000000000 : ℝ)*(base23) + (369129523/100000000000000 : ℝ)*(upper3) + (5448689/2500000000000 : ℝ)*(lower4) + (161006383/50000000000000 : ℝ)*(upper5) + (1029612764270481/20000000000000 : ℝ)*(major0) + (1029612764270481/20000000000000 : ℝ)*(major1) + (1029612764270481/20000000000000 : ℝ)*(major2) + (17052366387/100000000000000 : ℝ)*(sp1) + (2303782181/5000000000000 : ℝ)*(sp2) + (6839825717531551/100000000000000 : ℝ)*(sp4) + (6839807562347929/100000000000000 : ℝ)*(sp5) + (1367955532274049/20000000000000 : ℝ)*(sp6) + (3456301660706447/100000000000000 : ℝ)*(sp7) + (3456301660706447/100000000000000 : ℝ)*(f.failure) + (6839825717531551/100000000000000 : ℝ)*(f.sum) + (3666077452089/1071500000000000000000000000 : ℝ)*base65 + (1160202002873921011/214300000000000000000000000000000 : ℝ)*base68 + (1113157403419221011/214300000000000000000000000000000 : ℝ)*base70 + (2089376080080478989/214300000000000000000000000000000 : ℝ)*base71 + (2565172114721/1071500000000000000000000000 : ℝ)*base73 + (4299983883712321011/214300000000000000000000000000000 : ℝ)*base76 + (299461827949421011/214300000000000000000000000000000 : ℝ)*base78 + (2170029667301821011/214300000000000000000000000000000 : ℝ)*base80 + (4972595624637/1071500000000000000000000000 : ℝ)*base81 + (72236987/10000000000000000000000 : ℝ)*base90 + (72236987/10000000000000000000000 : ℝ)*base92 + (72236987/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1115_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14839/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10553/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11123/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1115_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1115_s5_0 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-136230003/625000000 : ℝ)*x 0 + (539563291/1000000000 : ℝ)*x 1 + (2631650007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136230003/625000000 : ℝ)^2077 ≤ (2648339140193/20000000000000 : ℝ)^1565 := by
    have hnat : (136230003 : ℕ)^2077*20000000000000^1565 ≤ 2648339140193^1565*625000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136230003 625000000 2648339140193 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539563291/1000000000 : ℝ)^2077 ≤ (22046939674717/50000000000000 : ℝ)^1565 := by
    have hnat : (539563291 : ℕ)^2077*50000000000000^1565 ≤ 22046939674717^1565*1000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539563291 1000000000 22046939674717 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631650007/5000000000 : ℝ)^2077 ≤ (21332212469783/50000000000000 : ℝ)^1565 := by
    have hnat : (2631650007 : ℕ)^2077*50000000000000^1565 ≤ 21332212469783^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631650007 5000000000 21332212469783 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-136230003/625000000 : ℝ), (539563291/1000000000 : ℝ), (2631650007/5000000000 : ℝ)] ![(2648339140193/20000000000000 : ℝ), (22046939674717/50000000000000 : ℝ), (21332212469783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-136230003/625000000 : ℝ)|^2077 ≤ (2648339140193/20000000000000 : ℝ)^1565
        have hw : |(-136230003/625000000 : ℝ)|=(136230003/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539563291/1000000000 : ℝ)|^2077 ≤ (22046939674717/50000000000000 : ℝ)^1565
        have hw : |(539563291/1000000000 : ℝ)|=(539563291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631650007/5000000000 : ℝ)|^2077 ≤ (21332212469783/50000000000000 : ℝ)^1565
        have hw : |(2631650007/5000000000 : ℝ)|=(2631650007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s5_1 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345380839/10000000000 : ℝ)*x 0 + (-2246839501/10000000000 : ℝ)*x 1 + (5263299991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345380839/10000000000 : ℝ)^2077 ≤ (43549691926689/100000000000000 : ℝ)^1565 := by
    have hnat : (5345380839 : ℕ)^2077*100000000000000^1565 ≤ 43549691926689^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345380839 10000000000 43549691926689 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246839501/10000000000 : ℝ)^2077 ≤ (6892941683279/50000000000000 : ℝ)^1565 := by
    have hnat : (2246839501 : ℕ)^2077*50000000000000^1565 ≤ 6892941683279^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246839501 10000000000 6892941683279 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263299991/10000000000 : ℝ)^2077 ≤ (42664424692133/100000000000000 : ℝ)^1565 := by
    have hnat : (5263299991 : ℕ)^2077*100000000000000^1565 ≤ 42664424692133^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263299991 10000000000 42664424692133 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345380839/10000000000 : ℝ), (-2246839501/10000000000 : ℝ), (5263299991/10000000000 : ℝ)] ![(43549691926689/100000000000000 : ℝ), (6892941683279/50000000000000 : ℝ), (42664424692133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345380839/10000000000 : ℝ)|^2077 ≤ (43549691926689/100000000000000 : ℝ)^1565
        have hw : |(5345380839/10000000000 : ℝ)|=(5345380839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2246839501/10000000000 : ℝ)|^2077 ≤ (6892941683279/50000000000000 : ℝ)^1565
        have hw : |(-2246839501/10000000000 : ℝ)|=(2246839501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263299991/10000000000 : ℝ)|^2077 ≤ (42664424692133/100000000000000 : ℝ)^1565
        have hw : |(5263299991/10000000000 : ℝ)|=(5263299991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s5_2 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069076169/2000000000 : ℝ)*x 0 + (1315824999/2500000000 : ℝ)*x 1 + (-1123419743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069076169/2000000000 : ℝ)^2077 ≤ (8709938398313/20000000000000 : ℝ)^1565 := by
    have hnat : (1069076169 : ℕ)^2077*20000000000000^1565 ≤ 8709938398313^1565*2000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069076169 2000000000 8709938398313 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315824999/2500000000 : ℝ)^2077 ≤ (42664424745923/100000000000000 : ℝ)^1565 := by
    have hnat : (1315824999 : ℕ)^2077*100000000000000^1565 ≤ 42664424745923^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315824999 2500000000 42664424745923 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123419743/5000000000 : ℝ)^2077 ≤ (13785883244413/100000000000000 : ℝ)^1565 := by
    have hnat : (1123419743 : ℕ)^2077*100000000000000^1565 ≤ 13785883244413^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123419743 5000000000 13785883244413 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069076169/2000000000 : ℝ), (1315824999/2500000000 : ℝ), (-1123419743/5000000000 : ℝ)] ![(8709938398313/20000000000000 : ℝ), (42664424745923/100000000000000 : ℝ), (13785883244413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069076169/2000000000 : ℝ)|^2077 ≤ (8709938398313/20000000000000 : ℝ)^1565
        have hw : |(1069076169/2000000000 : ℝ)|=(1069076169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315824999/2500000000 : ℝ)|^2077 ≤ (42664424745923/100000000000000 : ℝ)^1565
        have hw : |(1315824999/2500000000 : ℝ)|=(1315824999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1123419743/5000000000 : ℝ)|^2077 ≤ (13785883244413/100000000000000 : ℝ)^1565
        have hw : |(-1123419743/5000000000 : ℝ)|=(1123419743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s5_3 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4368384569/10000000000 : ℝ)*x 0 + (4239409973/10000000000 : ℝ)*x 1 + (35166323/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368384569/10000000000 : ℝ)^2077 ≤ (1041116911483/3125000000000 : ℝ)^1565 := by
    have hnat : (4368384569 : ℕ)^2077*3125000000000^1565 ≤ 1041116911483^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368384569 10000000000 1041116911483 3125000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4239409973/10000000000 : ℝ)^2077 ≤ (32016654053111/100000000000000 : ℝ)^1565 := by
    have hnat : (4239409973 : ℕ)^2077*100000000000000^1565 ≤ 32016654053111^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239409973 10000000000 32016654053111 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35166323/78125000 : ℝ)^2077 ≤ (34667604767867/100000000000000 : ℝ)^1565 := by
    have hnat : (35166323 : ℕ)^2077*100000000000000^1565 ≤ 34667604767867^1565*78125000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35166323 78125000 34667604767867 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368384569/10000000000 : ℝ), (4239409973/10000000000 : ℝ), (35166323/78125000 : ℝ)] ![(1041116911483/3125000000000 : ℝ), (32016654053111/100000000000000 : ℝ), (34667604767867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368384569/10000000000 : ℝ)|^2077 ≤ (1041116911483/3125000000000 : ℝ)^1565
        have hw : |(4368384569/10000000000 : ℝ)|=(4368384569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4239409973/10000000000 : ℝ)|^2077 ≤ (32016654053111/100000000000000 : ℝ)^1565
        have hw : |(4239409973/10000000000 : ℝ)|=(4239409973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35166323/78125000 : ℝ)|^2077 ≤ (34667604767867/100000000000000 : ℝ)^1565
        have hw : |(35166323/78125000 : ℝ)|=(35166323/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s5_4 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-272460623/1250000000 : ℝ)*x 0 + (5263643041/10000000000 : ℝ)*x 1 + (5395288981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272460623/1250000000 : ℝ)^2077 ≤ (13241735497781/100000000000000 : ℝ)^1565 := by
    have hnat : (272460623 : ℕ)^2077*100000000000000^1565 ≤ 13241735497781^1565*1250000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272460623 1250000000 13241735497781 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263643041/10000000000 : ℝ)^2077 ≤ (853362304993/2000000000000 : ℝ)^1565 := by
    have hnat : (5263643041 : ℕ)^2077*2000000000000^1565 ≤ 853362304993^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263643041 10000000000 853362304993 2000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395288981/10000000000 : ℝ)^2077 ≤ (8818029846687/20000000000000 : ℝ)^1565 := by
    have hnat : (5395288981 : ℕ)^2077*20000000000000^1565 ≤ 8818029846687^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395288981 10000000000 8818029846687 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-272460623/1250000000 : ℝ), (5263643041/10000000000 : ℝ), (5395288981/10000000000 : ℝ)] ![(13241735497781/100000000000000 : ℝ), (853362304993/2000000000000 : ℝ), (8818029846687/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-272460623/1250000000 : ℝ)|^2077 ≤ (13241735497781/100000000000000 : ℝ)^1565
        have hw : |(-272460623/1250000000 : ℝ)|=(272460623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263643041/10000000000 : ℝ)|^2077 ≤ (853362304993/2000000000000 : ℝ)^1565
        have hw : |(5263643041/10000000000 : ℝ)|=(5263643041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395288981/10000000000 : ℝ)|^2077 ≤ (8818029846687/20000000000000 : ℝ)^1565
        have hw : |(5395288981/10000000000 : ℝ)|=(5395288981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s5_5 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (331995123/625000000 : ℝ)*x 0 + (-2114851251/10000000000 : ℝ)*x 1 + (5395288451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331995123/625000000 : ℝ)^2077 ≤ (4318828677203/10000000000000 : ℝ)^1565 := by
    have hnat : (331995123 : ℕ)^2077*10000000000000^1565 ≤ 4318828677203^1565*625000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331995123 625000000 4318828677203 10000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114851251/10000000000 : ℝ)^2077 ≤ (6360784863367/50000000000000 : ℝ)^1565 := by
    have hnat : (2114851251 : ℕ)^2077*50000000000000^1565 ≤ 6360784863367^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114851251 10000000000 6360784863367 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395288451/10000000000 : ℝ)^2077 ≤ (44090143485327/100000000000000 : ℝ)^1565 := by
    have hnat : (5395288451 : ℕ)^2077*100000000000000^1565 ≤ 44090143485327^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395288451 10000000000 44090143485327 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331995123/625000000 : ℝ), (-2114851251/10000000000 : ℝ), (5395288451/10000000000 : ℝ)] ![(4318828677203/10000000000000 : ℝ), (6360784863367/50000000000000 : ℝ), (44090143485327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331995123/625000000 : ℝ)|^2077 ≤ (4318828677203/10000000000000 : ℝ)^1565
        have hw : |(331995123/625000000 : ℝ)|=(331995123/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2114851251/10000000000 : ℝ)|^2077 ≤ (6360784863367/50000000000000 : ℝ)^1565
        have hw : |(-2114851251/10000000000 : ℝ)|=(2114851251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395288451/10000000000 : ℝ)|^2077 ≤ (44090143485327/100000000000000 : ℝ)^1565
        have hw : |(5395288451/10000000000 : ℝ)|=(5395288451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s5_6 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5311922579/10000000000 : ℝ)*x 0 + (2697644369/5000000000 : ℝ)*x 1 + (-422970007/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311922579/10000000000 : ℝ)^2077 ≤ (10797073341237/25000000000000 : ℝ)^1565 := by
    have hnat : (5311922579 : ℕ)^2077*25000000000000^1565 ≤ 10797073341237^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311922579 10000000000 10797073341237 25000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697644369/5000000000 : ℝ)^2077 ≤ (22045073298991/50000000000000 : ℝ)^1565 := by
    have hnat : (2697644369 : ℕ)^2077*50000000000000^1565 ≤ 22045073298991^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697644369 5000000000 22045073298991 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422970007/2000000000 : ℝ)^2077 ≤ (12721560019029/100000000000000 : ℝ)^1565 := by
    have hnat : (422970007 : ℕ)^2077*100000000000000^1565 ≤ 12721560019029^1565*2000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422970007 2000000000 12721560019029 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311922579/10000000000 : ℝ), (2697644369/5000000000 : ℝ), (-422970007/2000000000 : ℝ)] ![(10797073341237/25000000000000 : ℝ), (22045073298991/50000000000000 : ℝ), (12721560019029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311922579/10000000000 : ℝ)|^2077 ≤ (10797073341237/25000000000000 : ℝ)^1565
        have hw : |(5311922579/10000000000 : ℝ)|=(5311922579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697644369/5000000000 : ℝ)|^2077 ≤ (22045073298991/50000000000000 : ℝ)^1565
        have hw : |(2697644369/5000000000 : ℝ)|=(2697644369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-422970007/2000000000 : ℝ)|^2077 ≤ (12721560019029/100000000000000 : ℝ)^1565
        have hw : |(-422970007/2000000000 : ℝ)|=(422970007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s5_7 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (174735863/400000000 : ℝ)*x 0 + (1125152693/2500000000 : ℝ)*x 1 + (132502807/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174735863/400000000 : ℝ)^2077 ≤ (2082241417993/6250000000000 : ℝ)^1565 := by
    have hnat : (174735863 : ℕ)^2077*6250000000000^1565 ≤ 2082241417993^1565*400000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174735863 400000000 2082241417993 6250000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125152693/2500000000 : ℝ)^2077 ≤ (173303345021/500000000000 : ℝ)^1565 := by
    have hnat : (1125152693 : ℕ)^2077*500000000000^1565 ≤ 173303345021^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125152693 2500000000 173303345021 500000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132502807/312500000 : ℝ)^2077 ≤ (32023468299199/100000000000000 : ℝ)^1565 := by
    have hnat : (132502807 : ℕ)^2077*100000000000000^1565 ≤ 32023468299199^1565*312500000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132502807 312500000 32023468299199 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174735863/400000000 : ℝ), (1125152693/2500000000 : ℝ), (132502807/312500000 : ℝ)] ![(2082241417993/6250000000000 : ℝ), (173303345021/500000000000 : ℝ), (32023468299199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174735863/400000000 : ℝ)|^2077 ≤ (2082241417993/6250000000000 : ℝ)^1565
        have hw : |(174735863/400000000 : ℝ)|=(174735863/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125152693/2500000000 : ℝ)|^2077 ≤ (173303345021/500000000000 : ℝ)^1565
        have hw : |(1125152693/2500000000 : ℝ)|=(1125152693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(132502807/312500000 : ℝ)|^2077 ≤ (32023468299199/100000000000000 : ℝ)^1565
        have hw : |(132502807/312500000 : ℝ)|=(132502807/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1115_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11123/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (451/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7039/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11123/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11123/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11123/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11123/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11123/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11123/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11123/100000 : ℝ) ^ (8307/2048 : ℝ) ≤ (13531030570618877/100000000000000000000 : ℝ) := by
    have hpowers : (11123/100000 : ℝ)^8307 ≤ (13531030570618877/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11123 : ℕ)^8307*100000000000000000000^2048 ≤ 13531030570618877^2048*100000^8307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11123 100000 13531030570618877 100000000000000000000 8307 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11123/100000 : ℝ)) (X := (13531030570618877/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (8307/2048 : ℝ) ≤ (36824461434278399/100000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^8307 ≤ (36824461434278399/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14237 : ℕ)^8307*100000000000000000000^2048 ≤ 36824461434278399^2048*100000^8307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 36824461434278399 100000000000000000000 8307 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (36824461434278399/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013531030570618877/50000000000000000000 : ℝ) ≤ (31252084742223/31250000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (50013531030570618877/50000000000000000000 : ℝ)^2048 ≤ (31252084742223/31250000000000 : ℝ)^8307 := by
      have hnat : (50013531030570618877 : ℕ)^2048*31250000000000^8307 ≤ 31252084742223^8307*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013531030570618877 50000000000000000000 31252084742223 31250000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31252084742223/31250000000000 : ℝ)) (X := (50013531030570618877/50000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012588873001224319/25000000000000000000 : ℝ) ≤ (2500310306035661/2500000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (25012588873001224319/25000000000000000000 : ℝ)^2048 ≤ (2500310306035661/2500000000000000 : ℝ)^8307 := by
      have hnat : (25012588873001224319 : ℕ)^2048*2500000000000000^8307 ≤ 2500310306035661^8307*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012588873001224319 25000000000000000000 2500310306035661 2500000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500310306035661/2500000000000000 : ℝ)) (X := (25012588873001224319/25000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036824461434278399/50000000000000000000 : ℝ) ≤ (1250226916346741/1250000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (50036824461434278399/50000000000000000000 : ℝ)^2048 ≤ (1250226916346741/1250000000000000 : ℝ)^8307 := by
      have hnat : (50036824461434278399 : ℕ)^2048*1250000000000000^8307 ≤ 1250226916346741^8307*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036824461434278399 50000000000000000000 1250226916346741 1250000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250226916346741/1250000000000000 : ℝ)) (X := (50036824461434278399/50000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13531030570618877/100000000000000000000 : ℝ) ≤ ((3891163228476353897/3892500000000000000 : ℝ)+2*(143526657821/77850000000000 : ℝ)*(11123/100000 : ℝ))^(8307/2048 : ℝ) := by
    rw [show (3891163228476353897/3892500000000000000 : ℝ)+2*(143526657821/77850000000000 : ℝ)*(11123/100000 : ℝ)=(31252084742223/31250000000000 : ℝ) by norm_num, show 1+2*(13531030570618877/100000000000000000000 : ℝ)=(50013531030570618877/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36824461434278399/100000000000000000000 : ℝ)+(13531030570618877/100000000000000000000 : ℝ) ≤ ((3891163228476353897/3892500000000000000 : ℝ)+(143526657821/77850000000000 : ℝ)*((14237/100000 : ℝ)+(11123/100000 : ℝ)))^(8307/2048 : ℝ) := by
    rw [show (3891163228476353897/3892500000000000000 : ℝ)+(143526657821/77850000000000 : ℝ)*((14237/100000 : ℝ)+(11123/100000 : ℝ))=(2500310306035661/2500000000000000 : ℝ) by norm_num, show 1+(36824461434278399/100000000000000000000 : ℝ)+(13531030570618877/100000000000000000000 : ℝ)=(25012588873001224319/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36824461434278399/100000000000000000000 : ℝ) ≤ ((3891163228476353897/3892500000000000000 : ℝ)+2*(143526657821/77850000000000 : ℝ)*(14237/100000 : ℝ))^(8307/2048 : ℝ) := by
    rw [show (3891163228476353897/3892500000000000000 : ℝ)+2*(143526657821/77850000000000 : ℝ)*(14237/100000 : ℝ)=(1250226916346741/1250000000000000 : ℝ) by norm_num, show 1+2*(36824461434278399/100000000000000000000 : ℝ)=(50036824461434278399/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3891163228476353897/3892500000000000000 : ℝ)*(X 1 0+X 2 0)+(143526657821/77850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (11123/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (3891163228476353897/3892500000000000000 : ℝ)) (alpha := (143526657821/77850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3891163228476353897/3892500000000000000 : ℝ)*(X 0 1+X 2 1)+(143526657821/77850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (11123/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (3891163228476353897/3892500000000000000 : ℝ)) (alpha := (143526657821/77850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3891163228476353897/3892500000000000000 : ℝ)*(X 0 2+X 1 2)+(143526657821/77850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (11123/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (3891163228476353897/3892500000000000000 : ℝ)) (alpha := (143526657821/77850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-136230003/625000000 : ℝ)*X 0 0+(539563291/1000000000 : ℝ)*X 0 1+(2631650007/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345380839/10000000000 : ℝ)*X 1 0+(-2246839501/10000000000 : ℝ)*X 1 1+(5263299991/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069076169/2000000000 : ℝ)*X 2 0+(1315824999/2500000000 : ℝ)*X 2 1+(-1123419743/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4368384569/10000000000 : ℝ)*X 0 0+(4239409973/10000000000 : ℝ)*X 0 1+(35166323/78125000 : ℝ)*X 0 2+(4368384569/10000000000 : ℝ)*X 1 0+(4239409973/10000000000 : ℝ)*X 1 1+(35166323/78125000 : ℝ)*X 1 2+(4368384569/10000000000 : ℝ)*X 2 0+(4239409973/10000000000 : ℝ)*X 2 1+(35166323/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-272460623/1250000000 : ℝ)*X 0 0+(5263643041/10000000000 : ℝ)*X 0 1+(5395288981/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331995123/625000000 : ℝ)*X 1 0+(-2114851251/10000000000 : ℝ)*X 1 1+(5395288451/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311922579/10000000000 : ℝ)*X 2 0+(2697644369/5000000000 : ℝ)*X 2 1+(-422970007/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174735863/400000000 : ℝ)*X 0 0+(1125152693/2500000000 : ℝ)*X 0 1+(132502807/312500000 : ℝ)*X 0 2+(174735863/400000000 : ℝ)*X 1 0+(1125152693/2500000000 : ℝ)*X 1 1+(132502807/312500000 : ℝ)*X 1 2+(174735863/400000000 : ℝ)*X 2 0+(1125152693/2500000000 : ℝ)*X 2 1+(132502807/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (126836465554894403741322451/21625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1185466897/100000000000000 : ℝ)*(base19) + (553470783/50000000000000 : ℝ)*(base23) + (46508837/100000000000000 : ℝ)*(lower2) + (131167983/100000000000000 : ℝ)*(upper3) + (45440239/50000000000000 : ℝ)*(upper5) + (5687673803367083/100000000000000 : ℝ)*(major0) + (5687673803367083/100000000000000 : ℝ)*(major1) + (5687673803367083/100000000000000 : ℝ)*(major2) + (3778365840685863/50000000000000 : ℝ)*(sp0) + (755676178424487/10000000000000 : ℝ)*(sp1) + (37783809313851/500000000000 : ℝ)*(sp2) + (3818567535998087/100000000000000 : ℝ)*(sp3) + (31288340041/100000000000000 : ℝ)*(sp4) + (4226378823/25000000000000 : ℝ)*(sp7) + (190929222075669/5000000000000 : ℝ)*(f.failure) + (7556762969711767/100000000000000 : ℝ)*(f.sum) + (25700590724651/7785000000000000000000000000 : ℝ)*base65 + (4460492663470759183/129750000000000000000000000000000 : ℝ)*base68 + (2648768956244509183/129750000000000000000000000000000 : ℝ)*base70 + (1568136273701509183/129750000000000000000000000000000 : ℝ)*base72 + (866752171361/7785000000000000000000000000 : ℝ)*base73 + (2938034097348259183/129750000000000000000000000000000 : ℝ)*base76 + (988773079534009183/129750000000000000000000000000000 : ℝ)*base78 + (2671047077176009183/129750000000000000000000000000000 : ℝ)*base80 + (26711958368263/3892500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (7087751/500000000000000000000 : ℝ)*base89 + (7087751/500000000000000000000 : ℝ)*base91 + (7087751/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79272872057654402711621603/12975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (813861587/50000000000000 : ℝ)*(base19) + (2425156383/100000000000000 : ℝ)*(base23) + (300587981/50000000000000 : ℝ)*(lower2) + (173462129/50000000000000 : ℝ)*(upper3) + (153074989/50000000000000 : ℝ)*(lower4) + (1143461953838833/20000000000000 : ℝ)*(major0) + (1143461953838833/20000000000000 : ℝ)*(major1) + (1143461953838833/20000000000000 : ℝ)*(major2) + (76062639377/100000000000000 : ℝ)*(sp2) + (883196721/100000000000000 : ℝ)*(sp3) + (59344827576001/781250000000 : ℝ)*(sp4) + (1519227260400991/20000000000000 : ℝ)*(sp5) + (474753715120773/6250000000000 : ℝ)*(sp6) + (1919240260904023/50000000000000 : ℝ)*(sp7) + (1919240702502383/50000000000000 : ℝ)*(f.failure) + (59344827576001/781250000000 : ℝ)*(f.sum) + (8374545992707/1557000000000000000000000000 : ℝ)*base65 + (202901565135305933/25950000000000000000000000000000 : ℝ)*base68 + (6023980653155933/25950000000000000000000000000000 : ℝ)*base70 + (384854267889005933/25950000000000000000000000000000 : ℝ)*base72 + (814286350297/778500000000000000000000000 : ℝ)*base74 + (538832420358305933/25950000000000000000000000000000 : ℝ)*base76 + (73955601051155933/25950000000000000000000000000000 : ℝ)*base78 + (741946819821905933/25950000000000000000000000000000 : ℝ)*base80 + (20335407443/12164062500000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (61372443/5000000000000000000000 : ℝ)*base90 + (61372443/5000000000000000000000 : ℝ)*base92 + (61372443/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1115_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11123/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (451/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1115_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1115_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3317/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4473/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (451/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1115_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1115_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1115_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3317/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4473/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (451/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1115_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

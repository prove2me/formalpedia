-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1418_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:50:49.922369+00:00
-- url     : https://prove2.me/submissions/e1463aa0-602b-41a0-a9e7-4385e9752385

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
theorem support_rectangle_w1418_s6_0 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-39601821/200000000 : ℝ)*x 0 + (2704394413/5000000000 : ℝ)*x 1 + (655831521/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (39601821/200000000 : ℝ)^2189 ≤ (6038487254417/50000000000000 : ℝ)^1677 := by
    have hnat : (39601821 : ℕ)^2189*50000000000000^1677 ≤ 6038487254417^1677*200000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39601821 200000000 6038487254417 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704394413/5000000000 : ℝ)^2189 ≤ (44834627891677/100000000000000 : ℝ)^1677 := by
    have hnat : (2704394413 : ℕ)^2189*100000000000000^1677 ≤ 44834627891677^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704394413 5000000000 44834627891677 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655831521/1250000000 : ℝ)^2189 ≤ (10772099397411/25000000000000 : ℝ)^1677 := by
    have hnat : (655831521 : ℕ)^2189*25000000000000^1677 ≤ 10772099397411^1677*1250000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655831521 1250000000 10772099397411 25000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-39601821/200000000 : ℝ), (2704394413/5000000000 : ℝ), (655831521/1250000000 : ℝ)] ![(6038487254417/50000000000000 : ℝ), (44834627891677/100000000000000 : ℝ), (10772099397411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-39601821/200000000 : ℝ)|^2189 ≤ (6038487254417/50000000000000 : ℝ)^1677
        have hw : |(-39601821/200000000 : ℝ)|=(39601821/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704394413/5000000000 : ℝ)|^2189 ≤ (44834627891677/100000000000000 : ℝ)^1677
        have hw : |(2704394413/5000000000 : ℝ)|=(2704394413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655831521/1250000000 : ℝ)|^2189 ≤ (10772099397411/25000000000000 : ℝ)^1677
        have hw : |(655831521/1250000000 : ℝ)|=(655831521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s6_1 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (20888893/39062500 : ℝ)*x 0 + (-2062645061/10000000000 : ℝ)*x 1 + (1049330433/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20888893/39062500 : ℝ)^2189 ≤ (22086622414553/50000000000000 : ℝ)^1677 := by
    have hnat : (20888893 : ℕ)^2189*50000000000000^1677 ≤ 22086622414553^1677*39062500^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20888893 39062500 22086622414553 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062645061/10000000000 : ℝ)^2189 ≤ (12738357601373/100000000000000 : ℝ)^1677 := by
    have hnat : (2062645061 : ℕ)^2189*100000000000000^1677 ≤ 12738357601373^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062645061 10000000000 12738357601373 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049330433/2000000000 : ℝ)^2189 ≤ (10772099389371/25000000000000 : ℝ)^1677 := by
    have hnat : (1049330433 : ℕ)^2189*25000000000000^1677 ≤ 10772099389371^1677*2000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049330433 2000000000 10772099389371 25000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20888893/39062500 : ℝ), (-2062645061/10000000000 : ℝ), (1049330433/2000000000 : ℝ)] ![(22086622414553/50000000000000 : ℝ), (12738357601373/100000000000000 : ℝ), (10772099389371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20888893/39062500 : ℝ)|^2189 ≤ (22086622414553/50000000000000 : ℝ)^1677
        have hw : |(20888893/39062500 : ℝ)|=(20888893/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2062645061/10000000000 : ℝ)|^2189 ≤ (12738357601373/100000000000000 : ℝ)^1677
        have hw : |(-2062645061/10000000000 : ℝ)|=(2062645061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049330433/2000000000 : ℝ)|^2189 ≤ (10772099389371/25000000000000 : ℝ)^1677
        have hw : |(1049330433/2000000000 : ℝ)|=(1049330433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s6_2 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347556609/10000000000 : ℝ)*x 0 + (655831521/1250000000 : ℝ)*x 1 + (-2062645057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347556609/10000000000 : ℝ)^2189 ≤ (2760827802493/6250000000000 : ℝ)^1677 := by
    have hnat : (5347556609 : ℕ)^2189*6250000000000^1677 ≤ 2760827802493^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347556609 10000000000 2760827802493 6250000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655831521/1250000000 : ℝ)^2189 ≤ (10772099397411/25000000000000 : ℝ)^1677 := by
    have hnat : (655831521 : ℕ)^2189*25000000000000^1677 ≤ 10772099397411^1677*1250000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655831521 1250000000 10772099397411 25000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2062645057/10000000000 : ℝ)^2189 ≤ (1592294696141/12500000000000 : ℝ)^1677 := by
    have hnat : (2062645057 : ℕ)^2189*12500000000000^1677 ≤ 1592294696141^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062645057 10000000000 1592294696141 12500000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347556609/10000000000 : ℝ), (655831521/1250000000 : ℝ), (-2062645057/10000000000 : ℝ)] ![(2760827802493/6250000000000 : ℝ), (10772099397411/25000000000000 : ℝ), (1592294696141/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347556609/10000000000 : ℝ)|^2189 ≤ (2760827802493/6250000000000 : ℝ)^1677
        have hw : |(5347556609/10000000000 : ℝ)|=(5347556609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655831521/1250000000 : ℝ)|^2189 ≤ (10772099397411/25000000000000 : ℝ)^1677
        have hw : |(655831521/1250000000 : ℝ)|=(655831521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2062645057/10000000000 : ℝ)|^2189 ≤ (1592294696141/12500000000000 : ℝ)^1677
        have hw : |(-2062645057/10000000000 : ℝ)|=(2062645057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s6_3 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4307131361/10000000000 : ℝ)*x 0 + (413566109/1000000000 : ℝ)*x 1 + (4485003769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307131361/10000000000 : ℝ)^2189 ≤ (33304518075869/100000000000000 : ℝ)^1677 := by
    have hnat : (4307131361 : ℕ)^2189*100000000000000^1677 ≤ 33304518075869^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307131361 10000000000 33304518075869 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (413566109/1000000000 : ℝ)^2189 ≤ (31584455308973/100000000000000 : ℝ)^1677 := by
    have hnat : (413566109 : ℕ)^2189*100000000000000^1677 ≤ 31584455308973^1677*1000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413566109 1000000000 31584455308973 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4485003769/10000000000 : ℝ)^2189 ≤ (35111026600817/100000000000000 : ℝ)^1677 := by
    have hnat : (4485003769 : ℕ)^2189*100000000000000^1677 ≤ 35111026600817^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485003769 10000000000 35111026600817 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307131361/10000000000 : ℝ), (413566109/1000000000 : ℝ), (4485003769/10000000000 : ℝ)] ![(33304518075869/100000000000000 : ℝ), (31584455308973/100000000000000 : ℝ), (35111026600817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307131361/10000000000 : ℝ)|^2189 ≤ (33304518075869/100000000000000 : ℝ)^1677
        have hw : |(4307131361/10000000000 : ℝ)|=(4307131361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(413566109/1000000000 : ℝ)|^2189 ≤ (31584455308973/100000000000000 : ℝ)^1677
        have hw : |(413566109/1000000000 : ℝ)|=(413566109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4485003769/10000000000 : ℝ)|^2189 ≤ (35111026600817/100000000000000 : ℝ)^1677
        have hw : |(4485003769/10000000000 : ℝ)|=(4485003769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s6_4 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1980102343/10000000000 : ℝ)*x 0 + (5247236681/10000000000 : ℝ)*x 1 + (540820139/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1980102343/10000000000 : ℝ)^2189 ≤ (483082576649/4000000000000 : ℝ)^1677 := by
    have hnat : (1980102343 : ℕ)^2189*4000000000000^1677 ≤ 483082576649^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980102343 10000000000 483082576649 4000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247236681/10000000000 : ℝ)^2189 ≤ (43094663617619/100000000000000 : ℝ)^1677 := by
    have hnat : (5247236681 : ℕ)^2189*100000000000000^1677 ≤ 43094663617619^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247236681 10000000000 43094663617619 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540820139/1000000000 : ℝ)^2189 ≤ (8965654390887/20000000000000 : ℝ)^1677 := by
    have hnat : (540820139 : ℕ)^2189*20000000000000^1677 ≤ 8965654390887^1677*1000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540820139 1000000000 8965654390887 20000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1980102343/10000000000 : ℝ), (5247236681/10000000000 : ℝ), (540820139/1000000000 : ℝ)] ![(483082576649/4000000000000 : ℝ), (43094663617619/100000000000000 : ℝ), (8965654390887/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1980102343/10000000000 : ℝ)|^2189 ≤ (483082576649/4000000000000 : ℝ)^1677
        have hw : |(-1980102343/10000000000 : ℝ)|=(1980102343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247236681/10000000000 : ℝ)|^2189 ≤ (43094663617619/100000000000000 : ℝ)^1677
        have hw : |(5247236681/10000000000 : ℝ)|=(5247236681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540820139/1000000000 : ℝ)|^2189 ≤ (8965654390887/20000000000000 : ℝ)^1677
        have hw : |(540820139/1000000000 : ℝ)|=(540820139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s6_5 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652725559/5000000000 : ℝ)*x 0 + (-950547943/5000000000 : ℝ)*x 1 + (2704100789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652725559/5000000000 : ℝ)^2189 ≤ (21859896028323/50000000000000 : ℝ)^1677 := by
    have hnat : (2652725559 : ℕ)^2189*50000000000000^1677 ≤ 21859896028323^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652725559 5000000000 21859896028323 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (950547943/5000000000 : ℝ)^2189 ≤ (11451933929783/100000000000000 : ℝ)^1677 := by
    have hnat : (950547943 : ℕ)^2189*100000000000000^1677 ≤ 11451933929783^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950547943 5000000000 11451933929783 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704100789/5000000000 : ℝ)^2189 ≤ (44828273988523/100000000000000 : ℝ)^1677 := by
    have hnat : (2704100789 : ℕ)^2189*100000000000000^1677 ≤ 44828273988523^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704100789 5000000000 44828273988523 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652725559/5000000000 : ℝ), (-950547943/5000000000 : ℝ), (2704100789/5000000000 : ℝ)] ![(21859896028323/50000000000000 : ℝ), (11451933929783/100000000000000 : ℝ), (44828273988523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652725559/5000000000 : ℝ)|^2189 ≤ (21859896028323/50000000000000 : ℝ)^1677
        have hw : |(2652725559/5000000000 : ℝ)|=(2652725559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-950547943/5000000000 : ℝ)|^2189 ≤ (11451933929783/100000000000000 : ℝ)^1677
        have hw : |(-950547943/5000000000 : ℝ)|=(950547943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704100789/5000000000 : ℝ)|^2189 ≤ (44828273988523/100000000000000 : ℝ)^1677
        have hw : |(2704100789/5000000000 : ℝ)|=(2704100789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s6_6 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061090131/2000000000 : ℝ)*x 0 + (5408202191/10000000000 : ℝ)*x 1 + (-1901095677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061090131/2000000000 : ℝ)^2189 ≤ (8743957415283/20000000000000 : ℝ)^1677 := by
    have hnat : (1061090131 : ℕ)^2189*20000000000000^1677 ≤ 8743957415283^1677*2000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061090131 2000000000 8743957415283 20000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408202191/10000000000 : ℝ)^2189 ≤ (11207070155237/25000000000000 : ℝ)^1677 := by
    have hnat : (5408202191 : ℕ)^2189*25000000000000^1677 ≤ 11207070155237^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408202191 10000000000 11207070155237 25000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1901095677/10000000000 : ℝ)^2189 ≤ (11451932286419/100000000000000 : ℝ)^1677 := by
    have hnat : (1901095677 : ℕ)^2189*100000000000000^1677 ≤ 11451932286419^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901095677 10000000000 11451932286419 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061090131/2000000000 : ℝ), (5408202191/10000000000 : ℝ), (-1901095677/10000000000 : ℝ)] ![(8743957415283/20000000000000 : ℝ), (11207070155237/25000000000000 : ℝ), (11451932286419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061090131/2000000000 : ℝ)|^2189 ≤ (8743957415283/20000000000000 : ℝ)^1677
        have hw : |(1061090131/2000000000 : ℝ)|=(1061090131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408202191/10000000000 : ℝ)|^2189 ≤ (11207070155237/25000000000000 : ℝ)^1677
        have hw : |(5408202191/10000000000 : ℝ)|=(5408202191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1901095677/10000000000 : ℝ)|^2189 ≤ (11451932286419/100000000000000 : ℝ)^1677
        have hw : |(-1901095677/10000000000 : ℝ)|=(1901095677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s6_7 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2153577883/5000000000 : ℝ)*x 0 + (140117037/312500000 : ℝ)*x 1 + (2585579/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153577883/5000000000 : ℝ)^2189 ≤ (33304764399979/100000000000000 : ℝ)^1677 := by
    have hnat : (2153577883 : ℕ)^2189*100000000000000^1677 ≤ 33304764399979^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153577883 5000000000 33304764399979 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140117037/312500000 : ℝ)^2189 ≤ (17549083057717/50000000000000 : ℝ)^1677 := by
    have hnat : (140117037 : ℕ)^2189*50000000000000^1677 ≤ 17549083057717^1677*312500000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140117037 312500000 17549083057717 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2585579/6250000 : ℝ)^2189 ≤ (3159706947/10000000000 : ℝ)^1677 := by
    have hnat : (2585579 : ℕ)^2189*10000000000^1677 ≤ 3159706947^1677*6250000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585579 6250000 3159706947 10000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153577883/5000000000 : ℝ), (140117037/312500000 : ℝ), (2585579/6250000 : ℝ)] ![(33304764399979/100000000000000 : ℝ), (17549083057717/50000000000000 : ℝ), (3159706947/10000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153577883/5000000000 : ℝ)|^2189 ≤ (33304764399979/100000000000000 : ℝ)^1677
        have hw : |(2153577883/5000000000 : ℝ)|=(2153577883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140117037/312500000 : ℝ)|^2189 ≤ (17549083057717/50000000000000 : ℝ)^1677
        have hw : |(140117037/312500000 : ℝ)|=(140117037/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2585579/6250000 : ℝ)|^2189 ≤ (3159706947/10000000000 : ℝ)^1677
        have hw : |(2585579/6250000 : ℝ)|=(2585579/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1418_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78865469/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11317/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14751/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11313/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11313/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11313/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11313/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11313/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11313/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (11313/100000 : ℝ) ^ (4377/1024 : ℝ) ≤ (2251850699645487/25000000000000000000 : ℝ) := by
    have hpowers : (11313/100000 : ℝ)^4377 ≤ (2251850699645487/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11313 : ℕ)^4377*25000000000000000000^1024 ≤ 2251850699645487^1024*100000^4377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11313 100000 2251850699645487 25000000000000000000 4377 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11313/100000 : ℝ)) (X := (2251850699645487/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2951/20000 : ℝ) ^ (4377/1024 : ℝ) ≤ (28035098662530139/100000000000000000000 : ℝ) := by
    have hpowers : (2951/20000 : ℝ)^4377 ≤ (28035098662530139/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2951 : ℕ)^4377*100000000000000000000^1024 ≤ 28035098662530139^1024*20000^4377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2951 20000 28035098662530139 100000000000000000000 4377 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2951/20000 : ℝ)) (X := (28035098662530139/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502251850699645487/12500000000000000000 : ℝ) ≤ (2000084285529771/2000000000000000 : ℝ) ^ (4377/1024 : ℝ) := by
    have hpowers : (12502251850699645487/12500000000000000000 : ℝ)^1024 ≤ (2000084285529771/2000000000000000 : ℝ)^4377 := by
      have hnat : (12502251850699645487 : ℕ)^1024*2000000000000000^4377 ≤ 2000084285529771^4377*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502251850699645487 12500000000000000000 2000084285529771 2000000000000000 1024 4377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000084285529771/2000000000000000 : ℝ)) (X := (12502251850699645487/12500000000000000000 : ℝ)) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037042501461112087/100000000000000000000 : ℝ) ≤ (625054155444467/625000000000000 : ℝ) ^ (4377/1024 : ℝ) := by
    have hpowers : (100037042501461112087/100000000000000000000 : ℝ)^1024 ≤ (625054155444467/625000000000000 : ℝ)^4377 := by
      have hnat : (100037042501461112087 : ℕ)^1024*625000000000000^4377 ≤ 625054155444467^4377*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037042501461112087 100000000000000000000 625054155444467 625000000000000 1024 4377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625054155444467/625000000000000 : ℝ)) (X := (100037042501461112087/100000000000000000000 : ℝ)) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028035098662530139/50000000000000000000 : ℝ) ≤ (10001311546574089/10000000000000000 : ℝ) ^ (4377/1024 : ℝ) := by
    have hpowers : (50028035098662530139/50000000000000000000 : ℝ)^1024 ≤ (10001311546574089/10000000000000000 : ℝ)^4377 := by
      have hnat : (50028035098662530139 : ℕ)^1024*10000000000000000^4377 ≤ 10001311546574089^4377*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028035098662530139 50000000000000000000 10001311546574089 10000000000000000 1024 4377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001311546574089/10000000000000000 : ℝ)) (X := (50028035098662530139/50000000000000000000 : ℝ)) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2251850699645487/25000000000000000000 : ℝ) ≤ ((8602845159641546667/8605000000000000000 : ℝ)+2*(445059462617/344200000000000 : ℝ)*(11313/100000 : ℝ))^(4377/1024 : ℝ) := by
    rw [show (8602845159641546667/8605000000000000000 : ℝ)+2*(445059462617/344200000000000 : ℝ)*(11313/100000 : ℝ)=(2000084285529771/2000000000000000 : ℝ) by norm_num, show 1+2*(2251850699645487/25000000000000000000 : ℝ)=(12502251850699645487/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28035098662530139/100000000000000000000 : ℝ)+(2251850699645487/25000000000000000000 : ℝ) ≤ ((8602845159641546667/8605000000000000000 : ℝ)+(445059462617/344200000000000 : ℝ)*((2951/20000 : ℝ)+(11313/100000 : ℝ)))^(4377/1024 : ℝ) := by
    rw [show (8602845159641546667/8605000000000000000 : ℝ)+(445059462617/344200000000000 : ℝ)*((2951/20000 : ℝ)+(11313/100000 : ℝ))=(625054155444467/625000000000000 : ℝ) by norm_num, show 1+(28035098662530139/100000000000000000000 : ℝ)+(2251850699645487/25000000000000000000 : ℝ)=(100037042501461112087/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28035098662530139/100000000000000000000 : ℝ) ≤ ((8602845159641546667/8605000000000000000 : ℝ)+2*(445059462617/344200000000000 : ℝ)*(2951/20000 : ℝ))^(4377/1024 : ℝ) := by
    rw [show (8602845159641546667/8605000000000000000 : ℝ)+2*(445059462617/344200000000000 : ℝ)*(2951/20000 : ℝ)=(10001311546574089/10000000000000000 : ℝ) by norm_num, show 1+2*(28035098662530139/100000000000000000000 : ℝ)=(50028035098662530139/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8602845159641546667/8605000000000000000 : ℝ)*(X 1 0+X 2 0)+(445059462617/344200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4377/1024 : ℝ)) (lo := (11313/100000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (8602845159641546667/8605000000000000000 : ℝ)) (alpha := (445059462617/344200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8602845159641546667/8605000000000000000 : ℝ)*(X 0 1+X 2 1)+(445059462617/344200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4377/1024 : ℝ)) (lo := (11313/100000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (8602845159641546667/8605000000000000000 : ℝ)) (alpha := (445059462617/344200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8602845159641546667/8605000000000000000 : ℝ)*(X 0 2+X 1 2)+(445059462617/344200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4377/1024 : ℝ)) (lo := (11313/100000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (8602845159641546667/8605000000000000000 : ℝ)) (alpha := (445059462617/344200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-39601821/200000000 : ℝ)*X 0 0+(2704394413/5000000000 : ℝ)*X 0 1+(655831521/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((20888893/39062500 : ℝ)*X 1 0+(-2062645061/10000000000 : ℝ)*X 1 1+(1049330433/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347556609/10000000000 : ℝ)*X 2 0+(655831521/1250000000 : ℝ)*X 2 1+(-2062645057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4307131361/10000000000 : ℝ)*X 0 0+(413566109/1000000000 : ℝ)*X 0 1+(4485003769/10000000000 : ℝ)*X 0 2+(4307131361/10000000000 : ℝ)*X 1 0+(413566109/1000000000 : ℝ)*X 1 1+(4485003769/10000000000 : ℝ)*X 1 2+(4307131361/10000000000 : ℝ)*X 2 0+(413566109/1000000000 : ℝ)*X 2 1+(4485003769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1980102343/10000000000 : ℝ)*X 0 0+(5247236681/10000000000 : ℝ)*X 0 1+(540820139/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652725559/5000000000 : ℝ)*X 1 0+(-950547943/5000000000 : ℝ)*X 1 1+(2704100789/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061090131/2000000000 : ℝ)*X 2 0+(5408202191/10000000000 : ℝ)*X 2 1+(-1901095677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2153577883/5000000000 : ℝ)*X 0 0+(140117037/312500000 : ℝ)*X 0 1+(2585579/6250000 : ℝ)*X 0 2+(2153577883/5000000000 : ℝ)*X 1 0+(140117037/312500000 : ℝ)*X 1 1+(2585579/6250000 : ℝ)*X 1 2+(2153577883/5000000000 : ℝ)*X 2 0+(140117037/312500000 : ℝ)*X 2 1+(2585579/6250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3738931134507950688917615163/430250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6215737/390625000000 : ℝ)*(base19) + (741132099/50000000000000 : ℝ)*(base23) + (2944307/5000000000000 : ℝ)*(lower2) + (13420651/6250000000000 : ℝ)*(upper3) + (70242253/50000000000000 : ℝ)*(upper5) + (4515127791145163/100000000000000 : ℝ)*(major0) + (4515127791145163/100000000000000 : ℝ)*(major1) + (4515127791145163/100000000000000 : ℝ)*(major2) + (3083835678116251/50000000000000 : ℝ)*(sp0) + (1233540635615531/20000000000000 : ℝ)*(sp1) + (6167703287042129/100000000000000 : ℝ)*(sp2) + (2862533844765579/100000000000000 : ℝ)*(sp3) + (1336522953/4000000000000 : ℝ)*(sp4) + (8339273603/50000000000000 : ℝ)*(sp7) + (178909407707049/6250000000000 : ℝ)*(f.failure) + (6167704769306327/100000000000000 : ℝ)*(f.sum) + (135573206171/17210000000000000000000000000 : ℝ)*base65 + (1254211890719596721/860500000000000000000000000000000 : ℝ)*base67 + (4199389496963403279/860500000000000000000000000000000 : ℝ)*base70 + (1457509780602403279/860500000000000000000000000000000 : ℝ)*base72 + (111970905793819/17210000000000000000000000000 : ℝ)*base74 + (10804494553497903279/860500000000000000000000000000000 : ℝ)*base76 + (1758190490177096721/860500000000000000000000000000000 : ℝ)*base77 + (7908898251077903279/860500000000000000000000000000000 : ℝ)*base80 + (37123484047009/17210000000000000000000000000 : ℝ)*base82 + (384019/312500000000000000000 : ℝ)*base90 + (384019/312500000000000000000 : ℝ)*base92 + (384019/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (240848314165668907055317413/53781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50803083/50000000000000 : ℝ)*(base21) + (361853/250000000000 : ℝ)*(base29) + (62258101/100000000000000 : ℝ)*(upper2) + (7740769/20000000000000 : ℝ)*(upper3) + (114360083/100000000000000 : ℝ)*(lower4) + (568493183603663/12500000000000 : ℝ)*(major0) + (568493201696313/12500000000000 : ℝ)*(major1) + (568493201696313/12500000000000 : ℝ)*(major2) + (15038879237/100000000000000 : ℝ)*(sp2) + (4058365663/100000000000000 : ℝ)*(sp3) + (24850137397911/400000000000 : ℝ)*(sp4) + (6212534204736551/100000000000000 : ℝ)*(sp5) + (6212519064251147/100000000000000 : ℝ)*(sp6) + (288335267002107/10000000000000 : ℝ)*(sp7) + (720839182096683/25000000000000 : ℝ)*(f.failure) + (24850137397911/400000000000 : ℝ)*(f.sum) + (19117993400881/8605000000000000000000000000 : ℝ)*base66 + (460770108423113771/107562500000000000000000000000000 : ℝ)*base67 + (2322288791444823729/107562500000000000000000000000000 : ℝ)*base70 + (621433687444146279/107562500000000000000000000000000 : ℝ)*base72 + (10186427096959/2151250000000000000000000000 : ℝ)*base74 + (1135520461482801271/107562500000000000000000000000000 : ℝ)*base75 + (2268157973481646279/107562500000000000000000000000000 : ℝ)*base78 + (9657329735522073729/107562500000000000000000000000000 : ℝ)*base80 + (34896102143111/8605000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (8139327/1250000000000000000000 : ℝ)*base89 + (8139327/1250000000000000000000 : ℝ)*base91 + (8139327/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1418_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78865469/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1418_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1418_s7_0 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1980093849/10000000000 : ℝ)*x 0 + (1352189893/2500000000 : ℝ)*x 1 + (81979369/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1980093849/10000000000 : ℝ)^2189 ≤ (2415399358521/20000000000000 : ℝ)^1677 := by
    have hnat : (1980093849 : ℕ)^2189*20000000000000^1677 ≤ 2415399358521^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980093849 10000000000 2415399358521 20000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352189893/2500000000 : ℝ)^2189 ≤ (112085778411/250000000000 : ℝ)^1677 := by
    have hnat : (1352189893 : ℕ)^2189*250000000000^1677 ≤ 112085778411^1677*2500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352189893 2500000000 112085778411 250000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81979369/156250000 : ℝ)^2189 ≤ (21544345914859/50000000000000 : ℝ)^1677 := by
    have hnat : (81979369 : ℕ)^2189*50000000000000^1677 ≤ 21544345914859^1677*156250000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81979369 156250000 21544345914859 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1980093849/10000000000 : ℝ), (1352189893/2500000000 : ℝ), (81979369/156250000 : ℝ)] ![(2415399358521/20000000000000 : ℝ), (112085778411/250000000000 : ℝ), (21544345914859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1980093849/10000000000 : ℝ)|^2189 ≤ (2415399358521/20000000000000 : ℝ)^1677
        have hw : |(-1980093849/10000000000 : ℝ)|=(1980093849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352189893/2500000000 : ℝ)|^2189 ≤ (112085778411/250000000000 : ℝ)^1677
        have hw : |(1352189893/2500000000 : ℝ)|=(1352189893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81979369/156250000 : ℝ)|^2189 ≤ (21544345914859/50000000000000 : ℝ)^1677
        have hw : |(81979369/156250000 : ℝ)|=(81979369/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s7_1 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673774583/5000000000 : ℝ)*x 0 + (-412523687/2000000000 : ℝ)*x 1 + (5246679673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673774583/5000000000 : ℝ)^2189 ≤ (8834632917257/20000000000000 : ℝ)^1677 := by
    have hnat : (2673774583 : ℕ)^2189*20000000000000^1677 ≤ 8834632917257^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673774583 5000000000 8834632917257 20000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412523687/2000000000 : ℝ)^2189 ≤ (12738142963327/100000000000000 : ℝ)^1677 := by
    have hnat : (412523687 : ℕ)^2189*100000000000000^1677 ≤ 12738142963327^1677*2000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412523687 2000000000 12738142963327 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246679673/10000000000 : ℝ)^2189 ≤ (43088692440753/100000000000000 : ℝ)^1677 := by
    have hnat : (5246679673 : ℕ)^2189*100000000000000^1677 ≤ 43088692440753^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246679673 10000000000 43088692440753 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673774583/5000000000 : ℝ), (-412523687/2000000000 : ℝ), (5246679673/10000000000 : ℝ)] ![(8834632917257/20000000000000 : ℝ), (12738142963327/100000000000000 : ℝ), (43088692440753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673774583/5000000000 : ℝ)|^2189 ≤ (8834632917257/20000000000000 : ℝ)^1677
        have hw : |(2673774583/5000000000 : ℝ)|=(2673774583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-412523687/2000000000 : ℝ)|^2189 ≤ (12738142963327/100000000000000 : ℝ)^1677
        have hw : |(-412523687/2000000000 : ℝ)|=(412523687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246679673/10000000000 : ℝ)|^2189 ≤ (43088692440753/100000000000000 : ℝ)^1677
        have hw : |(5246679673/10000000000 : ℝ)|=(5246679673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s7_2 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673774573/5000000000 : ℝ)*x 0 + (5246679693/10000000000 : ℝ)*x 1 + (-412523687/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673774573/5000000000 : ℝ)^2189 ≤ (44173164370637/100000000000000 : ℝ)^1677 := by
    have hnat : (2673774573 : ℕ)^2189*100000000000000^1677 ≤ 44173164370637^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673774573 5000000000 44173164370637 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246679693/10000000000 : ℝ)^2189 ≤ (43088692655151/100000000000000 : ℝ)^1677 := by
    have hnat : (5246679693 : ℕ)^2189*100000000000000^1677 ≤ 43088692655151^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246679693 10000000000 43088692655151 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (412523687/2000000000 : ℝ)^2189 ≤ (12738142963327/100000000000000 : ℝ)^1677 := by
    have hnat : (412523687 : ℕ)^2189*100000000000000^1677 ≤ 12738142963327^1677*2000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412523687 2000000000 12738142963327 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673774573/5000000000 : ℝ), (5246679693/10000000000 : ℝ), (-412523687/2000000000 : ℝ)] ![(44173164370637/100000000000000 : ℝ), (43088692655151/100000000000000 : ℝ), (12738142963327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673774573/5000000000 : ℝ)|^2189 ≤ (44173164370637/100000000000000 : ℝ)^1677
        have hw : |(2673774573/5000000000 : ℝ)|=(2673774573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246679693/10000000000 : ℝ)|^2189 ≤ (43088692655151/100000000000000 : ℝ)^1677
        have hw : |(5246679693/10000000000 : ℝ)|=(5246679693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-412523687/2000000000 : ℝ)|^2189 ≤ (12738142963327/100000000000000 : ℝ)^1677
        have hw : |(-412523687/2000000000 : ℝ)|=(412523687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s7_3 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (430713337/1000000000 : ℝ)*x 0 + (1033930499/2500000000 : ℝ)*x 1 + (140154449/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430713337/1000000000 : ℝ)^2189 ≤ (1040766823533/3125000000000 : ℝ)^1677 := by
    have hnat : (430713337 : ℕ)^2189*3125000000000^1677 ≤ 1040766823533^1677*1000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430713337 1000000000 1040766823533 3125000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033930499/2500000000 : ℝ)^2189 ≤ (15792531233823/50000000000000 : ℝ)^1677 := by
    have hnat : (1033930499 : ℕ)^2189*50000000000000^1677 ≤ 15792531233823^1677*2500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033930499 2500000000 15792531233823 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140154449/312500000 : ℝ)^2189 ≤ (35110399166959/100000000000000 : ℝ)^1677 := by
    have hnat : (140154449 : ℕ)^2189*100000000000000^1677 ≤ 35110399166959^1677*312500000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140154449 312500000 35110399166959 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(430713337/1000000000 : ℝ), (1033930499/2500000000 : ℝ), (140154449/312500000 : ℝ)] ![(1040766823533/3125000000000 : ℝ), (15792531233823/50000000000000 : ℝ), (35110399166959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(430713337/1000000000 : ℝ)|^2189 ≤ (1040766823533/3125000000000 : ℝ)^1677
        have hw : |(430713337/1000000000 : ℝ)|=(430713337/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1033930499/2500000000 : ℝ)|^2189 ≤ (15792531233823/50000000000000 : ℝ)^1677
        have hw : |(1033930499/2500000000 : ℝ)|=(1033930499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140154449/312500000 : ℝ)|^2189 ≤ (35110399166959/100000000000000 : ℝ)^1677
        have hw : |(140154449/312500000 : ℝ)|=(140154449/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s7_4 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1980105537/10000000000 : ℝ)*x 0 + (2623631731/5000000000 : ℝ)*x 1 + (676021563/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1980105537/10000000000 : ℝ)^2189 ≤ (12077089844767/100000000000000 : ℝ)^1677 := by
    have hnat : (1980105537 : ℕ)^2189*100000000000000^1677 ≤ 12077089844767^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980105537 10000000000 12077089844767 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623631731/5000000000 : ℝ)^2189 ≤ (5386868839659/12500000000000 : ℝ)^1677 := by
    have hnat : (2623631731 : ℕ)^2189*12500000000000^1677 ≤ 5386868839659^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623631731 5000000000 5386868839659 12500000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676021563/1250000000 : ℝ)^2189 ≤ (44827959419267/100000000000000 : ℝ)^1677 := by
    have hnat : (676021563 : ℕ)^2189*100000000000000^1677 ≤ 44827959419267^1677*1250000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676021563 1250000000 44827959419267 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1980105537/10000000000 : ℝ), (2623631731/5000000000 : ℝ), (676021563/1250000000 : ℝ)] ![(12077089844767/100000000000000 : ℝ), (5386868839659/12500000000000 : ℝ), (44827959419267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1980105537/10000000000 : ℝ)|^2189 ≤ (12077089844767/100000000000000 : ℝ)^1677
        have hw : |(-1980105537/10000000000 : ℝ)|=(1980105537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623631731/5000000000 : ℝ)|^2189 ≤ (5386868839659/12500000000000 : ℝ)^1677
        have hw : |(2623631731/5000000000 : ℝ)|=(2623631731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676021563/1250000000 : ℝ)|^2189 ≤ (44827959419267/100000000000000 : ℝ)^1677
        have hw : |(676021563/1250000000 : ℝ)|=(676021563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_s7_5 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4307158609/10000000000 : ℝ)*x 0 + (2241841921/5000000000 : ℝ)*x 1 + (413698639/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307158609/10000000000 : ℝ)^2189 ≤ (8326198273731/25000000000000 : ℝ)^1677 := by
    have hnat : (4307158609 : ℕ)^2189*25000000000000^1677 ≤ 8326198273731^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307158609 10000000000 8326198273731 25000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241841921/5000000000 : ℝ)^2189 ≤ (35097539338183/100000000000000 : ℝ)^1677 := by
    have hnat : (2241841921 : ℕ)^2189*100000000000000^1677 ≤ 35097539338183^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241841921 5000000000 35097539338183 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413698639/1000000000 : ℝ)^2189 ≤ (31597667553103/100000000000000 : ℝ)^1677 := by
    have hnat : (413698639 : ℕ)^2189*100000000000000^1677 ≤ 31597667553103^1677*1000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413698639 1000000000 31597667553103 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307158609/10000000000 : ℝ), (2241841921/5000000000 : ℝ), (413698639/1000000000 : ℝ)] ![(8326198273731/25000000000000 : ℝ), (35097539338183/100000000000000 : ℝ), (31597667553103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307158609/10000000000 : ℝ)|^2189 ≤ (8326198273731/25000000000000 : ℝ)^1677
        have hw : |(4307158609/10000000000 : ℝ)|=(4307158609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2241841921/5000000000 : ℝ)|^2189 ≤ (35097539338183/100000000000000 : ℝ)^1677
        have hw : |(2241841921/5000000000 : ℝ)|=(2241841921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(413698639/1000000000 : ℝ)|^2189 ≤ (31597667553103/100000000000000 : ℝ)^1677
        have hw : |(413698639/1000000000 : ℝ)|=(413698639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1418_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78865469/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5659/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14751/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14751/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11317/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11317/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11317/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11317/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11317/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11317/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11317/100000 : ℝ) ^ (4377/1024 : ℝ) ≤ (4510511911568159/50000000000000000000 : ℝ) := by
    have hpowers : (11317/100000 : ℝ)^4377 ≤ (4510511911568159/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11317 : ℕ)^4377*50000000000000000000^1024 ≤ 4510511911568159^1024*100000^4377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11317 100000 4510511911568159 50000000000000000000 4377 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11317/100000 : ℝ)) (X := (4510511911568159/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14751/100000 : ℝ) ^ (4377/1024 : ℝ) ≤ (14001313418802101/50000000000000000000 : ℝ) := by
    have hpowers : (14751/100000 : ℝ)^4377 ≤ (14001313418802101/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14751 : ℕ)^4377*50000000000000000000^1024 ≤ 14001313418802101^1024*100000^4377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14751 100000 14001313418802101 50000000000000000000 4377 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14751/100000 : ℝ)) (X := (14001313418802101/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004510511911568159/25000000000000000000 : ℝ) ≤ (5000211032444559/5000000000000000 : ℝ) ^ (4377/1024 : ℝ) := by
    have hpowers : (25004510511911568159/25000000000000000000 : ℝ)^1024 ≤ (5000211032444559/5000000000000000 : ℝ)^4377 := by
      have hnat : (25004510511911568159 : ℕ)^1024*5000000000000000^4377 ≤ 5000211032444559^4377*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004510511911568159 25000000000000000000 5000211032444559 5000000000000000 1024 4377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000211032444559/5000000000000000 : ℝ)) (X := (25004510511911568159/25000000000000000000 : ℝ)) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2500925591266518513/2500000000000000000 : ℝ) ≤ (10000866046221703/10000000000000000 : ℝ) ^ (4377/1024 : ℝ) := by
    have hpowers : (2500925591266518513/2500000000000000000 : ℝ)^1024 ≤ (10000866046221703/10000000000000000 : ℝ)^4377 := by
      have hnat : (2500925591266518513 : ℕ)^1024*10000000000000000^4377 ≤ 10000866046221703^4377*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500925591266518513 2500000000000000000 10000866046221703 10000000000000000 1024 4377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000866046221703/10000000000000000 : ℝ)) (X := (2500925591266518513/2500000000000000000 : ℝ)) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014001313418802101/25000000000000000000 : ℝ) ≤ (625081876722143/625000000000000 : ℝ) ^ (4377/1024 : ℝ) := by
    have hpowers : (25014001313418802101/25000000000000000000 : ℝ)^1024 ≤ (625081876722143/625000000000000 : ℝ)^4377 := by
      have hnat : (25014001313418802101 : ℕ)^1024*625000000000000^4377 ≤ 625081876722143^4377*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014001313418802101 25000000000000000000 625081876722143 625000000000000 1024 4377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625081876722143/625000000000000 : ℝ)) (X := (25014001313418802101/25000000000000000000 : ℝ)) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4510511911568159/50000000000000000000 : ℝ) ≤ ((17165700148673751161/17170000000000000000 : ℝ)+2*(88796266517/68680000000000 : ℝ)*(11317/100000 : ℝ))^(4377/1024 : ℝ) := by
    rw [show (17165700148673751161/17170000000000000000 : ℝ)+2*(88796266517/68680000000000 : ℝ)*(11317/100000 : ℝ)=(5000211032444559/5000000000000000 : ℝ) by norm_num, show 1+2*(4510511911568159/50000000000000000000 : ℝ)=(25004510511911568159/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14001313418802101/50000000000000000000 : ℝ)+(4510511911568159/50000000000000000000 : ℝ) ≤ ((17165700148673751161/17170000000000000000 : ℝ)+(88796266517/68680000000000 : ℝ)*((14751/100000 : ℝ)+(11317/100000 : ℝ)))^(4377/1024 : ℝ) := by
    rw [show (17165700148673751161/17170000000000000000 : ℝ)+(88796266517/68680000000000 : ℝ)*((14751/100000 : ℝ)+(11317/100000 : ℝ))=(10000866046221703/10000000000000000 : ℝ) by norm_num, show 1+(14001313418802101/50000000000000000000 : ℝ)+(4510511911568159/50000000000000000000 : ℝ)=(2500925591266518513/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14001313418802101/50000000000000000000 : ℝ) ≤ ((17165700148673751161/17170000000000000000 : ℝ)+2*(88796266517/68680000000000 : ℝ)*(14751/100000 : ℝ))^(4377/1024 : ℝ) := by
    rw [show (17165700148673751161/17170000000000000000 : ℝ)+2*(88796266517/68680000000000 : ℝ)*(14751/100000 : ℝ)=(625081876722143/625000000000000 : ℝ) by norm_num, show 1+2*(14001313418802101/50000000000000000000 : ℝ)=(25014001313418802101/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17165700148673751161/17170000000000000000 : ℝ)*(X 1 0+X 2 0)+(88796266517/68680000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4377/1024 : ℝ)) (lo := (11317/100000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (17165700148673751161/17170000000000000000 : ℝ)) (alpha := (88796266517/68680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17165700148673751161/17170000000000000000 : ℝ)*(X 0 1+X 2 1)+(88796266517/68680000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4377/1024 : ℝ)) (lo := (11317/100000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (17165700148673751161/17170000000000000000 : ℝ)) (alpha := (88796266517/68680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17165700148673751161/17170000000000000000 : ℝ)*(X 0 2+X 1 2)+(88796266517/68680000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4377/1024 : ℝ)) (lo := (11317/100000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (17165700148673751161/17170000000000000000 : ℝ)) (alpha := (88796266517/68680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1980093849/10000000000 : ℝ)*X 0 0+(1352189893/2500000000 : ℝ)*X 0 1+(81979369/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673774583/5000000000 : ℝ)*X 1 0+(-412523687/2000000000 : ℝ)*X 1 1+(5246679673/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673774573/5000000000 : ℝ)*X 2 0+(5246679693/10000000000 : ℝ)*X 2 1+(-412523687/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((430713337/1000000000 : ℝ)*X 0 0+(1033930499/2500000000 : ℝ)*X 0 1+(140154449/312500000 : ℝ)*X 0 2+(430713337/1000000000 : ℝ)*X 1 0+(1033930499/2500000000 : ℝ)*X 1 1+(140154449/312500000 : ℝ)*X 1 2+(430713337/1000000000 : ℝ)*X 2 0+(1033930499/2500000000 : ℝ)*X 2 1+(140154449/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1980105537/10000000000 : ℝ)*X 0 0+(2623631731/5000000000 : ℝ)*X 0 1+(676021563/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4307158609/10000000000 : ℝ)*X 0 0+(2241841921/5000000000 : ℝ)*X 0 1+(413698639/1000000000 : ℝ)*X 0 2+(4307158609/10000000000 : ℝ)*X 1 0+(2241841921/5000000000 : ℝ)*X 1 1+(413698639/1000000000 : ℝ)*X 1 2+(4307158609/10000000000 : ℝ)*X 2 0+(2241841921/5000000000 : ℝ)*X 2 1+(413698639/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (814026768959937463377525651/171700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (646947/80000000000 : ℝ)*(base19) + (363843647/50000000000000 : ℝ)*(base23) + (30973591/100000000000000 : ℝ)*(lower2) + (3119203/2500000000000 : ℝ)*(upper3) + (78595441/100000000000000 : ℝ)*(upper5) + (903336988143303/20000000000000 : ℝ)*(major0) + (903336988143303/20000000000000 : ℝ)*(major1) + (903336988143303/20000000000000 : ℝ)*(major2) + (308490686348583/5000000000000 : ℝ)*(sp0) + (6169831172541591/100000000000000 : ℝ)*(sp1) + (24100903334133/390625000000 : ℝ)*(sp2) + (715882276445283/25000000000000 : ℝ)*(sp3) + (9127126841/50000000000000 : ℝ)*(sp4) + (8636393783/100000000000000 : ℝ)*(sp5) + (715884435543729/25000000000000 : ℝ)*(f.failure) + (3084915990612671/50000000000000 : ℝ)*(f.sum) + (9149679523787/3434000000000000000000000000 : ℝ)*base66 + (2384608739926483/3400000000000000000000000000000 : ℝ)*base67 + (405519224873517/3400000000000000000000000000000 : ℝ)*base70 + (15814828274526483/3400000000000000000000000000000 : ℝ)*base71 + (679261015173/3434000000000000000000000000 : ℝ)*base73 + (70035893428126483/3400000000000000000000000000000 : ℝ)*base75 + (12385779007726483/3400000000000000000000000000000 : ℝ)*base77 + (26886544304073517/3400000000000000000000000000000 : ℝ)*base80 + (1177206835611/3434000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (20093901/1250000000000000000000 : ℝ)*base89 + (20093901/1250000000000000000000 : ℝ)*base91 + (20093901/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1418_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78865469/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1418_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1418_box_0 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-909315277/5000000000 : ℝ)*x 0 + (1077345527/2000000000 : ℝ)*x 1 + (5386727811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (909315277/5000000000 : ℝ)^2189 ≤ (2161569564473/20000000000000 : ℝ)^1677 := by
    have hnat : (909315277 : ℕ)^2189*20000000000000^1677 ≤ 2161569564473^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909315277 5000000000 2161569564473 20000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077345527/2000000000 : ℝ)^2189 ≤ (44596075129847/100000000000000 : ℝ)^1677 := by
    have hnat : (1077345527 : ℕ)^2189*100000000000000^1677 ≤ 44596075129847^1677*2000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077345527 2000000000 44596075129847 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386727811/10000000000 : ℝ)^2189 ≤ (44596077031787/100000000000000 : ℝ)^1677 := by
    have hnat : (5386727811 : ℕ)^2189*100000000000000^1677 ≤ 44596077031787^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386727811 10000000000 44596077031787 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-909315277/5000000000 : ℝ), (1077345527/2000000000 : ℝ), (5386727811/10000000000 : ℝ)] ![(2161569564473/20000000000000 : ℝ), (44596075129847/100000000000000 : ℝ), (44596077031787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-909315277/5000000000 : ℝ)|^2189 ≤ (2161569564473/20000000000000 : ℝ)^1677
        have hw : |(-909315277/5000000000 : ℝ)|=(909315277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077345527/2000000000 : ℝ)|^2189 ≤ (44596075129847/100000000000000 : ℝ)^1677
        have hw : |(1077345527/2000000000 : ℝ)|=(1077345527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386727811/10000000000 : ℝ)|^2189 ≤ (44596077031787/100000000000000 : ℝ)^1677
        have hw : |(5386727811/10000000000 : ℝ)|=(5386727811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_box_1 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (165186937/312500000 : ℝ)*x 0 + (-489248927/2500000000 : ℝ)*x 1 + (1346681927/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165186937/312500000 : ℝ)^2189 ≤ (43510490941177/100000000000000 : ℝ)^1677 := by
    have hnat : (165186937 : ℕ)^2189*100000000000000^1677 ≤ 43510490941177^1677*312500000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165186937 312500000 43510490941177 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (489248927/2500000000 : ℝ)^2189 ≤ (475737324609/4000000000000 : ℝ)^1677 := by
    have hnat : (489248927 : ℕ)^2189*4000000000000^1677 ≤ 475737324609^1677*2500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489248927 2500000000 475737324609 4000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346681927/2500000000 : ℝ)^2189 ≤ (69681368623/156250000000 : ℝ)^1677 := by
    have hnat : (1346681927 : ℕ)^2189*156250000000^1677 ≤ 69681368623^1677*2500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346681927 2500000000 69681368623 156250000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165186937/312500000 : ℝ), (-489248927/2500000000 : ℝ), (1346681927/2500000000 : ℝ)] ![(43510490941177/100000000000000 : ℝ), (475737324609/4000000000000 : ℝ), (69681368623/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165186937/312500000 : ℝ)|^2189 ≤ (43510490941177/100000000000000 : ℝ)^1677
        have hw : |(165186937/312500000 : ℝ)|=(165186937/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-489248927/2500000000 : ℝ)|^2189 ≤ (475737324609/4000000000000 : ℝ)^1677
        have hw : |(-489248927/2500000000 : ℝ)|=(489248927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346681927/2500000000 : ℝ)|^2189 ≤ (69681368623/156250000000 : ℝ)^1677
        have hw : |(1346681927/2500000000 : ℝ)|=(1346681927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_box_2 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5285982143/10000000000 : ℝ)*x 0 + (5386727711/10000000000 : ℝ)*x 1 + (-1956995491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285982143/10000000000 : ℝ)^2189 ≤ (10877623162383/25000000000000 : ℝ)^1677 := by
    have hnat : (5285982143 : ℕ)^2189*25000000000000^1677 ≤ 10877623162383^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285982143 10000000000 10877623162383 25000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386727711/10000000000 : ℝ)^2189 ≤ (44596075951139/100000000000000 : ℝ)^1677 := by
    have hnat : (5386727711 : ℕ)^2189*100000000000000^1677 ≤ 44596075951139^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386727711 10000000000 44596075951139 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1956995491/10000000000 : ℝ)^2189 ≤ (11893431393793/100000000000000 : ℝ)^1677 := by
    have hnat : (1956995491 : ℕ)^2189*100000000000000^1677 ≤ 11893431393793^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956995491 10000000000 11893431393793 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285982143/10000000000 : ℝ), (5386727711/10000000000 : ℝ), (-1956995491/10000000000 : ℝ)] ![(10877623162383/25000000000000 : ℝ), (44596075951139/100000000000000 : ℝ), (11893431393793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285982143/10000000000 : ℝ)|^2189 ≤ (10877623162383/25000000000000 : ℝ)^1677
        have hw : |(5285982143/10000000000 : ℝ)|=(5285982143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386727711/10000000000 : ℝ)|^2189 ≤ (44596075951139/100000000000000 : ℝ)^1677
        have hw : |(5386727711/10000000000 : ℝ)|=(5386727711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1956995491/10000000000 : ℝ)|^2189 ≤ (11893431393793/100000000000000 : ℝ)^1677
        have hw : |(-1956995491/10000000000 : ℝ)|=(1956995491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_box_3 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (890730721/2000000000 : ℝ)*x 0 + (2118801561/5000000000 : ℝ)*x 1 + (1059400797/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (890730721/2000000000 : ℝ)^2189 ≤ (17395506359467/50000000000000 : ℝ)^1677 := by
    have hnat : (890730721 : ℕ)^2189*50000000000000^1677 ≤ 17395506359467^1677*2000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890730721 2000000000 17395506359467 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2118801561/5000000000 : ℝ)^2189 ≤ (652089866107/2000000000000 : ℝ)^1677 := by
    have hnat : (2118801561 : ℕ)^2189*2000000000000^1677 ≤ 652089866107^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118801561 5000000000 652089866107 2000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059400797/2500000000 : ℝ)^2189 ≤ (32604493968197/100000000000000 : ℝ)^1677 := by
    have hnat : (1059400797 : ℕ)^2189*100000000000000^1677 ≤ 32604493968197^1677*2500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059400797 2500000000 32604493968197 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(890730721/2000000000 : ℝ), (2118801561/5000000000 : ℝ), (1059400797/2500000000 : ℝ)] ![(17395506359467/50000000000000 : ℝ), (652089866107/2000000000000 : ℝ), (32604493968197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(890730721/2000000000 : ℝ)|^2189 ≤ (17395506359467/50000000000000 : ℝ)^1677
        have hw : |(890730721/2000000000 : ℝ)|=(890730721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2118801561/5000000000 : ℝ)|^2189 ≤ (652089866107/2000000000000 : ℝ)^1677
        have hw : |(2118801561/5000000000 : ℝ)|=(2118801561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1059400797/2500000000 : ℝ)|^2189 ≤ (32604493968197/100000000000000 : ℝ)^1677
        have hw : |(1059400797/2500000000 : ℝ)|=(1059400797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_box_4 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2144289169/10000000000 : ℝ)*x 0 + (5266359181/10000000000 : ℝ)*x 1 + (5266358933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144289169/10000000000 : ℝ)^2189 ≤ (13400450969597/100000000000000 : ℝ)^1677 := by
    have hnat : (2144289169 : ℕ)^2189*100000000000000^1677 ≤ 13400450969597^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144289169 10000000000 13400450969597 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266359181/10000000000 : ℝ)^2189 ≤ (4329977584169/10000000000000 : ℝ)^1677 := by
    have hnat : (5266359181 : ℕ)^2189*10000000000000^1677 ≤ 4329977584169^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266359181 10000000000 4329977584169 10000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266358933/10000000000 : ℝ)^2189 ≤ (4329977318011/10000000000000 : ℝ)^1677 := by
    have hnat : (5266358933 : ℕ)^2189*10000000000000^1677 ≤ 4329977318011^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266358933 10000000000 4329977318011 10000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2144289169/10000000000 : ℝ), (5266359181/10000000000 : ℝ), (5266358933/10000000000 : ℝ)] ![(13400450969597/100000000000000 : ℝ), (4329977584169/10000000000000 : ℝ), (4329977318011/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2144289169/10000000000 : ℝ)|^2189 ≤ (13400450969597/100000000000000 : ℝ)^1677
        have hw : |(-2144289169/10000000000 : ℝ)|=(2144289169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266359181/10000000000 : ℝ)|^2189 ≤ (4329977584169/10000000000000 : ℝ)^1677
        have hw : |(5266359181/10000000000 : ℝ)|=(5266359181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266358933/10000000000 : ℝ)|^2189 ≤ (4329977318011/10000000000000 : ℝ)^1677
        have hw : |(5266358933/10000000000 : ℝ)|=(5266358933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_box_5 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5370259887/10000000000 : ℝ)*x 0 + (-401159261/2000000000 : ℝ)*x 1 + (5266358941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370259887/10000000000 : ℝ)^2189 ≤ (1110454995531/2500000000000 : ℝ)^1677 := by
    have hnat : (5370259887 : ℕ)^2189*2500000000000^1677 ≤ 1110454995531^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370259887 10000000000 1110454995531 2500000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401159261/2000000000 : ℝ)^2189 ≤ (76762668123/625000000000 : ℝ)^1677 := by
    have hnat : (401159261 : ℕ)^2189*625000000000^1677 ≤ 76762668123^1677*2000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401159261 2000000000 76762668123 625000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266358941/10000000000 : ℝ)^2189 ≤ (43299773265967/100000000000000 : ℝ)^1677 := by
    have hnat : (5266358941 : ℕ)^2189*100000000000000^1677 ≤ 43299773265967^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266358941 10000000000 43299773265967 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370259887/10000000000 : ℝ), (-401159261/2000000000 : ℝ), (5266358941/10000000000 : ℝ)] ![(1110454995531/2500000000000 : ℝ), (76762668123/625000000000 : ℝ), (43299773265967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370259887/10000000000 : ℝ)|^2189 ≤ (1110454995531/2500000000000 : ℝ)^1677
        have hw : |(5370259887/10000000000 : ℝ)|=(5370259887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-401159261/2000000000 : ℝ)|^2189 ≤ (76762668123/625000000000 : ℝ)^1677
        have hw : |(-401159261/2000000000 : ℝ)|=(401159261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266358941/10000000000 : ℝ)|^2189 ≤ (43299773265967/100000000000000 : ℝ)^1677
        have hw : |(5266358941/10000000000 : ℝ)|=(5266358941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_box_6 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5370259879/10000000000 : ℝ)*x 0 + (2633179679/5000000000 : ℝ)*x 1 + (-501448939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370259879/10000000000 : ℝ)^2189 ≤ (44418199734869/100000000000000 : ℝ)^1677 := by
    have hnat : (5370259879 : ℕ)^2189*100000000000000^1677 ≤ 44418199734869^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370259879 10000000000 44418199734869 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633179679/5000000000 : ℝ)^2189 ≤ (8659955548257/20000000000000 : ℝ)^1677 := by
    have hnat : (2633179679 : ℕ)^2189*20000000000000^1677 ≤ 8659955548257^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633179679 5000000000 8659955548257 20000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501448939/2500000000 : ℝ)^2189 ≤ (12282022511663/100000000000000 : ℝ)^1677 := by
    have hnat : (501448939 : ℕ)^2189*100000000000000^1677 ≤ 12282022511663^1677*2500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501448939 2500000000 12282022511663 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370259879/10000000000 : ℝ), (2633179679/5000000000 : ℝ), (-501448939/2500000000 : ℝ)] ![(44418199734869/100000000000000 : ℝ), (8659955548257/20000000000000 : ℝ), (12282022511663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370259879/10000000000 : ℝ)|^2189 ≤ (44418199734869/100000000000000 : ℝ)^1677
        have hw : |(5370259879/10000000000 : ℝ)|=(5370259879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633179679/5000000000 : ℝ)|^2189 ≤ (8659955548257/20000000000000 : ℝ)^1677
        have hw : |(2633179679/5000000000 : ℝ)|=(2633179679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-501448939/2500000000 : ℝ)|^2189 ≤ (12282022511663/100000000000000 : ℝ)^1677
        have hw : |(-501448939/2500000000 : ℝ)|=(501448939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_box_7 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4159579191/10000000000 : ℝ)*x 0 + (4384588889/10000000000 : ℝ)*x 1 + (4384589409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4159579191/10000000000 : ℝ)^2189 ≤ (31823099342983/100000000000000 : ℝ)^1677 := by
    have hnat : (4159579191 : ℕ)^2189*100000000000000^1677 ≤ 31823099342983^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159579191 10000000000 31823099342983 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4384588889/10000000000 : ℝ)^2189 ≤ (6817689537269/20000000000000 : ℝ)^1677 := by
    have hnat : (4384588889 : ℕ)^2189*20000000000000^1677 ≤ 6817689537269^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4384588889 10000000000 6817689537269 20000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4384589409/10000000000 : ℝ)^2189 ≤ (17044226481717/50000000000000 : ℝ)^1677 := by
    have hnat : (4384589409 : ℕ)^2189*50000000000000^1677 ≤ 17044226481717^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4384589409 10000000000 17044226481717 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4159579191/10000000000 : ℝ), (4384588889/10000000000 : ℝ), (4384589409/10000000000 : ℝ)] ![(31823099342983/100000000000000 : ℝ), (6817689537269/20000000000000 : ℝ), (17044226481717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4159579191/10000000000 : ℝ)|^2189 ≤ (31823099342983/100000000000000 : ℝ)^1677
        have hw : |(4159579191/10000000000 : ℝ)|=(4159579191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4384588889/10000000000 : ℝ)|^2189 ≤ (6817689537269/20000000000000 : ℝ)^1677
        have hw : |(4384588889/10000000000 : ℝ)|=(4384588889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4384589409/10000000000 : ℝ)|^2189 ≤ (17044226481717/50000000000000 : ℝ)^1677
        have hw : |(4384589409/10000000000 : ℝ)|=(4384589409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_box_8 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-259464987/1250000000 : ℝ)*x 0 + (2591575023/5000000000 : ℝ)*x 1 + (5400708489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259464987/1250000000 : ℝ)^2189 ≤ (12843858772067/100000000000000 : ℝ)^1677 := by
    have hnat : (259464987 : ℕ)^2189*100000000000000^1677 ≤ 12843858772067^1677*1250000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259464987 1250000000 12843858772067 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591575023/5000000000 : ℝ)^2189 ≤ (42408922423083/100000000000000 : ℝ)^1677 := by
    have hnat : (2591575023 : ℕ)^2189*100000000000000^1677 ≤ 42408922423083^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591575023 5000000000 42408922423083 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400708489/10000000000 : ℝ)^2189 ≤ (2796701174727/6250000000000 : ℝ)^1677 := by
    have hnat : (5400708489 : ℕ)^2189*6250000000000^1677 ≤ 2796701174727^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400708489 10000000000 2796701174727 6250000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-259464987/1250000000 : ℝ), (2591575023/5000000000 : ℝ), (5400708489/10000000000 : ℝ)] ![(12843858772067/100000000000000 : ℝ), (42408922423083/100000000000000 : ℝ), (2796701174727/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-259464987/1250000000 : ℝ)|^2189 ≤ (12843858772067/100000000000000 : ℝ)^1677
        have hw : |(-259464987/1250000000 : ℝ)|=(259464987/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591575023/5000000000 : ℝ)|^2189 ≤ (42408922423083/100000000000000 : ℝ)^1677
        have hw : |(2591575023/5000000000 : ℝ)|=(2591575023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400708489/10000000000 : ℝ)|^2189 ≤ (2796701174727/6250000000000 : ℝ)^1677
        have hw : |(5400708489/10000000000 : ℝ)|=(5400708489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_box_9 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5276189127/10000000000 : ℝ)*x 0 + (-487800069/2500000000 : ℝ)*x 1 + (5400708399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276189127/10000000000 : ℝ)^2189 ≤ (678207853433/1562500000000 : ℝ)^1677 := by
    have hnat : (5276189127 : ℕ)^2189*1562500000000^1677 ≤ 678207853433^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276189127 10000000000 678207853433 1562500000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (487800069/2500000000 : ℝ)^2189 ≤ (11847479533667/100000000000000 : ℝ)^1677 := by
    have hnat : (487800069 : ℕ)^2189*100000000000000^1677 ≤ 11847479533667^1677*2500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487800069 2500000000 11847479533667 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400708399/10000000000 : ℝ)^2189 ≤ (44747217822279/100000000000000 : ℝ)^1677 := by
    have hnat : (5400708399 : ℕ)^2189*100000000000000^1677 ≤ 44747217822279^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400708399 10000000000 44747217822279 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276189127/10000000000 : ℝ), (-487800069/2500000000 : ℝ), (5400708399/10000000000 : ℝ)] ![(678207853433/1562500000000 : ℝ), (11847479533667/100000000000000 : ℝ), (44747217822279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276189127/10000000000 : ℝ)|^2189 ≤ (678207853433/1562500000000 : ℝ)^1677
        have hw : |(5276189127/10000000000 : ℝ)|=(5276189127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-487800069/2500000000 : ℝ)|^2189 ≤ (11847479533667/100000000000000 : ℝ)^1677
        have hw : |(-487800069/2500000000 : ℝ)|=(487800069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400708399/10000000000 : ℝ)|^2189 ≤ (44747217822279/100000000000000 : ℝ)^1677
        have hw : |(5400708399/10000000000 : ℝ)|=(5400708399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_box_10 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1319047243/2500000000 : ℝ)*x 0 + (5400708537/10000000000 : ℝ)*x 1 + (-1951200299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319047243/2500000000 : ℝ)^2189 ≤ (43405300955277/100000000000000 : ℝ)^1677 := by
    have hnat : (1319047243 : ℕ)^2189*100000000000000^1677 ≤ 43405300955277^1677*2500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319047243 2500000000 43405300955277 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400708537/10000000000 : ℝ)^2189 ≤ (22373609657377/50000000000000 : ℝ)^1677 := by
    have hnat : (5400708537 : ℕ)^2189*50000000000000^1677 ≤ 22373609657377^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400708537 10000000000 22373609657377 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1951200299/10000000000 : ℝ)^2189 ≤ (5923739857979/50000000000000 : ℝ)^1677 := by
    have hnat : (1951200299 : ℕ)^2189*50000000000000^1677 ≤ 5923739857979^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951200299 10000000000 5923739857979 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319047243/2500000000 : ℝ), (5400708537/10000000000 : ℝ), (-1951200299/10000000000 : ℝ)] ![(43405300955277/100000000000000 : ℝ), (22373609657377/50000000000000 : ℝ), (5923739857979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319047243/2500000000 : ℝ)|^2189 ≤ (43405300955277/100000000000000 : ℝ)^1677
        have hw : |(1319047243/2500000000 : ℝ)|=(1319047243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400708537/10000000000 : ℝ)|^2189 ≤ (22373609657377/50000000000000 : ℝ)^1677
        have hw : |(5400708537/10000000000 : ℝ)|=(5400708537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1951200299/10000000000 : ℝ)|^2189 ≤ (5923739857979/50000000000000 : ℝ)^1677
        have hw : |(-1951200299/10000000000 : ℝ)|=(1951200299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_box_11 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (897450643/2000000000 : ℝ)*x 0 + (1055129049/2500000000 : ℝ)*x 1 + (1055129057/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (897450643/2000000000 : ℝ)^2189 ≤ (35134014656069/100000000000000 : ℝ)^1677 := by
    have hnat : (897450643 : ℕ)^2189*100000000000000^1677 ≤ 35134014656069^1677*2000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897450643 2000000000 35134014656069 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055129049/2500000000 : ℝ)^2189 ≤ (6486598500421/20000000000000 : ℝ)^1677 := by
    have hnat : (1055129049 : ℕ)^2189*20000000000000^1677 ≤ 6486598500421^1677*2500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055129049 2500000000 6486598500421 20000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055129057/2500000000 : ℝ)^2189 ≤ (3243299282309/10000000000000 : ℝ)^1677 := by
    have hnat : (1055129057 : ℕ)^2189*10000000000000^1677 ≤ 3243299282309^1677*2500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055129057 2500000000 3243299282309 10000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(897450643/2000000000 : ℝ), (1055129049/2500000000 : ℝ), (1055129057/2500000000 : ℝ)] ![(35134014656069/100000000000000 : ℝ), (6486598500421/20000000000000 : ℝ), (3243299282309/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(897450643/2000000000 : ℝ)|^2189 ≤ (35134014656069/100000000000000 : ℝ)^1677
        have hw : |(897450643/2000000000 : ℝ)|=(897450643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055129049/2500000000 : ℝ)|^2189 ≤ (6486598500421/20000000000000 : ℝ)^1677
        have hw : |(1055129049/2500000000 : ℝ)|=(1055129049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055129057/2500000000 : ℝ)|^2189 ≤ (3243299282309/10000000000000 : ℝ)^1677
        have hw : |(1055129057/2500000000 : ℝ)|=(1055129057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_box_12 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-471849699/2500000000 : ℝ)*x 0 + (1366972879/2500000000 : ℝ)*x 1 + (2627619283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (471849699/2500000000 : ℝ)^2189 ≤ (5672176276153/50000000000000 : ℝ)^1677 := by
    have hnat : (471849699 : ℕ)^2189*50000000000000^1677 ≤ 5672176276153^1677*2500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471849699 2500000000 5672176276153 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366972879/2500000000 : ℝ)^2189 ≤ (45475181525013/100000000000000 : ℝ)^1677 := by
    have hnat : (1366972879 : ℕ)^2189*100000000000000^1677 ≤ 45475181525013^1677*2500000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366972879 2500000000 45475181525013 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627619283/5000000000 : ℝ)^2189 ≤ (269877911947/625000000000 : ℝ)^1677 := by
    have hnat : (2627619283 : ℕ)^2189*625000000000^1677 ≤ 269877911947^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627619283 5000000000 269877911947 625000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-471849699/2500000000 : ℝ), (1366972879/2500000000 : ℝ), (2627619283/5000000000 : ℝ)] ![(5672176276153/50000000000000 : ℝ), (45475181525013/100000000000000 : ℝ), (269877911947/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-471849699/2500000000 : ℝ)|^2189 ≤ (5672176276153/50000000000000 : ℝ)^1677
        have hw : |(-471849699/2500000000 : ℝ)|=(471849699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366972879/2500000000 : ℝ)|^2189 ≤ (45475181525013/100000000000000 : ℝ)^1677
        have hw : |(1366972879/2500000000 : ℝ)|=(1366972879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627619283/5000000000 : ℝ)|^2189 ≤ (269877911947/625000000000 : ℝ)^1677
        have hw : |(2627619283/5000000000 : ℝ)|=(2627619283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_box_13 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5378044663/10000000000 : ℝ)*x 0 + (-2010204249/10000000000 : ℝ)*x 1 + (2627619187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378044663/10000000000 : ℝ)^2189 ≤ (8900453169961/20000000000000 : ℝ)^1677 := by
    have hnat : (5378044663 : ℕ)^2189*20000000000000^1677 ≤ 8900453169961^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378044663 10000000000 8900453169961 20000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010204249/10000000000 : ℝ)^2189 ≤ (12317270281893/100000000000000 : ℝ)^1677 := by
    have hnat : (2010204249 : ℕ)^2189*100000000000000^1677 ≤ 12317270281893^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010204249 10000000000 12317270281893 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627619187/5000000000 : ℝ)^2189 ≤ (43180463852271/100000000000000 : ℝ)^1677 := by
    have hnat : (2627619187 : ℕ)^2189*100000000000000^1677 ≤ 43180463852271^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627619187 5000000000 43180463852271 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378044663/10000000000 : ℝ), (-2010204249/10000000000 : ℝ), (2627619187/5000000000 : ℝ)] ![(8900453169961/20000000000000 : ℝ), (12317270281893/100000000000000 : ℝ), (43180463852271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378044663/10000000000 : ℝ)|^2189 ≤ (8900453169961/20000000000000 : ℝ)^1677
        have hw : |(5378044663/10000000000 : ℝ)|=(5378044663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2010204249/10000000000 : ℝ)|^2189 ≤ (12317270281893/100000000000000 : ℝ)^1677
        have hw : |(-2010204249/10000000000 : ℝ)|=(2010204249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627619187/5000000000 : ℝ)|^2189 ≤ (43180463852271/100000000000000 : ℝ)^1677
        have hw : |(2627619187/5000000000 : ℝ)|=(2627619187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_box_14 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5378044417/10000000000 : ℝ)*x 0 + (131380961/250000000 : ℝ)*x 1 + (-2010204493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378044417/10000000000 : ℝ)^2189 ≤ (556278289909/1250000000000 : ℝ)^1677 := by
    have hnat : (5378044417 : ℕ)^2189*1250000000000^1677 ≤ 556278289909^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378044417 10000000000 556278289909 1250000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131380961/250000000 : ℝ)^2189 ≤ (21590232280069/50000000000000 : ℝ)^1677 := by
    have hnat : (131380961 : ℕ)^2189*50000000000000^1677 ≤ 21590232280069^1677*250000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131380961 250000000 21590232280069 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2010204493/10000000000 : ℝ)^2189 ≤ (1231727223343/10000000000000 : ℝ)^1677 := by
    have hnat : (2010204493 : ℕ)^2189*10000000000000^1677 ≤ 1231727223343^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010204493 10000000000 1231727223343 10000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378044417/10000000000 : ℝ), (131380961/250000000 : ℝ), (-2010204493/10000000000 : ℝ)] ![(556278289909/1250000000000 : ℝ), (21590232280069/50000000000000 : ℝ), (1231727223343/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378044417/10000000000 : ℝ)|^2189 ≤ (556278289909/1250000000000 : ℝ)^1677
        have hw : |(5378044417/10000000000 : ℝ)|=(5378044417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131380961/250000000 : ℝ)|^2189 ≤ (21590232280069/50000000000000 : ℝ)^1677
        have hw : |(131380961/250000000 : ℝ)|=(131380961/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2010204493/10000000000 : ℝ)|^2189 ≤ (1231727223343/10000000000000 : ℝ)^1677
        have hw : |(-2010204493/10000000000 : ℝ)|=(2010204493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1418_box_15 (p : ℝ) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4131961237/10000000000 : ℝ)*x 0 + (4398158219/10000000000 : ℝ)*x 1 + (2199078487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4131961237/10000000000 : ℝ)^2189 ≤ (31547577399719/100000000000000 : ℝ)^1677 := by
    have hnat : (4131961237 : ℕ)^2189*100000000000000^1677 ≤ 31547577399719^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131961237 10000000000 31547577399719 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4398158219/10000000000 : ℝ)^2189 ≤ (17113108806517/50000000000000 : ℝ)^1677 := by
    have hnat : (4398158219 : ℕ)^2189*50000000000000^1677 ≤ 17113108806517^1677*10000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4398158219 10000000000 17113108806517 50000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2199078487/5000000000 : ℝ)^2189 ≤ (34226204966541/100000000000000 : ℝ)^1677 := by
    have hnat : (2199078487 : ℕ)^2189*100000000000000^1677 ≤ 34226204966541^1677*5000000000^2189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199078487 5000000000 34226204966541 100000000000000 2189 1677 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2189/512 : ℝ)) 2189 1677 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4131961237/10000000000 : ℝ), (4398158219/10000000000 : ℝ), (2199078487/5000000000 : ℝ)] ![(31547577399719/100000000000000 : ℝ), (17113108806517/50000000000000 : ℝ), (34226204966541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4131961237/10000000000 : ℝ)|^2189 ≤ (31547577399719/100000000000000 : ℝ)^1677
        have hw : |(4131961237/10000000000 : ℝ)|=(4131961237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4398158219/10000000000 : ℝ)|^2189 ≤ (17113108806517/50000000000000 : ℝ)^1677
        have hw : |(4398158219/10000000000 : ℝ)|=(4398158219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2199078487/5000000000 : ℝ)|^2189 ≤ (34226204966541/100000000000000 : ℝ)^1677
        have hw : |(2199078487/5000000000 : ℝ)|=(2199078487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1418_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78865469/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62893/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59091/100000 : ℝ) ∧ (20097/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84643/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14751/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5659/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5659/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5659/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5659/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5659/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5659/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5659/50000 : ℝ) ^ (4377/1024 : ℝ) ≤ (9024431543362343/100000000000000000000 : ℝ) := by
    have hpowers : (5659/50000 : ℝ)^4377 ≤ (9024431543362343/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5659 : ℕ)^4377*100000000000000000000^1024 ≤ 9024431543362343^1024*50000^4377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5659 50000 9024431543362343 100000000000000000000 4377 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5659/50000 : ℝ)) (X := (9024431543362343/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14751/100000 : ℝ) ^ (4377/1024 : ℝ) ≤ (14001313418802101/50000000000000000000 : ℝ) := by
    have hpowers : (14751/100000 : ℝ)^4377 ≤ (14001313418802101/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14751 : ℕ)^4377*50000000000000000000^1024 ≤ 14001313418802101^1024*100000^4377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14751 100000 14001313418802101 50000000000000000000 4377 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14751/100000 : ℝ)) (X := (14001313418802101/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009024431543362343/50000000000000000000 : ℝ) ≤ (5000211112157221/5000000000000000 : ℝ) ^ (4377/1024 : ℝ) := by
    have hpowers : (50009024431543362343/50000000000000000000 : ℝ)^1024 ≤ (5000211112157221/5000000000000000 : ℝ)^4377 := by
      have hnat : (50009024431543362343 : ℕ)^1024*5000000000000000^4377 ≤ 5000211112157221^4377*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009024431543362343 50000000000000000000 5000211112157221 5000000000000000 1024 4377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000211112157221/5000000000000000 : ℝ)) (X := (50009024431543362343/50000000000000000000 : ℝ)) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007405411676193309/20000000000000000000 : ℝ) ≤ (10000866125922779/10000000000000000 : ℝ) ^ (4377/1024 : ℝ) := by
    have hpowers : (20007405411676193309/20000000000000000000 : ℝ)^1024 ≤ (10000866125922779/10000000000000000 : ℝ)^4377 := by
      have hnat : (20007405411676193309 : ℕ)^1024*10000000000000000^4377 ≤ 10000866125922779^4377*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007405411676193309 20000000000000000000 10000866125922779 10000000000000000 1024 4377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000866125922779/10000000000000000 : ℝ)) (X := (20007405411676193309/20000000000000000000 : ℝ)) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014001313418802101/25000000000000000000 : ℝ) ≤ (2500327506882779/2500000000000000 : ℝ) ^ (4377/1024 : ℝ) := by
    have hpowers : (25014001313418802101/25000000000000000000 : ℝ)^1024 ≤ (2500327506882779/2500000000000000 : ℝ)^4377 := by
      have hnat : (25014001313418802101 : ℕ)^1024*2500000000000000^4377 ≤ 2500327506882779^4377*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014001313418802101 25000000000000000000 2500327506882779 2500000000000000 1024 4377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500327506882779/2500000000000000 : ℝ)) (X := (25014001313418802101/25000000000000000000 : ℝ)) (by norm_num) 4377 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9024431543362343/100000000000000000000 : ℝ) ≤ ((17160700669632581527/17165000000000000000 : ℝ)+2*(443901608337/343300000000000 : ℝ)*(5659/50000 : ℝ))^(4377/1024 : ℝ) := by
    rw [show (17160700669632581527/17165000000000000000 : ℝ)+2*(443901608337/343300000000000 : ℝ)*(5659/50000 : ℝ)=(5000211112157221/5000000000000000 : ℝ) by norm_num, show 1+2*(9024431543362343/100000000000000000000 : ℝ)=(50009024431543362343/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14001313418802101/50000000000000000000 : ℝ)+(9024431543362343/100000000000000000000 : ℝ) ≤ ((17160700669632581527/17165000000000000000 : ℝ)+(443901608337/343300000000000 : ℝ)*((14751/100000 : ℝ)+(5659/50000 : ℝ)))^(4377/1024 : ℝ) := by
    rw [show (17160700669632581527/17165000000000000000 : ℝ)+(443901608337/343300000000000 : ℝ)*((14751/100000 : ℝ)+(5659/50000 : ℝ))=(10000866125922779/10000000000000000 : ℝ) by norm_num, show 1+(14001313418802101/50000000000000000000 : ℝ)+(9024431543362343/100000000000000000000 : ℝ)=(20007405411676193309/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14001313418802101/50000000000000000000 : ℝ) ≤ ((17160700669632581527/17165000000000000000 : ℝ)+2*(443901608337/343300000000000 : ℝ)*(14751/100000 : ℝ))^(4377/1024 : ℝ) := by
    rw [show (17160700669632581527/17165000000000000000 : ℝ)+2*(443901608337/343300000000000 : ℝ)*(14751/100000 : ℝ)=(2500327506882779/2500000000000000 : ℝ) by norm_num, show 1+2*(14001313418802101/50000000000000000000 : ℝ)=(25014001313418802101/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17160700669632581527/17165000000000000000 : ℝ)*(X 1 0+X 2 0)+(443901608337/343300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4377/1024 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (17160700669632581527/17165000000000000000 : ℝ)) (alpha := (443901608337/343300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17160700669632581527/17165000000000000000 : ℝ)*(X 0 1+X 2 1)+(443901608337/343300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4377/1024 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (17160700669632581527/17165000000000000000 : ℝ)) (alpha := (443901608337/343300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17160700669632581527/17165000000000000000 : ℝ)*(X 0 2+X 1 2)+(443901608337/343300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4377/1024 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (17160700669632581527/17165000000000000000 : ℝ)) (alpha := (443901608337/343300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-909315277/5000000000 : ℝ)*X 0 0+(1077345527/2000000000 : ℝ)*X 0 1+(5386727811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((165186937/312500000 : ℝ)*X 1 0+(-489248927/2500000000 : ℝ)*X 1 1+(1346681927/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285982143/10000000000 : ℝ)*X 2 0+(5386727711/10000000000 : ℝ)*X 2 1+(-1956995491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((890730721/2000000000 : ℝ)*X 0 0+(2118801561/5000000000 : ℝ)*X 0 1+(1059400797/2500000000 : ℝ)*X 0 2+(890730721/2000000000 : ℝ)*X 1 0+(2118801561/5000000000 : ℝ)*X 1 1+(1059400797/2500000000 : ℝ)*X 1 2+(890730721/2000000000 : ℝ)*X 2 0+(2118801561/5000000000 : ℝ)*X 2 1+(1059400797/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2144289169/10000000000 : ℝ)*X 0 0+(5266359181/10000000000 : ℝ)*X 0 1+(5266358933/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5370259887/10000000000 : ℝ)*X 1 0+(-401159261/2000000000 : ℝ)*X 1 1+(5266358941/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5370259879/10000000000 : ℝ)*X 2 0+(2633179679/5000000000 : ℝ)*X 2 1+(-501448939/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4159579191/10000000000 : ℝ)*X 0 0+(4384588889/10000000000 : ℝ)*X 0 1+(4384589409/10000000000 : ℝ)*X 0 2+(4159579191/10000000000 : ℝ)*X 1 0+(4384588889/10000000000 : ℝ)*X 1 1+(4384589409/10000000000 : ℝ)*X 1 2+(4159579191/10000000000 : ℝ)*X 2 0+(4384588889/10000000000 : ℝ)*X 2 1+(4384589409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-259464987/1250000000 : ℝ)*X 0 0+(2591575023/5000000000 : ℝ)*X 0 1+(5400708489/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276189127/10000000000 : ℝ)*X 1 0+(-487800069/2500000000 : ℝ)*X 1 1+(5400708399/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1319047243/2500000000 : ℝ)*X 2 0+(5400708537/10000000000 : ℝ)*X 2 1+(-1951200299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((897450643/2000000000 : ℝ)*X 0 0+(1055129049/2500000000 : ℝ)*X 0 1+(1055129057/2500000000 : ℝ)*X 0 2+(897450643/2000000000 : ℝ)*X 1 0+(1055129049/2500000000 : ℝ)*X 1 1+(1055129057/2500000000 : ℝ)*X 1 2+(897450643/2000000000 : ℝ)*X 2 0+(1055129049/2500000000 : ℝ)*X 2 1+(1055129057/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-471849699/2500000000 : ℝ)*X 0 0+(1366972879/2500000000 : ℝ)*X 0 1+(2627619283/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5378044663/10000000000 : ℝ)*X 1 0+(-2010204249/10000000000 : ℝ)*X 1 1+(2627619187/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5378044417/10000000000 : ℝ)*X 2 0+(131380961/250000000 : ℝ)*X 2 1+(-2010204493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4131961237/10000000000 : ℝ)*X 0 0+(4398158219/10000000000 : ℝ)*X 0 1+(2199078487/5000000000 : ℝ)*X 0 2+(4131961237/10000000000 : ℝ)*X 1 0+(4398158219/10000000000 : ℝ)*X 1 1+(2199078487/5000000000 : ℝ)*X 1 2+(4131961237/10000000000 : ℝ)*X 2 0+(4398158219/10000000000 : ℝ)*X 2 1+(2199078487/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1418_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62893/100000 : ℝ) ≤ (-10795119995089573476264961479/17165000000000000000000000000 : ℝ) := by norm_num
    linear_combination (120588319/100000000000000 : ℝ)*(upper0) + (7748203/25000000000000 : ℝ)*(lower1) + (173470413/100000000000000 : ℝ)*(lower2) + (73689023/100000000000000 : ℝ)*(lower3) + (187798368515319/6250000000000 : ℝ)*(major0) + (187798368515319/6250000000000 : ℝ)*(major1) + (187798368515319/6250000000000 : ℝ)*(major2) + (1561197347/100000000000000 : ℝ)*(sp1) + (4125506703095253/100000000000000 : ℝ)*(sp4) + (2062754982142663/50000000000000 : ℝ)*(sp5) + (1031325337026201/25000000000000 : ℝ)*(sp6) + (380999940068207/20000000000000 : ℝ)*(sp7) + (4822387419/100000000000000 : ℝ)*(sp8) + (52544344467/25000000000000 : ℝ)*(sp14) + (380999940068207/20000000000000 : ℝ)*(f.failure) + (257844470342667/6250000000000 : ℝ)*(f.sum) + (3222046354559/536406250000000000000000000 : ℝ)*base65 + (73480588177875387/107281250000000000000000000000000 : ℝ)*base68 + (134131407009406637/107281250000000000000000000000000 : ℝ)*base70 + (141627103011843363/107281250000000000000000000000000 : ℝ)*base71 + (105062256067437/17165000000000000000000000000 : ℝ)*base74 + (19318811479155863/107281250000000000000000000000000 : ℝ)*base75 + (597142532891655863/107281250000000000000000000000000 : ℝ)*base77 + (3405127988103031637/107281250000000000000000000000000 : ℝ)*base80 + (88300223474493/17165000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2955917/1000000000000000000000 : ℝ)*base90 + (2955917/1000000000000000000000 : ℝ)*base92 + (2955917/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59091/100000 : ℝ) ≤ (253585338974488024760313227010843/429125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36486727/100000000000000 : ℝ)*(upper0) + (32447243/100000000000000 : ℝ)*(lower3) + (49157517/50000000000000 : ℝ)*(upper4) + (8132867/50000000000000 : ℝ)*(upper5) + (1538006173300897/50000000000000 : ℝ)*(major0) + (1538006173300897/50000000000000 : ℝ)*(major1) + (1538006173300897/50000000000000 : ℝ)*(major2) + (418216178484609/10000000000000 : ℝ)*(sp0) + (4182162593203607/100000000000000 : ℝ)*(sp1) + (4182158817752309/100000000000000 : ℝ)*(sp2) + (15235642248229/781250000000 : ℝ)*(sp3) + (1887725649/50000000000000 : ℝ)*(sp6) + (2031154751/100000000000000 : ℝ)*(sp11) + (808357517/100000000000000 : ℝ)*(sp12) + (975082119464031/50000000000000 : ℝ)*(f.failure) + (4182162593203607/100000000000000 : ℝ)*(f.sum) + (108590607941867/17165000000000000000000000000 : ℝ)*base66 + (897608753732320281/858250000000000000000000000000000 : ℝ)*base68 + (13097035216527179719/858250000000000000000000000000000 : ℝ)*base69 + (3978598414686929719/858250000000000000000000000000000 : ℝ)*base71 + (98015654707291/8582500000000000000000000000 : ℝ)*base74 + (10951038470689179719/858250000000000000000000000000000 : ℝ)*base75 + (3898716932398679719/858250000000000000000000000000000 : ℝ)*base77 + (207797577885570281/858250000000000000000000000000000 : ℝ)*base80 + (17484058352127/17165000000000000000000000000 : ℝ)*base82 + (16554461/2500000000000000000000 : ℝ)*base90 + (16554461/2500000000000000000000 : ℝ)*base92 + (16554461/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (20097/25000 : ℝ) ≤ (13798967330932391459714276973/17165000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37367377/100000000000000 : ℝ)*(upper2) + (11594369/50000000000000 : ℝ)*(lower3) + (23470843/50000000000000 : ℝ)*(lower5) + (3384505461695263/100000000000000 : ℝ)*(major0) + (3384505461695263/100000000000000 : ℝ)*(major1) + (3384505461695263/100000000000000 : ℝ)*(major2) + (1670950259/100000000000000 : ℝ)*(sp0) + (8648342411/25000000000000 : ℝ)*(sp2) + (18472618039/100000000000000 : ℝ)*(sp3) + (4596465343362463/100000000000000 : ℝ)*(sp8) + (2298234051714713/50000000000000 : ℝ)*(sp9) + (2298216755029891/50000000000000 : ℝ)*(sp10) + (1072863817199121/50000000000000 : ℝ)*(sp11) + (34034897/3125000000000 : ℝ)*(sp12) + (2145746107016281/100000000000000 : ℝ)*(f.failure) + (2298234051714713/50000000000000 : ℝ)*(f.sum) + (593677963061/1072812500000000000000000000 : ℝ)*base65 + (2014897159121743399/1716500000000000000000000000000000 : ℝ)*base68 + (1628561433303243399/1716500000000000000000000000000000 : ℝ)*base70 + (9908906535463256601/1716500000000000000000000000000000 : ℝ)*base71 + (92894852626679/17165000000000000000000000000 : ℝ)*base74 + (13330150647505756601/1716500000000000000000000000000000 : ℝ)*base75 + (12726815764112256601/1716500000000000000000000000000000 : ℝ)*base77 + (1559080225373243399/1716500000000000000000000000000000 : ℝ)*base80 + (60293468919559/17165000000000000000000000000 : ℝ)*base82 + (41700789/5000000000000000000000 : ℝ)*base89 + (41700789/5000000000000000000000 : ℝ)*base91 + (41700789/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84643/100000 : ℝ) ≤ (-181607723167168765587151690618401/214562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (267736519/100000000000000 : ℝ)*(lower0) + (59150541/50000000000000 : ℝ)*(upper3) + (113505393/100000000000000 : ℝ)*(lower4) + (1710927335473721/50000000000000 : ℝ)*(major0) + (1710927335473721/50000000000000 : ℝ)*(major1) + (1710927335473721/50000000000000 : ℝ)*(major2) + (2935399837/50000000000000 : ℝ)*(sp0) + (256986663411/100000000000000 : ℝ)*(sp5) + (254199166591/100000000000000 : ℝ)*(sp6) + (30227459073/100000000000000 : ℝ)*(sp7) + (4702491948041107/100000000000000 : ℝ)*(sp12) + (470224083217737/10000000000000 : ℝ)*(sp13) + (470224361967419/10000000000000 : ℝ)*(sp14) + (216939494323727/10000000000000 : ℝ)*(sp15) + (2169425170696343/100000000000000 : ℝ)*(f.failure) + (4702497818840781/100000000000000 : ℝ)*(f.sum) + (29400848731271/17165000000000000000000000000 : ℝ)*base66 + (2232602102508151967/858250000000000000000000000000000 : ℝ)*base67 + (5440018825109848033/858250000000000000000000000000000 : ℝ)*base70 + (5195433380947401967/858250000000000000000000000000000 : ℝ)*base71 + (17501213980131/4291250000000000000000000000 : ℝ)*base73 + (2566991975011401967/858250000000000000000000000000000 : ℝ)*base75 + (1495321218718401967/858250000000000000000000000000000 : ℝ)*base77 + (1710500325856151967/858250000000000000000000000000000 : ℝ)*base79 + (36547479419261/17165000000000000000000000000 : ℝ)*base82 + (47279867/5000000000000000000000 : ℝ)*base89 + (47279867/5000000000000000000000 : ℝ)*base91 + (47279867/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1418_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78865469/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62893/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59091/100000 : ℝ) else (20097/25000 : ℝ) ≤ X j i ∧ X j i ≤ (84643/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1418_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1418_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78865469/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62893/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59091/100000 : ℝ) else (20097/25000 : ℝ) ≤ X j i ∧ X j i ≤ (84643/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1418_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1418_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1418_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4377/1024 : ℝ) ≤ p) (hpb : p ≤ (2189/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78865469/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62893/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59091/100000 : ℝ) else (20097/25000 : ℝ) ≤ X j i ∧ X j i ≤ (84643/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1418_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

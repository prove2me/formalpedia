-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1579_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:29:53.061537+00:00
-- url     : https://prove2.me/submissions/7a92be01-b2af-48f8-a2e7-8df2dcaf4985

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
theorem support_rectangle_w1579_s0_0 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-404255049/2500000000 : ℝ)*x 0 + (1465767929/2500000000 : ℝ)*x 1 + (2441471767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404255049/2500000000 : ℝ)^4655 ≤ (9672986011711/100000000000000 : ℝ)^3631 := by
    have hnat : (404255049 : ℕ)^4655*100000000000000^3631 ≤ 9672986011711^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404255049 2500000000 9672986011711 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1465767929/2500000000 : ℝ)^4655 ≤ (25217545616729/50000000000000 : ℝ)^3631 := by
    have hnat : (1465767929 : ℕ)^4655*50000000000000^3631 ≤ 25217545616729^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1465767929 2500000000 25217545616729 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2441471767/5000000000 : ℝ)^4655 ≤ (3989192274509/10000000000000 : ℝ)^3631 := by
    have hnat : (2441471767 : ℕ)^4655*10000000000000^3631 ≤ 3989192274509^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2441471767 5000000000 3989192274509 10000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-404255049/2500000000 : ℝ), (1465767929/2500000000 : ℝ), (2441471767/5000000000 : ℝ)] ![(9672986011711/100000000000000 : ℝ), (25217545616729/50000000000000 : ℝ), (3989192274509/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-404255049/2500000000 : ℝ)|^4655 ≤ (9672986011711/100000000000000 : ℝ)^3631
        have hw : |(-404255049/2500000000 : ℝ)|=(404255049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1465767929/2500000000 : ℝ)|^4655 ≤ (25217545616729/50000000000000 : ℝ)^3631
        have hw : |(1465767929/2500000000 : ℝ)|=(1465767929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2441471767/5000000000 : ℝ)|^4655 ≤ (3989192274509/10000000000000 : ℝ)^3631
        have hw : |(2441471767/5000000000 : ℝ)|=(2441471767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s0_1 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1365890469/2500000000 : ℝ)*x 0 + (-5404633/25000000 : ℝ)*x 1 + (4882943509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1365890469/2500000000 : ℝ)^4655 ≤ (46072297159017/100000000000000 : ℝ)^3631 := by
    have hnat : (1365890469 : ℕ)^4655*100000000000000^3631 ≤ 46072297159017^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365890469 2500000000 46072297159017 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404633/25000000 : ℝ)^4655 ≤ (7017890174753/50000000000000 : ℝ)^3631 := by
    have hnat : (5404633 : ℕ)^4655*50000000000000^3631 ≤ 7017890174753^3631*25000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404633 25000000 7017890174753 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4882943509/10000000000 : ℝ)^4655 ≤ (39891922483249/100000000000000 : ℝ)^3631 := by
    have hnat : (4882943509 : ℕ)^4655*100000000000000^3631 ≤ 39891922483249^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4882943509 10000000000 39891922483249 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1365890469/2500000000 : ℝ), (-5404633/25000000 : ℝ), (4882943509/10000000000 : ℝ)] ![(46072297159017/100000000000000 : ℝ), (7017890174753/50000000000000 : ℝ), (39891922483249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1365890469/2500000000 : ℝ)|^4655 ≤ (46072297159017/100000000000000 : ℝ)^3631
        have hw : |(1365890469/2500000000 : ℝ)|=(1365890469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5404633/25000000 : ℝ)|^4655 ≤ (7017890174753/50000000000000 : ℝ)^3631
        have hw : |(-5404633/25000000 : ℝ)|=(5404633/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4882943509/10000000000 : ℝ)|^4655 ≤ (39891922483249/100000000000000 : ℝ)^3631
        have hw : |(4882943509/10000000000 : ℝ)|=(4882943509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s0_2 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5463561941/10000000000 : ℝ)*x 0 + (4882943421/10000000000 : ℝ)*x 1 + (-1080926613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5463561941/10000000000 : ℝ)^4655 ≤ (23036148930859/50000000000000 : ℝ)^3631 := by
    have hnat : (5463561941 : ℕ)^4655*50000000000000^3631 ≤ 23036148930859^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463561941 10000000000 23036148930859 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4882943421/10000000000 : ℝ)^4655 ≤ (39891921561571/100000000000000 : ℝ)^3631 := by
    have hnat : (4882943421 : ℕ)^4655*100000000000000^3631 ≤ 39891921561571^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4882943421 10000000000 39891921561571 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080926613/5000000000 : ℝ)^4655 ≤ (3508945141479/25000000000000 : ℝ)^3631 := by
    have hnat : (1080926613 : ℕ)^4655*25000000000000^3631 ≤ 3508945141479^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080926613 5000000000 3508945141479 25000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5463561941/10000000000 : ℝ), (4882943421/10000000000 : ℝ), (-1080926613/5000000000 : ℝ)] ![(23036148930859/50000000000000 : ℝ), (39891921561571/100000000000000 : ℝ), (3508945141479/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5463561941/10000000000 : ℝ)|^4655 ≤ (23036148930859/50000000000000 : ℝ)^3631
        have hw : |(5463561941/10000000000 : ℝ)|=(5463561941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4882943421/10000000000 : ℝ)|^4655 ≤ (39891921561571/100000000000000 : ℝ)^3631
        have hw : |(4882943421/10000000000 : ℝ)|=(4882943421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1080926613/5000000000 : ℝ)|^4655 ≤ (3508945141479/25000000000000 : ℝ)^3631
        have hw : |(-1080926613/5000000000 : ℝ)|=(1080926613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s0_3 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (825507163/2000000000 : ℝ)*x 0 + (309369163/1000000000 : ℝ)*x 1 + (169423031/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (825507163/2000000000 : ℝ)^4655 ≤ (32159518027273/100000000000000 : ℝ)^3631 := by
    have hnat : (825507163 : ℕ)^4655*100000000000000^3631 ≤ 32159518027273^3631*2000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825507163 2000000000 32159518027273 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (309369163/1000000000 : ℝ)^4655 ≤ (2777751666031/12500000000000 : ℝ)^3631 := by
    have hnat : (309369163 : ℕ)^4655*12500000000000^3631 ≤ 2777751666031^3631*1000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309369163 1000000000 2777751666031 12500000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169423031/312500000 : ℝ)^4655 ≤ (22809234315269/50000000000000 : ℝ)^3631 := by
    have hnat : (169423031 : ℕ)^4655*50000000000000^3631 ≤ 22809234315269^3631*312500000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169423031 312500000 22809234315269 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(825507163/2000000000 : ℝ), (309369163/1000000000 : ℝ), (169423031/312500000 : ℝ)] ![(32159518027273/100000000000000 : ℝ), (2777751666031/12500000000000 : ℝ), (22809234315269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(825507163/2000000000 : ℝ)|^4655 ≤ (32159518027273/100000000000000 : ℝ)^3631
        have hw : |(825507163/2000000000 : ℝ)|=(825507163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(309369163/1000000000 : ℝ)|^4655 ≤ (2777751666031/12500000000000 : ℝ)^3631
        have hw : |(309369163/1000000000 : ℝ)|=(309369163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169423031/312500000 : ℝ)|^4655 ≤ (22809234315269/50000000000000 : ℝ)^3631
        have hw : |(169423031/312500000 : ℝ)|=(169423031/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s0_4 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1620008809/10000000000 : ℝ)*x 0 + (1226898233/2500000000 : ℝ)*x 1 + (233502021/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1620008809/10000000000 : ℝ)^4655 ≤ (605994477847/6250000000000 : ℝ)^3631 := by
    have hnat : (1620008809 : ℕ)^4655*6250000000000^3631 ≤ 605994477847^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1620008809 10000000000 605994477847 6250000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1226898233/2500000000 : ℝ)^4655 ≤ (2509392165939/6250000000000 : ℝ)^3631 := by
    have hnat : (1226898233 : ℕ)^4655*6250000000000^3631 ≤ 2509392165939^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1226898233 2500000000 2509392165939 6250000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (233502021/400000000 : ℝ)^4655 ≤ (6269226711863/12500000000000 : ℝ)^3631 := by
    have hnat : (233502021 : ℕ)^4655*12500000000000^3631 ≤ 6269226711863^3631*400000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233502021 400000000 6269226711863 12500000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1620008809/10000000000 : ℝ), (1226898233/2500000000 : ℝ), (233502021/400000000 : ℝ)] ![(605994477847/6250000000000 : ℝ), (2509392165939/6250000000000 : ℝ), (6269226711863/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1620008809/10000000000 : ℝ)|^4655 ≤ (605994477847/6250000000000 : ℝ)^3631
        have hw : |(-1620008809/10000000000 : ℝ)|=(1620008809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1226898233/2500000000 : ℝ)|^4655 ≤ (2509392165939/6250000000000 : ℝ)^3631
        have hw : |(1226898233/2500000000 : ℝ)|=(1226898233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(233502021/400000000 : ℝ)|^4655 ≤ (6269226711863/12500000000000 : ℝ)^3631
        have hw : |(233502021/400000000 : ℝ)|=(233502021/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s0_5 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195608987/10000000000 : ℝ)*x 0 + (-9657973/80000000 : ℝ)*x 1 + (291877517/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195608987/10000000000 : ℝ)^4655 ≤ (43195787755191/100000000000000 : ℝ)^3631 := by
    have hnat : (5195608987 : ℕ)^4655*100000000000000^3631 ≤ 43195787755191^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195608987 10000000000 43195787755191 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9657973/80000000 : ℝ)^4655 ≤ (6650400573599/100000000000000 : ℝ)^3631 := by
    have hnat : (9657973 : ℕ)^4655*100000000000000^3631 ≤ 6650400573599^3631*80000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9657973 80000000 6650400573599 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (291877517/500000000 : ℝ)^4655 ≤ (12538452914303/25000000000000 : ℝ)^3631 := by
    have hnat : (291877517 : ℕ)^4655*25000000000000^3631 ≤ 12538452914303^3631*500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291877517 500000000 12538452914303 25000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195608987/10000000000 : ℝ), (-9657973/80000000 : ℝ), (291877517/500000000 : ℝ)] ![(43195787755191/100000000000000 : ℝ), (6650400573599/100000000000000 : ℝ), (12538452914303/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195608987/10000000000 : ℝ)|^4655 ≤ (43195787755191/100000000000000 : ℝ)^3631
        have hw : |(5195608987/10000000000 : ℝ)|=(5195608987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9657973/80000000 : ℝ)|^4655 ≤ (6650400573599/100000000000000 : ℝ)^3631
        have hw : |(-9657973/80000000 : ℝ)|=(9657973/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(291877517/500000000 : ℝ)|^4655 ≤ (12538452914303/25000000000000 : ℝ)^3631
        have hw : |(291877517/500000000 : ℝ)|=(291877517/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s0_6 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597803891/5000000000 : ℝ)*x 0 + (1167510339/2000000000 : ℝ)*x 1 + (-301811583/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597803891/5000000000 : ℝ)^4655 ≤ (43195774911631/100000000000000 : ℝ)^3631 := by
    have hnat : (2597803891 : ℕ)^4655*100000000000000^3631 ≤ 43195774911631^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597803891 5000000000 43195774911631 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1167510339/2000000000 : ℝ)^4655 ≤ (50153826581927/100000000000000 : ℝ)^3631 := by
    have hnat : (1167510339 : ℕ)^4655*100000000000000^3631 ≤ 50153826581927^3631*2000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167510339 2000000000 50153826581927 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (301811583/2500000000 : ℝ)^4655 ≤ (6650398504349/100000000000000 : ℝ)^3631 := by
    have hnat : (301811583 : ℕ)^4655*100000000000000^3631 ≤ 6650398504349^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301811583 2500000000 6650398504349 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597803891/5000000000 : ℝ), (1167510339/2000000000 : ℝ), (-301811583/2500000000 : ℝ)] ![(43195774911631/100000000000000 : ℝ), (50153826581927/100000000000000 : ℝ), (6650398504349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597803891/5000000000 : ℝ)|^4655 ≤ (43195774911631/100000000000000 : ℝ)^3631
        have hw : |(2597803891/5000000000 : ℝ)|=(2597803891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1167510339/2000000000 : ℝ)|^4655 ≤ (50153826581927/100000000000000 : ℝ)^3631
        have hw : |(1167510339/2000000000 : ℝ)|=(1167510339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-301811583/2500000000 : ℝ)|^4655 ≤ (6650398504349/100000000000000 : ℝ)^3631
        have hw : |(-301811583/2500000000 : ℝ)|=(301811583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s0_7 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4134631527/10000000000 : ℝ)*x 0 + (2681494867/5000000000 : ℝ)*x 1 + (98572029/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4134631527/10000000000 : ℝ)^4655 ≤ (16115206326851/50000000000000 : ℝ)^3631 := by
    have hnat : (4134631527 : ℕ)^4655*50000000000000^3631 ≤ 16115206326851^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134631527 10000000000 16115206326851 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2681494867/5000000000 : ℝ)^4655 ≤ (899757350467/2000000000000 : ℝ)^3631 := by
    have hnat : (2681494867 : ℕ)^4655*2000000000000^3631 ≤ 899757350467^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681494867 5000000000 899757350467 2000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (98572029/312500000 : ℝ)^4655 ≤ (22781719817583/100000000000000 : ℝ)^3631 := by
    have hnat : (98572029 : ℕ)^4655*100000000000000^3631 ≤ 22781719817583^3631*312500000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98572029 312500000 22781719817583 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4134631527/10000000000 : ℝ), (2681494867/5000000000 : ℝ), (98572029/312500000 : ℝ)] ![(16115206326851/50000000000000 : ℝ), (899757350467/2000000000000 : ℝ), (22781719817583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4134631527/10000000000 : ℝ)|^4655 ≤ (16115206326851/50000000000000 : ℝ)^3631
        have hw : |(4134631527/10000000000 : ℝ)|=(4134631527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2681494867/5000000000 : ℝ)|^4655 ≤ (899757350467/2000000000000 : ℝ)^3631
        have hw : |(2681494867/5000000000 : ℝ)|=(2681494867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(98572029/312500000 : ℝ)|^4655 ≤ (22781719817583/100000000000000 : ℝ)^3631
        have hw : |(98572029/312500000 : ℝ)|=(98572029/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1579_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168752083/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (73/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4929/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4653/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4653 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4653*1^1024 ≤ 0^1024*1^4653 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4653 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4653/1024 : ℝ) ≤ (194398261153682431/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4653 ≤ (194398261153682431/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4653*12500000000000000000^1024 ≤ 194398261153682431^1024*5^4653 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 194398261153682431 12500000000000000000 4653 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (194398261153682431/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4653/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4653 := by
      have hnat : (1 : ℕ)^1024*1^4653 ≤ 1^4653*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4653 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12694398261153682431/12500000000000000000 : ℝ) ≤ (5017009893481949/5000000000000000 : ℝ) ^ (4653/1024 : ℝ) := by
    have hpowers : (12694398261153682431/12500000000000000000 : ℝ)^1024 ≤ (5017009893481949/5000000000000000 : ℝ)^4653 := by
      have hnat : (12694398261153682431 : ℕ)^1024*5000000000000000^4653 ≤ 5017009893481949^4653*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12694398261153682431 12500000000000000000 5017009893481949 5000000000000000 1024 4653 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5017009893481949/5000000000000000 : ℝ)) (X := (12694398261153682431/12500000000000000000 : ℝ)) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6444398261153682431/6250000000000000000 : ℝ) ≤ (2517009893481949/2500000000000000 : ℝ) ^ (4653/1024 : ℝ) := by
    have hpowers : (6444398261153682431/6250000000000000000 : ℝ)^1024 ≤ (2517009893481949/2500000000000000 : ℝ)^4653 := by
      have hnat : (6444398261153682431 : ℕ)^1024*2500000000000000^4653 ≤ 2517009893481949^4653*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6444398261153682431 6250000000000000000 2517009893481949 2500000000000000 1024 4653 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2517009893481949/2500000000000000 : ℝ)) (X := (6444398261153682431/6250000000000000000 : ℝ)) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(17009893481949/2000000000000000 : ℝ)*(0 : ℝ))^(4653/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(17009893481949/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(194398261153682431/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(17009893481949/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4653/1024 : ℝ) := by
    rw [show (1 : ℝ)+(17009893481949/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5017009893481949/5000000000000000 : ℝ) by norm_num, show 1+(194398261153682431/12500000000000000000 : ℝ)+(0 : ℝ)=(12694398261153682431/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(194398261153682431/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(17009893481949/2000000000000000 : ℝ)*(2/5 : ℝ))^(4653/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(17009893481949/2000000000000000 : ℝ)*(2/5 : ℝ)=(2517009893481949/2500000000000000 : ℝ) by norm_num, show 1+2*(194398261153682431/12500000000000000000 : ℝ)=(6444398261153682431/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(17009893481949/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4653/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17009893481949/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(17009893481949/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4653/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17009893481949/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(17009893481949/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4653/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17009893481949/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-404255049/2500000000 : ℝ)*X 0 0+(1465767929/2500000000 : ℝ)*X 0 1+(2441471767/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1365890469/2500000000 : ℝ)*X 1 0+(-5404633/25000000 : ℝ)*X 1 1+(4882943509/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5463561941/10000000000 : ℝ)*X 2 0+(4882943421/10000000000 : ℝ)*X 2 1+(-1080926613/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((825507163/2000000000 : ℝ)*X 0 0+(309369163/1000000000 : ℝ)*X 0 1+(169423031/312500000 : ℝ)*X 0 2+(825507163/2000000000 : ℝ)*X 1 0+(309369163/1000000000 : ℝ)*X 1 1+(169423031/312500000 : ℝ)*X 1 2+(825507163/2000000000 : ℝ)*X 2 0+(309369163/1000000000 : ℝ)*X 2 1+(169423031/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1620008809/10000000000 : ℝ)*X 0 0+(1226898233/2500000000 : ℝ)*X 0 1+(233502021/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5195608987/10000000000 : ℝ)*X 1 0+(-9657973/80000000 : ℝ)*X 1 1+(291877517/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2597803891/5000000000 : ℝ)*X 2 0+(1167510339/2000000000 : ℝ)*X 2 1+(-301811583/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4134631527/10000000000 : ℝ)*X 0 0+(2681494867/5000000000 : ℝ)*X 0 1+(98572029/312500000 : ℝ)*X 0 2+(4134631527/10000000000 : ℝ)*X 1 0+(2681494867/5000000000 : ℝ)*X 1 1+(98572029/312500000 : ℝ)*X 1 2+(4134631527/10000000000 : ℝ)*X 2 0+(2681494867/5000000000 : ℝ)*X 2 1+(98572029/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (860063732360818732139601/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (79891837/100000000000000 : ℝ)*(base1) + (1744847687/100000000000000 : ℝ)*(base19) + (878493013/50000000000000 : ℝ)*(base23) + (57255579/25000000000000 : ℝ)*(upper3) + (112181267/50000000000000 : ℝ)*(upper5) + (724937452274339/100000000000000 : ℝ)*(major0) + (724937452274339/100000000000000 : ℝ)*(major1) + (724937452274339/100000000000000 : ℝ)*(major2) + (255070229399241/25000000000000 : ℝ)*(sp0) + (255071402850057/25000000000000 : ℝ)*(sp1) + (1020285599261889/100000000000000 : ℝ)*(sp2) + (26849025613157/6250000000000 : ℝ)*(sp3) + (1629635697/25000000000000 : ℝ)*(sp4) + (1385955249/50000000000000 : ℝ)*(sp7) + (429587261612847/100000000000000 : ℝ)*(f.failure) + (204057471249583/20000000000000 : ℝ)*(f.sum) + (21536563406711/100000000000000000000000000000 : ℝ)*base65 + (1824124546006711/200000000000000000000000000000 : ℝ)*base67 + (574975812393289/200000000000000000000000000000 : ℝ)*base70 + (518208801606711/200000000000000000000000000000 : ℝ)*base71 + (411350643206711/100000000000000000000000000000 : ℝ)*base73 + (783519072406711/200000000000000000000000000000 : ℝ)*base75 + (967477037406711/200000000000000000000000000000 : ℝ)*base77 + (1083257020206711/200000000000000000000000000000 : ℝ)*base79 + (444907120993289/100000000000000000000000000000 : ℝ)*base82 + (29189699/10000000000000000000000 : ℝ)*base90 + (29189699/10000000000000000000000 : ℝ)*base92 + (29189699/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (250984409794142368697859/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1351342511/100000000000000 : ℝ)*(base19) + (1503036191/100000000000000 : ℝ)*(base23) + (236449491/50000000000000 : ℝ)*(base39) + (65774757/50000000000000 : ℝ)*(upper3) + (528049503/100000000000000 : ℝ)*(upper5) + (382018281904157/50000000000000 : ℝ)*(major0) + (382018281904157/50000000000000 : ℝ)*(major1) + (191009022727333/25000000000000 : ℝ)*(major2) + (4305926271/100000000000000 : ℝ)*(sp1) + (61271837/2000000000000 : ℝ)*(sp2) + (268828916977007/25000000000000 : ℝ)*(sp4) + (537655005319623/50000000000000 : ℝ)*(sp5) + (134413946772371/12500000000000 : ℝ)*(sp6) + (18110272779467/4000000000000 : ℝ)*(sp7) + (18110272779467/4000000000000 : ℝ)*(f.failure) + (107531614080701/10000000000000 : ℝ)*(f.sum) + (50811789086027/100000000000000000000000000000 : ℝ)*base65 + (79317157112017/50000000000000000000000000000 : ℝ)*base67 + (87175717561993/100000000000000000000000000000 : ℝ)*base69 + (27682238262017/50000000000000000000000000000 : ℝ)*base71 + (353436946386027/100000000000000000000000000000 : ℝ)*base73 + (394179670338007/100000000000000000000000000000 : ℝ)*base76 + (352699372461993/100000000000000000000000000000 : ℝ)*base77 + (411444221561993/100000000000000000000000000000 : ℝ)*base79 + (61596581361993/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (120239/400000000000000000000 : ℝ)*base90 + (120239/400000000000000000000 : ℝ)*base92 + (120239/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1579_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168752083/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (73/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4929/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1579_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1579_s1_0 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-219170617/1250000000 : ℝ)*x 0 + (5529789333/10000000000 : ℝ)*x 1 + (512830211/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219170617/1250000000 : ℝ)^4655 ≤ (5365401631393/50000000000000 : ℝ)^3631 := by
    have hnat : (219170617 : ℕ)^4655*50000000000000^3631 ≤ 5365401631393^3631*1250000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219170617 1250000000 5365401631393 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5529789333/10000000000 : ℝ)^4655 ≤ (46789488541359/100000000000000 : ℝ)^3631 := by
    have hnat : (5529789333 : ℕ)^4655*100000000000000^3631 ≤ 46789488541359^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5529789333 10000000000 46789488541359 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512830211/1000000000 : ℝ)^4655 ≤ (4247970817831/10000000000000 : ℝ)^3631 := by
    have hnat : (512830211 : ℕ)^4655*10000000000000^3631 ≤ 4247970817831^3631*1000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512830211 1000000000 4247970817831 10000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219170617/1250000000 : ℝ), (5529789333/10000000000 : ℝ), (512830211/1000000000 : ℝ)] ![(5365401631393/50000000000000 : ℝ), (46789488541359/100000000000000 : ℝ), (4247970817831/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219170617/1250000000 : ℝ)|^4655 ≤ (5365401631393/50000000000000 : ℝ)^3631
        have hw : |(-219170617/1250000000 : ℝ)|=(219170617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5529789333/10000000000 : ℝ)|^4655 ≤ (46789488541359/100000000000000 : ℝ)^3631
        have hw : |(5529789333/10000000000 : ℝ)|=(5529789333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(512830211/1000000000 : ℝ)|^4655 ≤ (4247970817831/10000000000000 : ℝ)^3631
        have hw : |(512830211/1000000000 : ℝ)|=(512830211/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s1_1 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343731863/2500000000 : ℝ)*x 0 + (-245396789/1250000000 : ℝ)*x 1 + (5128301759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343731863/2500000000 : ℝ)^4655 ≤ (11279072379757/25000000000000 : ℝ)^3631 := by
    have hnat : (1343731863 : ℕ)^4655*25000000000000^3631 ≤ 11279072379757^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343731863 2500000000 11279072379757 25000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245396789/1250000000 : ℝ)^4655 ≤ (12404006011011/100000000000000 : ℝ)^3631 := by
    have hnat : (245396789 : ℕ)^4655*100000000000000^3631 ≤ 12404006011011^3631*1250000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245396789 1250000000 12404006011011 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5128301759/10000000000 : ℝ)^4655 ≤ (42479704450889/100000000000000 : ℝ)^3631 := by
    have hnat : (5128301759 : ℕ)^4655*100000000000000^3631 ≤ 42479704450889^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128301759 10000000000 42479704450889 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343731863/2500000000 : ℝ), (-245396789/1250000000 : ℝ), (5128301759/10000000000 : ℝ)] ![(11279072379757/25000000000000 : ℝ), (12404006011011/100000000000000 : ℝ), (42479704450889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343731863/2500000000 : ℝ)|^4655 ≤ (11279072379757/25000000000000 : ℝ)^3631
        have hw : |(1343731863/2500000000 : ℝ)|=(1343731863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-245396789/1250000000 : ℝ)|^4655 ≤ (12404006011011/100000000000000 : ℝ)^3631
        have hw : |(-245396789/1250000000 : ℝ)|=(245396789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5128301759/10000000000 : ℝ)|^4655 ≤ (42479704450889/100000000000000 : ℝ)^3631
        have hw : |(5128301759/10000000000 : ℝ)|=(5128301759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s1_2 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343731803/2500000000 : ℝ)*x 0 + (1282075499/2500000000 : ℝ)*x 1 + (-1963174321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343731803/2500000000 : ℝ)^4655 ≤ (22558143468189/50000000000000 : ℝ)^3631 := by
    have hnat : (1343731803 : ℕ)^4655*50000000000000^3631 ≤ 22558143468189^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343731803 2500000000 22558143468189 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1282075499/2500000000 : ℝ)^4655 ≤ (8495941393539/20000000000000 : ℝ)^3631 := by
    have hnat : (1282075499 : ℕ)^4655*20000000000000^3631 ≤ 8495941393539^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282075499 2500000000 8495941393539 20000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1963174321/10000000000 : ℝ)^4655 ≤ (12404006083913/100000000000000 : ℝ)^3631 := by
    have hnat : (1963174321 : ℕ)^4655*100000000000000^3631 ≤ 12404006083913^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963174321 10000000000 12404006083913 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343731803/2500000000 : ℝ), (1282075499/2500000000 : ℝ), (-1963174321/10000000000 : ℝ)] ![(22558143468189/50000000000000 : ℝ), (8495941393539/20000000000000 : ℝ), (12404006083913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343731803/2500000000 : ℝ)|^4655 ≤ (22558143468189/50000000000000 : ℝ)^3631
        have hw : |(1343731803/2500000000 : ℝ)|=(1343731803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1282075499/2500000000 : ℝ)|^4655 ≤ (8495941393539/20000000000000 : ℝ)^3631
        have hw : |(1282075499/2500000000 : ℝ)|=(1282075499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1963174321/10000000000 : ℝ)|^4655 ≤ (12404006083913/100000000000000 : ℝ)^3631
        have hw : |(-1963174321/10000000000 : ℝ)|=(1963174321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s1_3 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4225185553/10000000000 : ℝ)*x 0 + (1884971909/5000000000 : ℝ)*x 1 + (2361746843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4225185553/10000000000 : ℝ)^4655 ≤ (33138154717703/100000000000000 : ℝ)^3631 := by
    have hnat : (4225185553 : ℕ)^4655*100000000000000^3631 ≤ 33138154717703^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225185553 10000000000 33138154717703 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1884971909/5000000000 : ℝ)^4655 ≤ (14316094307917/50000000000000 : ℝ)^3631 := by
    have hnat : (1884971909 : ℕ)^4655*50000000000000^3631 ≤ 14316094307917^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884971909 5000000000 14316094307917 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2361746843/5000000000 : ℝ)^4655 ≤ (7645931331763/20000000000000 : ℝ)^3631 := by
    have hnat : (2361746843 : ℕ)^4655*20000000000000^3631 ≤ 7645931331763^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2361746843 5000000000 7645931331763 20000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4225185553/10000000000 : ℝ), (1884971909/5000000000 : ℝ), (2361746843/5000000000 : ℝ)] ![(33138154717703/100000000000000 : ℝ), (14316094307917/50000000000000 : ℝ), (7645931331763/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4225185553/10000000000 : ℝ)|^4655 ≤ (33138154717703/100000000000000 : ℝ)^3631
        have hw : |(4225185553/10000000000 : ℝ)|=(4225185553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1884971909/5000000000 : ℝ)|^4655 ≤ (14316094307917/50000000000000 : ℝ)^3631
        have hw : |(1884971909/5000000000 : ℝ)|=(1884971909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2361746843/5000000000 : ℝ)|^4655 ≤ (7645931331763/20000000000000 : ℝ)^3631
        have hw : |(2361746843/5000000000 : ℝ)|=(2361746843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s1_4 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-876782523/5000000000 : ℝ)*x 0 + (5132393733/10000000000 : ℝ)*x 1 + (1105127627/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (876782523/5000000000 : ℝ)^4655 ≤ (5366186684681/50000000000000 : ℝ)^3631 := by
    have hnat : (876782523 : ℕ)^4655*50000000000000^3631 ≤ 5366186684681^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876782523 5000000000 5366186684681 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5132393733/10000000000 : ℝ)^4655 ≤ (21261581892527/50000000000000 : ℝ)^3631 := by
    have hnat : (5132393733 : ℕ)^4655*50000000000000^3631 ≤ 21261581892527^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132393733 10000000000 21261581892527 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105127627/2000000000 : ℝ)^4655 ≤ (46744462826809/100000000000000 : ℝ)^3631 := by
    have hnat : (1105127627 : ℕ)^4655*100000000000000^3631 ≤ 46744462826809^3631*2000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105127627 2000000000 46744462826809 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-876782523/5000000000 : ℝ), (5132393733/10000000000 : ℝ), (1105127627/2000000000 : ℝ)] ![(5366186684681/50000000000000 : ℝ), (21261581892527/50000000000000 : ℝ), (46744462826809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-876782523/5000000000 : ℝ)|^4655 ≤ (5366186684681/50000000000000 : ℝ)^3631
        have hw : |(-876782523/5000000000 : ℝ)|=(876782523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5132393733/10000000000 : ℝ)|^4655 ≤ (21261581892527/50000000000000 : ℝ)^3631
        have hw : |(5132393733/10000000000 : ℝ)|=(5132393733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1105127627/2000000000 : ℝ)|^4655 ≤ (46744462826809/100000000000000 : ℝ)^3631
        have hw : |(1105127627/2000000000 : ℝ)|=(1105127627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s1_5 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5268412417/10000000000 : ℝ)*x 0 + (-782918987/5000000000 : ℝ)*x 1 + (138140969/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5268412417/10000000000 : ℝ)^4655 ≤ (2748330957781/6250000000000 : ℝ)^3631 := by
    have hnat : (5268412417 : ℕ)^4655*6250000000000^3631 ≤ 2748330957781^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268412417 10000000000 2748330957781 6250000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (782918987/5000000000 : ℝ)^4655 ≤ (580139691037/6250000000000 : ℝ)^3631 := by
    have hnat : (782918987 : ℕ)^4655*6250000000000^3631 ≤ 580139691037^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782918987 5000000000 580139691037 6250000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138140969/250000000 : ℝ)^4655 ≤ (9348893921023/20000000000000 : ℝ)^3631 := by
    have hnat : (138140969 : ℕ)^4655*20000000000000^3631 ≤ 9348893921023^3631*250000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138140969 250000000 9348893921023 20000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5268412417/10000000000 : ℝ), (-782918987/5000000000 : ℝ), (138140969/250000000 : ℝ)] ![(2748330957781/6250000000000 : ℝ), (580139691037/6250000000000 : ℝ), (9348893921023/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5268412417/10000000000 : ℝ)|^4655 ≤ (2748330957781/6250000000000 : ℝ)^3631
        have hw : |(5268412417/10000000000 : ℝ)|=(5268412417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-782918987/5000000000 : ℝ)|^4655 ≤ (580139691037/6250000000000 : ℝ)^3631
        have hw : |(-782918987/5000000000 : ℝ)|=(782918987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(138140969/250000000 : ℝ)|^4655 ≤ (9348893921023/20000000000000 : ℝ)^3631
        have hw : |(138140969/250000000 : ℝ)|=(138140969/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s1_6 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053682333/2000000000 : ℝ)*x 0 + (5525639051/10000000000 : ℝ)*x 1 + (-1565838617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053682333/2000000000 : ℝ)^4655 ≤ (21986643638873/50000000000000 : ℝ)^3631 := by
    have hnat : (1053682333 : ℕ)^4655*50000000000000^3631 ≤ 21986643638873^3631*2000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053682333 2000000000 21986643638873 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5525639051/10000000000 : ℝ)^4655 ≤ (9348894552219/20000000000000 : ℝ)^3631 := by
    have hnat : (5525639051 : ℕ)^4655*20000000000000^3631 ≤ 9348894552219^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5525639051 10000000000 9348894552219 20000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1565838617/10000000000 : ℝ)^4655 ≤ (928223994323/10000000000000 : ℝ)^3631 := by
    have hnat : (1565838617 : ℕ)^4655*10000000000000^3631 ≤ 928223994323^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1565838617 10000000000 928223994323 10000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053682333/2000000000 : ℝ), (5525639051/10000000000 : ℝ), (-1565838617/10000000000 : ℝ)] ![(21986643638873/50000000000000 : ℝ), (9348894552219/20000000000000 : ℝ), (928223994323/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053682333/2000000000 : ℝ)|^4655 ≤ (21986643638873/50000000000000 : ℝ)^3631
        have hw : |(1053682333/2000000000 : ℝ)|=(1053682333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5525639051/10000000000 : ℝ)|^4655 ≤ (9348894552219/20000000000000 : ℝ)^3631
        have hw : |(5525639051/10000000000 : ℝ)|=(5525639051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1565838617/10000000000 : ℝ)|^4655 ≤ (928223994323/10000000000000 : ℝ)^3631
        have hw : |(-1565838617/10000000000 : ℝ)|=(1565838617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s1_7 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2112829979/5000000000 : ℝ)*x 0 + (4713776573/10000000000 : ℝ)*x 1 + (1889901187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2112829979/5000000000 : ℝ)^4655 ≤ (1657146243423/5000000000000 : ℝ)^3631 := by
    have hnat : (2112829979 : ℕ)^4655*5000000000000^3631 ≤ 1657146243423^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112829979 5000000000 1657146243423 5000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4713776573/10000000000 : ℝ)^4655 ≤ (38128861032551/100000000000000 : ℝ)^3631 := by
    have hnat : (4713776573 : ℕ)^4655*100000000000000^3631 ≤ 38128861032551^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4713776573 10000000000 38128861032551 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1889901187/5000000000 : ℝ)^4655 ≤ (28728214082221/100000000000000 : ℝ)^3631 := by
    have hnat : (1889901187 : ℕ)^4655*100000000000000^3631 ≤ 28728214082221^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889901187 5000000000 28728214082221 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2112829979/5000000000 : ℝ), (4713776573/10000000000 : ℝ), (1889901187/5000000000 : ℝ)] ![(1657146243423/5000000000000 : ℝ), (38128861032551/100000000000000 : ℝ), (28728214082221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2112829979/5000000000 : ℝ)|^4655 ≤ (1657146243423/5000000000000 : ℝ)^3631
        have hw : |(2112829979/5000000000 : ℝ)|=(2112829979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4713776573/10000000000 : ℝ)|^4655 ≤ (38128861032551/100000000000000 : ℝ)^3631
        have hw : |(4713776573/10000000000 : ℝ)|=(4713776573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1889901187/5000000000 : ℝ)|^4655 ≤ (28728214082221/100000000000000 : ℝ)^3631
        have hw : |(1889901187/5000000000 : ℝ)|=(1889901187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1579_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168752083/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4929/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (73/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (9169/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8837/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4929/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (73/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4929/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (73/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4929/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (73/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4929/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (73/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4929/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (73/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4929/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (73/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (73/2000 : ℝ) ^ (4653/1024 : ℝ) ≤ (14659103292899/50000000000000000000 : ℝ) := by
    have hpowers : (73/2000 : ℝ)^4653 ≤ (14659103292899/50000000000000000000 : ℝ)^1024 := by
      have hnat : (73 : ℕ)^4653*50000000000000000000^1024 ≤ 14659103292899^1024*2000^4653 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73 2000 14659103292899 50000000000000000000 4653 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73/2000 : ℝ)) (X := (14659103292899/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4929/20000 : ℝ) ^ (4653/1024 : ℝ) ≤ (2690723428692639/1562500000000000000 : ℝ) := by
    have hpowers : (4929/20000 : ℝ)^4653 ≤ (2690723428692639/1562500000000000000 : ℝ)^1024 := by
      have hnat : (4929 : ℕ)^4653*1562500000000000000^1024 ≤ 2690723428692639^1024*20000^4653 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4929 20000 2690723428692639 1562500000000000000 4653 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4929/20000 : ℝ)) (X := (2690723428692639/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000014659103292899/25000000000000000000 : ℝ) ≤ (5000000645214629/5000000000000000 : ℝ) ^ (4653/1024 : ℝ) := by
    have hpowers : (25000014659103292899/25000000000000000000 : ℝ)^1024 ≤ (5000000645214629/5000000000000000 : ℝ)^4653 := by
      have hnat : (25000014659103292899 : ℕ)^1024*5000000000000000^4653 ≤ 5000000645214629^4653*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000014659103292899 25000000000000000000 5000000645214629 5000000000000000 1024 4653 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000645214629/5000000000000000 : ℝ)) (X := (25000014659103292899/25000000000000000000 : ℝ)) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50086117808821457347/50000000000000000000 : ℝ) ≤ (10003787898858743/10000000000000000 : ℝ) ^ (4653/1024 : ℝ) := by
    have hpowers : (50086117808821457347/50000000000000000000 : ℝ)^1024 ≤ (10003787898858743/10000000000000000 : ℝ)^4653 := by
      have hnat : (50086117808821457347 : ℕ)^1024*10000000000000000^4653 ≤ 10003787898858743^4653*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50086117808821457347 50000000000000000000 10003787898858743 10000000000000000 1024 4653 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003787898858743/10000000000000000 : ℝ)) (X := (50086117808821457347/50000000000000000000 : ℝ)) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (783940723428692639/781250000000000000 : ℝ) ≤ (2501893626822057/2500000000000000 : ℝ) ^ (4653/1024 : ℝ) := by
    have hpowers : (783940723428692639/781250000000000000 : ℝ)^1024 ≤ (2501893626822057/2500000000000000 : ℝ)^4653 := by
      have hnat : (783940723428692639 : ℕ)^1024*2500000000000000^4653 ≤ 2501893626822057^4653*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        783940723428692639 781250000000000000 2501893626822057 2500000000000000 1024 4653 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501893626822057/2500000000000000 : ℝ)) (X := (783940723428692639/781250000000000000 : ℝ)) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14659103292899/50000000000000000000 : ℝ) ≤ ((20992238485102703121/20995000000000000000 : ℝ)+2*(757321685897/419900000000000 : ℝ)*(73/2000 : ℝ))^(4653/1024 : ℝ) := by
    rw [show (20992238485102703121/20995000000000000000 : ℝ)+2*(757321685897/419900000000000 : ℝ)*(73/2000 : ℝ)=(5000000645214629/5000000000000000 : ℝ) by norm_num, show 1+2*(14659103292899/50000000000000000000 : ℝ)=(25000014659103292899/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2690723428692639/1562500000000000000 : ℝ)+(14659103292899/50000000000000000000 : ℝ) ≤ ((20992238485102703121/20995000000000000000 : ℝ)+(757321685897/419900000000000 : ℝ)*((4929/20000 : ℝ)+(73/2000 : ℝ)))^(4653/1024 : ℝ) := by
    rw [show (20992238485102703121/20995000000000000000 : ℝ)+(757321685897/419900000000000 : ℝ)*((4929/20000 : ℝ)+(73/2000 : ℝ))=(10003787898858743/10000000000000000 : ℝ) by norm_num, show 1+(2690723428692639/1562500000000000000 : ℝ)+(14659103292899/50000000000000000000 : ℝ)=(50086117808821457347/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2690723428692639/1562500000000000000 : ℝ) ≤ ((20992238485102703121/20995000000000000000 : ℝ)+2*(757321685897/419900000000000 : ℝ)*(4929/20000 : ℝ))^(4653/1024 : ℝ) := by
    rw [show (20992238485102703121/20995000000000000000 : ℝ)+2*(757321685897/419900000000000 : ℝ)*(4929/20000 : ℝ)=(2501893626822057/2500000000000000 : ℝ) by norm_num, show 1+2*(2690723428692639/1562500000000000000 : ℝ)=(783940723428692639/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20992238485102703121/20995000000000000000 : ℝ)*(X 1 0+X 2 0)+(757321685897/419900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4653/1024 : ℝ)) (lo := (73/2000 : ℝ)) (hi := (4929/20000 : ℝ)) (c := (20992238485102703121/20995000000000000000 : ℝ)) (alpha := (757321685897/419900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20992238485102703121/20995000000000000000 : ℝ)*(X 0 1+X 2 1)+(757321685897/419900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4653/1024 : ℝ)) (lo := (73/2000 : ℝ)) (hi := (4929/20000 : ℝ)) (c := (20992238485102703121/20995000000000000000 : ℝ)) (alpha := (757321685897/419900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20992238485102703121/20995000000000000000 : ℝ)*(X 0 2+X 1 2)+(757321685897/419900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4653/1024 : ℝ)) (lo := (73/2000 : ℝ)) (hi := (4929/20000 : ℝ)) (c := (20992238485102703121/20995000000000000000 : ℝ)) (alpha := (757321685897/419900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-219170617/1250000000 : ℝ)*X 0 0+(5529789333/10000000000 : ℝ)*X 0 1+(512830211/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1343731863/2500000000 : ℝ)*X 1 0+(-245396789/1250000000 : ℝ)*X 1 1+(5128301759/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1343731803/2500000000 : ℝ)*X 2 0+(1282075499/2500000000 : ℝ)*X 2 1+(-1963174321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4225185553/10000000000 : ℝ)*X 0 0+(1884971909/5000000000 : ℝ)*X 0 1+(2361746843/5000000000 : ℝ)*X 0 2+(4225185553/10000000000 : ℝ)*X 1 0+(1884971909/5000000000 : ℝ)*X 1 1+(2361746843/5000000000 : ℝ)*X 1 2+(4225185553/10000000000 : ℝ)*X 2 0+(1884971909/5000000000 : ℝ)*X 2 1+(2361746843/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-876782523/5000000000 : ℝ)*X 0 0+(5132393733/10000000000 : ℝ)*X 0 1+(1105127627/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5268412417/10000000000 : ℝ)*X 1 0+(-782918987/5000000000 : ℝ)*X 1 1+(138140969/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1053682333/2000000000 : ℝ)*X 2 0+(5525639051/10000000000 : ℝ)*X 2 1+(-1565838617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2112829979/5000000000 : ℝ)*X 0 0+(4713776573/10000000000 : ℝ)*X 0 1+(1889901187/5000000000 : ℝ)*X 0 2+(2112829979/5000000000 : ℝ)*X 1 0+(4713776573/10000000000 : ℝ)*X 1 1+(1889901187/5000000000 : ℝ)*X 1 2+(2112829979/5000000000 : ℝ)*X 2 0+(4713776573/10000000000 : ℝ)*X 2 1+(1889901187/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (55231409163987322756831083/13812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1467569291/100000000000000 : ℝ)*(base19) + (317472381/25000000000000 : ℝ)*(base23) + (30543521/20000000000000 : ℝ)*(upper3) + (4647313/10000000000000 : ℝ)*(upper4) + (7997387/12500000000000 : ℝ)*(upper5) + (442436106180207/25000000000000 : ℝ)*(major0) + (442436106180207/25000000000000 : ℝ)*(major1) + (442436106180207/25000000000000 : ℝ)*(major2) + (311344034317421/12500000000000 : ℝ)*(sp0) + (1245381378428339/50000000000000 : ℝ)*(sp1) + (622690738634111/25000000000000 : ℝ)*(sp2) + (262179589501919/25000000000000 : ℝ)*(sp3) + (59749433/500000000000 : ℝ)*(sp4) + (1533429883/25000000000000 : ℝ)*(sp7) + (1048724491727209/100000000000000 : ℝ)*(f.failure) + (155672764026623/6250000000000 : ℝ)*(f.sum) + (894883321597/656093750000000000000000000 : ℝ)*base66 + (5459822985249776047/524875000000000000000000000000000 : ℝ)*base67 + (9936875497604276047/524875000000000000000000000000000 : ℝ)*base69 + (1772618734298776047/524875000000000000000000000000000 : ℝ)*base71 + (2848822950691/1312187500000000000000000000 : ℝ)*base73 + (7301825000944526047/524875000000000000000000000000000 : ℝ)*base75 + (6029570355207776047/524875000000000000000000000000000 : ℝ)*base77 + (4166372011109776047/524875000000000000000000000000000 : ℝ)*base79 + (2615457300369/328046875000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (13473653/10000000000000000000000 : ℝ)*base90 + (13473653/10000000000000000000000 : ℝ)*base92 + (13473653/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (324271698443992313774877201/55250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (508480351/50000000000000 : ℝ)*(base19) + (220957917/25000000000000 : ℝ)*(base23) + (12962369/10000000000000 : ℝ)*(upper2) + (32681273/12500000000000 : ℝ)*(upper3) + (78039609/100000000000000 : ℝ)*(upper5) + (1806817953842287/100000000000000 : ℝ)*(major0) + (1806817953842287/100000000000000 : ℝ)*(major1) + (1806817953842287/100000000000000 : ℝ)*(major2) + (2217944999/25000000000000 : ℝ)*(sp1) + (8070691497/100000000000000 : ℝ)*(sp2) + (1271470996380661/50000000000000 : ℝ)*(sp4) + (158933256501289/6250000000000 : ℝ)*(sp5) + (2542933038238157/100000000000000 : ℝ)*(sp6) + (133836714910527/12500000000000 : ℝ)*(sp7) + (133836714910527/12500000000000 : ℝ)*(f.failure) + (1271470996380661/50000000000000 : ℝ)*(f.sum) + (921208470999/1105000000000000000000000000 : ℝ)*base66 + (429000784428190933/110500000000000000000000000000000 : ℝ)*base67 + (12908214401809067/110500000000000000000000000000000 : ℝ)*base70 + (423575838421190933/110500000000000000000000000000000 : ℝ)*base71 + (938624513019/1105000000000000000000000000 : ℝ)*base74 + (432916772491190933/110500000000000000000000000000000 : ℝ)*base75 + (80158231853309067/110500000000000000000000000000000 : ℝ)*base78 + (503565964201690933/110500000000000000000000000000000 : ℝ)*base79 + (2057037155509/1105000000000000000000000000 : ℝ)*base82 + (2377741/1250000000000000000000 : ℝ)*base89 + (2377741/1250000000000000000000 : ℝ)*base91 + (2377741/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1579_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168752083/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4929/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (73/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9169/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8837/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1579_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1579_s2_0 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-354233643/2000000000 : ℝ)*x 0 + (5439221931/10000000000 : ℝ)*x 1 + (260362871/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (354233643/2000000000 : ℝ)^4655 ≤ (10870688927129/100000000000000 : ℝ)^3631 := by
    have hnat : (354233643 : ℕ)^4655*100000000000000^3631 ≤ 10870688927129^3631*2000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354233643 2000000000 10870688927129 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439221931/10000000000 : ℝ)^4655 ≤ (22904664297409/50000000000000 : ℝ)^3631 := by
    have hnat : (5439221931 : ℕ)^4655*50000000000000^3631 ≤ 22904664297409^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439221931 10000000000 22904664297409 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260362871/500000000 : ℝ)^4655 ≤ (43319982460917/100000000000000 : ℝ)^3631 := by
    have hnat : (260362871 : ℕ)^4655*100000000000000^3631 ≤ 43319982460917^3631*500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260362871 500000000 43319982460917 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-354233643/2000000000 : ℝ), (5439221931/10000000000 : ℝ), (260362871/500000000 : ℝ)] ![(10870688927129/100000000000000 : ℝ), (22904664297409/50000000000000 : ℝ), (43319982460917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-354233643/2000000000 : ℝ)|^4655 ≤ (10870688927129/100000000000000 : ℝ)^3631
        have hw : |(-354233643/2000000000 : ℝ)|=(354233643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439221931/10000000000 : ℝ)|^4655 ≤ (22904664297409/50000000000000 : ℝ)^3631
        have hw : |(5439221931/10000000000 : ℝ)|=(5439221931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260362871/500000000 : ℝ)|^4655 ≤ (43319982460917/100000000000000 : ℝ)^3631
        have hw : |(260362871/500000000 : ℝ)|=(260362871/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s2_1 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535148277/1000000000 : ℝ)*x 0 + (-1890178707/10000000000 : ℝ)*x 1 + (1301814537/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535148277/1000000000 : ℝ)^4655 ≤ (44864155716649/100000000000000 : ℝ)^3631 := by
    have hnat : (535148277 : ℕ)^4655*100000000000000^3631 ≤ 44864155716649^3631*1000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535148277 1000000000 44864155716649 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1890178707/10000000000 : ℝ)^4655 ≤ (1181585405313/10000000000000 : ℝ)^3631 := by
    have hnat : (1890178707 : ℕ)^4655*10000000000000^3631 ≤ 1181585405313^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1890178707 10000000000 1181585405313 10000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1301814537/2500000000 : ℝ)^4655 ≤ (1353749694539/3125000000000 : ℝ)^3631 := by
    have hnat : (1301814537 : ℕ)^4655*3125000000000^3631 ≤ 1353749694539^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301814537 2500000000 1353749694539 3125000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535148277/1000000000 : ℝ), (-1890178707/10000000000 : ℝ), (1301814537/2500000000 : ℝ)] ![(44864155716649/100000000000000 : ℝ), (1181585405313/10000000000000 : ℝ), (1353749694539/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535148277/1000000000 : ℝ)|^4655 ≤ (44864155716649/100000000000000 : ℝ)^3631
        have hw : |(535148277/1000000000 : ℝ)|=(535148277/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1890178707/10000000000 : ℝ)|^4655 ≤ (1181585405313/10000000000000 : ℝ)^3631
        have hw : |(-1890178707/10000000000 : ℝ)|=(1890178707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1301814537/2500000000 : ℝ)|^4655 ≤ (1353749694539/3125000000000 : ℝ)^3631
        have hw : |(1301814537/2500000000 : ℝ)|=(1301814537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s2_2 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351483089/10000000000 : ℝ)*x 0 + (1301814403/2500000000 : ℝ)*x 1 + (-118136187/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351483089/10000000000 : ℝ)^4655 ≤ (44864159145191/100000000000000 : ℝ)^3631 := by
    have hnat : (5351483089 : ℕ)^4655*100000000000000^3631 ≤ 44864159145191^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351483089 10000000000 44864159145191 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1301814403/2500000000 : ℝ)^4655 ≤ (10829996127163/25000000000000 : ℝ)^3631 := by
    have hnat : (1301814403 : ℕ)^4655*25000000000000^3631 ≤ 10829996127163^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301814403 2500000000 10829996127163 25000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118136187/625000000 : ℝ)^4655 ≤ (5907928168577/50000000000000 : ℝ)^3631 := by
    have hnat : (118136187 : ℕ)^4655*50000000000000^3631 ≤ 5907928168577^3631*625000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118136187 625000000 5907928168577 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351483089/10000000000 : ℝ), (1301814403/2500000000 : ℝ), (-118136187/625000000 : ℝ)] ![(44864159145191/100000000000000 : ℝ), (10829996127163/25000000000000 : ℝ), (5907928168577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351483089/10000000000 : ℝ)|^4655 ≤ (44864159145191/100000000000000 : ℝ)^3631
        have hw : |(5351483089/10000000000 : ℝ)|=(5351483089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1301814403/2500000000 : ℝ)|^4655 ≤ (10829996127163/25000000000000 : ℝ)^3631
        have hw : |(1301814403/2500000000 : ℝ)|=(1301814403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-118136187/625000000 : ℝ)|^4655 ≤ (5907928168577/50000000000000 : ℝ)^3631
        have hw : |(-118136187/625000000 : ℝ)|=(118136187/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s2_3 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2119052929/5000000000 : ℝ)*x 0 + (248114959/625000000 : ℝ)*x 1 + (1130190853/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119052929/5000000000 : ℝ)^4655 ≤ (16634061267369/50000000000000 : ℝ)^3631 := by
    have hnat : (2119052929 : ℕ)^4655*50000000000000^3631 ≤ 16634061267369^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119052929 5000000000 16634061267369 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (248114959/625000000 : ℝ)^4655 ≤ (1529644444071/5000000000000 : ℝ)^3631 := by
    have hnat : (248114959 : ℕ)^4655*5000000000000^3631 ≤ 1529644444071^3631*625000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248114959 625000000 1529644444071 5000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130190853/2500000000 : ℝ)^4655 ≤ (4517373571469/12500000000000 : ℝ)^3631 := by
    have hnat : (1130190853 : ℕ)^4655*12500000000000^3631 ≤ 4517373571469^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130190853 2500000000 4517373571469 12500000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2119052929/5000000000 : ℝ), (248114959/625000000 : ℝ), (1130190853/2500000000 : ℝ)] ![(16634061267369/50000000000000 : ℝ), (1529644444071/5000000000000 : ℝ), (4517373571469/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2119052929/5000000000 : ℝ)|^4655 ≤ (16634061267369/50000000000000 : ℝ)^3631
        have hw : |(2119052929/5000000000 : ℝ)|=(2119052929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(248114959/625000000 : ℝ)|^4655 ≤ (1529644444071/5000000000000 : ℝ)^3631
        have hw : |(248114959/625000000 : ℝ)|=(248114959/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130190853/2500000000 : ℝ)|^4655 ≤ (4517373571469/12500000000000 : ℝ)^3631
        have hw : |(1130190853/2500000000 : ℝ)|=(1130190853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s2_4 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1771206109/10000000000 : ℝ)*x 0 + (1041726333/2000000000 : ℝ)*x 1 + (2718918379/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1771206109/10000000000 : ℝ)^4655 ≤ (10870987096107/100000000000000 : ℝ)^3631 := by
    have hnat : (1771206109 : ℕ)^4655*100000000000000^3631 ≤ 10870987096107^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1771206109 10000000000 10870987096107 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041726333/2000000000 : ℝ)^4655 ≤ (17333855891/40000000000 : ℝ)^3631 := by
    have hnat : (1041726333 : ℕ)^4655*40000000000^3631 ≤ 17333855891^3631*2000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041726333 2000000000 17333855891 40000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718918379/5000000000 : ℝ)^4655 ≤ (22897186580681/50000000000000 : ℝ)^3631 := by
    have hnat : (2718918379 : ℕ)^4655*50000000000000^3631 ≤ 22897186580681^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718918379 5000000000 22897186580681 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1771206109/10000000000 : ℝ), (1041726333/2000000000 : ℝ), (2718918379/5000000000 : ℝ)] ![(10870987096107/100000000000000 : ℝ), (17333855891/40000000000 : ℝ), (22897186580681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1771206109/10000000000 : ℝ)|^4655 ≤ (10870987096107/100000000000000 : ℝ)^3631
        have hw : |(-1771206109/10000000000 : ℝ)|=(1771206109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1041726333/2000000000 : ℝ)|^4655 ≤ (17333855891/40000000000 : ℝ)^3631
        have hw : |(1041726333/2000000000 : ℝ)|=(1041726333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718918379/5000000000 : ℝ)|^4655 ≤ (22897186580681/50000000000000 : ℝ)^3631
        have hw : |(2718918379/5000000000 : ℝ)|=(2718918379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s2_5 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058008421/2000000000 : ℝ)*x 0 + (-33192009/200000000 : ℝ)*x 1 + (1359459447/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058008421/2000000000 : ℝ)^4655 ≤ (44204876918689/100000000000000 : ℝ)^3631 := by
    have hnat : (1058008421 : ℕ)^4655*100000000000000^3631 ≤ 44204876918689^3631*2000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058008421 2000000000 44204876918689 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33192009/200000000 : ℝ)^4655 ≤ (10000738788207/100000000000000 : ℝ)^3631 := by
    have hnat : (33192009 : ℕ)^4655*100000000000000^3631 ≤ 10000738788207^3631*200000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33192009 200000000 10000738788207 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359459447/2500000000 : ℝ)^4655 ≤ (22897192140833/50000000000000 : ℝ)^3631 := by
    have hnat : (1359459447 : ℕ)^4655*50000000000000^3631 ≤ 22897192140833^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359459447 2500000000 22897192140833 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058008421/2000000000 : ℝ), (-33192009/200000000 : ℝ), (1359459447/2500000000 : ℝ)] ![(44204876918689/100000000000000 : ℝ), (10000738788207/100000000000000 : ℝ), (22897192140833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058008421/2000000000 : ℝ)|^4655 ≤ (44204876918689/100000000000000 : ℝ)^3631
        have hw : |(1058008421/2000000000 : ℝ)|=(1058008421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-33192009/200000000 : ℝ)|^4655 ≤ (10000738788207/100000000000000 : ℝ)^3631
        have hw : |(-33192009/200000000 : ℝ)|=(33192009/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359459447/2500000000 : ℝ)|^4655 ≤ (22897192140833/50000000000000 : ℝ)^3631
        have hw : |(1359459447/2500000000 : ℝ)|=(1359459447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s2_6 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2645021299/5000000000 : ℝ)*x 0 + (169932467/312500000 : ℝ)*x 1 + (-1659598151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645021299/5000000000 : ℝ)^4655 ≤ (22102441100059/50000000000000 : ℝ)^3631 := by
    have hnat : (2645021299 : ℕ)^4655*50000000000000^3631 ≤ 22102441100059^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645021299 5000000000 22102441100059 50000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169932467/312500000 : ℝ)^4655 ≤ (45794396762317/100000000000000 : ℝ)^3631 := by
    have hnat : (169932467 : ℕ)^4655*100000000000000^3631 ≤ 45794396762317^3631*312500000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169932467 312500000 45794396762317 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1659598151/10000000000 : ℝ)^4655 ≤ (400028841099/4000000000000 : ℝ)^3631 := by
    have hnat : (1659598151 : ℕ)^4655*4000000000000^3631 ≤ 400028841099^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1659598151 10000000000 400028841099 4000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645021299/5000000000 : ℝ), (169932467/312500000 : ℝ), (-1659598151/10000000000 : ℝ)] ![(22102441100059/50000000000000 : ℝ), (45794396762317/100000000000000 : ℝ), (400028841099/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645021299/5000000000 : ℝ)|^4655 ≤ (22102441100059/50000000000000 : ℝ)^3631
        have hw : |(2645021299/5000000000 : ℝ)|=(2645021299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169932467/312500000 : ℝ)|^4655 ≤ (45794396762317/100000000000000 : ℝ)^3631
        have hw : |(169932467/312500000 : ℝ)|=(169932467/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1659598151/10000000000 : ℝ)|^4655 ≤ (400028841099/4000000000000 : ℝ)^3631
        have hw : |(-1659598151/10000000000 : ℝ)|=(1659598151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1579_s2_7 (p : ℝ) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059549641/2500000000 : ℝ)*x 0 + (2258750567/5000000000 : ℝ)*x 1 + (3973128241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059549641/2500000000 : ℝ)^4655 ≤ (8317263871583/25000000000000 : ℝ)^3631 := by
    have hnat : (1059549641 : ℕ)^4655*25000000000000^3631 ≤ 8317263871583^3631*2500000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059549641 2500000000 8317263871583 25000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2258750567/5000000000 : ℝ)^4655 ≤ (7221111744521/20000000000000 : ℝ)^3631 := by
    have hnat : (2258750567 : ℕ)^4655*20000000000000^3631 ≤ 7221111744521^3631*5000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258750567 5000000000 7221111744521 20000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3973128241/10000000000 : ℝ)^4655 ≤ (30625385785497/100000000000000 : ℝ)^3631 := by
    have hnat : (3973128241 : ℕ)^4655*100000000000000^3631 ≤ 30625385785497^3631*10000000000^4655 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3973128241 10000000000 30625385785497 100000000000000 4655 3631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4655/1024 : ℝ)) 4655 3631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059549641/2500000000 : ℝ), (2258750567/5000000000 : ℝ), (3973128241/10000000000 : ℝ)] ![(8317263871583/25000000000000 : ℝ), (7221111744521/20000000000000 : ℝ), (30625385785497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059549641/2500000000 : ℝ)|^4655 ≤ (8317263871583/25000000000000 : ℝ)^3631
        have hw : |(1059549641/2500000000 : ℝ)|=(1059549641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2258750567/5000000000 : ℝ)|^4655 ≤ (7221111744521/20000000000000 : ℝ)^3631
        have hw : |(2258750567/5000000000 : ℝ)|=(2258750567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3973128241/10000000000 : ℝ)|^4655 ≤ (30625385785497/100000000000000 : ℝ)^3631
        have hw : |(3973128241/10000000000 : ℝ)|=(3973128241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1579_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168752083/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8837/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10869/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3947/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8837/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9169/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8837/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9169/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8837/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9169/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8837/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9169/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8837/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9169/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8837/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9169/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
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
  have hpowlo : (9169/100000 : ℝ) ^ (4653/1024 : ℝ) ≤ (1926849488737449/100000000000000000000 : ℝ) := by
    have hpowers : (9169/100000 : ℝ)^4653 ≤ (1926849488737449/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9169 : ℕ)^4653*100000000000000000000^1024 ≤ 1926849488737449^1024*100000^4653 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9169 100000 1926849488737449 100000000000000000000 4653 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9169/100000 : ℝ)) (X := (1926849488737449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8837/50000 : ℝ) ^ (4653/1024 : ℝ) ≤ (38012875458673289/100000000000000000000 : ℝ) := by
    have hpowers : (8837/50000 : ℝ)^4653 ≤ (38012875458673289/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8837 : ℕ)^4653*100000000000000000000^1024 ≤ 38012875458673289^1024*50000^4653 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8837 50000 38012875458673289 100000000000000000000 4653 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8837/50000 : ℝ)) (X := (38012875458673289/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001926849488737449/50000000000000000000 : ℝ) ≤ (10000084808262431/10000000000000000 : ℝ) ^ (4653/1024 : ℝ) := by
    have hpowers : (50001926849488737449/50000000000000000000 : ℝ)^1024 ≤ (10000084808262431/10000000000000000 : ℝ)^4653 := by
      have hnat : (50001926849488737449 : ℕ)^1024*10000000000000000^4653 ≤ 10000084808262431^4653*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001926849488737449 50000000000000000000 10000084808262431 10000000000000000 1024 4653 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000084808262431/10000000000000000 : ℝ)) (X := (50001926849488737449/50000000000000000000 : ℝ)) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019969862473705369/50000000000000000000 : ℝ) ≤ (10000878828926169/10000000000000000 : ℝ) ^ (4653/1024 : ℝ) := by
    have hpowers : (50019969862473705369/50000000000000000000 : ℝ)^1024 ≤ (10000878828926169/10000000000000000 : ℝ)^4653 := by
      have hnat : (50019969862473705369 : ℕ)^1024*10000000000000000^4653 ≤ 10000878828926169^4653*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019969862473705369 50000000000000000000 10000878828926169 10000000000000000 1024 4653 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000878828926169/10000000000000000 : ℝ)) (X := (50019969862473705369/50000000000000000000 : ℝ)) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038012875458673289/50000000000000000000 : ℝ) ≤ (10001672849589907/10000000000000000 : ℝ) ^ (4653/1024 : ℝ) := by
    have hpowers : (50038012875458673289/50000000000000000000 : ℝ)^1024 ≤ (10001672849589907/10000000000000000 : ℝ)^4653 := by
      have hnat : (50038012875458673289 : ℕ)^1024*10000000000000000^4653 ≤ 10001672849589907^4653*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038012875458673289 50000000000000000000 10001672849589907 10000000000000000 1024 4653 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001672849589907/10000000000000000 : ℝ)) (X := (50038012875458673289/50000000000000000000 : ℝ)) (by norm_num) 4653 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1926849488737449/100000000000000000000 : ℝ) ≤ ((85036160543340348211/85050000000000000000 : ℝ)+2*(397010331869/425250000000000 : ℝ)*(9169/100000 : ℝ))^(4653/1024 : ℝ) := by
    rw [show (85036160543340348211/85050000000000000000 : ℝ)+2*(397010331869/425250000000000 : ℝ)*(9169/100000 : ℝ)=(10000084808262431/10000000000000000 : ℝ) by norm_num, show 1+2*(1926849488737449/100000000000000000000 : ℝ)=(50001926849488737449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38012875458673289/100000000000000000000 : ℝ)+(1926849488737449/100000000000000000000 : ℝ) ≤ ((85036160543340348211/85050000000000000000 : ℝ)+(397010331869/425250000000000 : ℝ)*((8837/50000 : ℝ)+(9169/100000 : ℝ)))^(4653/1024 : ℝ) := by
    rw [show (85036160543340348211/85050000000000000000 : ℝ)+(397010331869/425250000000000 : ℝ)*((8837/50000 : ℝ)+(9169/100000 : ℝ))=(10000878828926169/10000000000000000 : ℝ) by norm_num, show 1+(38012875458673289/100000000000000000000 : ℝ)+(1926849488737449/100000000000000000000 : ℝ)=(50019969862473705369/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38012875458673289/100000000000000000000 : ℝ) ≤ ((85036160543340348211/85050000000000000000 : ℝ)+2*(397010331869/425250000000000 : ℝ)*(8837/50000 : ℝ))^(4653/1024 : ℝ) := by
    rw [show (85036160543340348211/85050000000000000000 : ℝ)+2*(397010331869/425250000000000 : ℝ)*(8837/50000 : ℝ)=(10001672849589907/10000000000000000 : ℝ) by norm_num, show 1+2*(38012875458673289/100000000000000000000 : ℝ)=(50038012875458673289/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (85036160543340348211/85050000000000000000 : ℝ)*(X 1 0+X 2 0)+(397010331869/425250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4653/1024 : ℝ)) (lo := (9169/100000 : ℝ)) (hi := (8837/50000 : ℝ)) (c := (85036160543340348211/85050000000000000000 : ℝ)) (alpha := (397010331869/425250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (85036160543340348211/85050000000000000000 : ℝ)*(X 0 1+X 2 1)+(397010331869/425250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4653/1024 : ℝ)) (lo := (9169/100000 : ℝ)) (hi := (8837/50000 : ℝ)) (c := (85036160543340348211/85050000000000000000 : ℝ)) (alpha := (397010331869/425250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (85036160543340348211/85050000000000000000 : ℝ)*(X 0 2+X 1 2)+(397010331869/425250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4653/1024 : ℝ)) (lo := (9169/100000 : ℝ)) (hi := (8837/50000 : ℝ)) (c := (85036160543340348211/85050000000000000000 : ℝ)) (alpha := (397010331869/425250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-354233643/2000000000 : ℝ)*X 0 0+(5439221931/10000000000 : ℝ)*X 0 1+(260362871/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535148277/1000000000 : ℝ)*X 1 0+(-1890178707/10000000000 : ℝ)*X 1 1+(1301814537/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351483089/10000000000 : ℝ)*X 2 0+(1301814403/2500000000 : ℝ)*X 2 1+(-118136187/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2119052929/5000000000 : ℝ)*X 0 0+(248114959/625000000 : ℝ)*X 0 1+(1130190853/2500000000 : ℝ)*X 0 2+(2119052929/5000000000 : ℝ)*X 1 0+(248114959/625000000 : ℝ)*X 1 1+(1130190853/2500000000 : ℝ)*X 1 2+(2119052929/5000000000 : ℝ)*X 2 0+(248114959/625000000 : ℝ)*X 2 1+(1130190853/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1771206109/10000000000 : ℝ)*X 0 0+(1041726333/2000000000 : ℝ)*X 0 1+(2718918379/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058008421/2000000000 : ℝ)*X 1 0+(-33192009/200000000 : ℝ)*X 1 1+(1359459447/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2645021299/5000000000 : ℝ)*X 2 0+(169932467/312500000 : ℝ)*X 2 1+(-1659598151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1059549641/2500000000 : ℝ)*X 0 0+(2258750567/5000000000 : ℝ)*X 0 1+(3973128241/10000000000 : ℝ)*X 0 2+(1059549641/2500000000 : ℝ)*X 1 0+(2258750567/5000000000 : ℝ)*X 1 1+(3973128241/10000000000 : ℝ)*X 1 2+(1059549641/2500000000 : ℝ)*X 2 0+(2258750567/5000000000 : ℝ)*X 2 1+(3973128241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1579_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (123943390339192233834358973/11812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (273400059/20000000000000 : ℝ)*(base19) + (756588357/50000000000000 : ℝ)*(base23) + (83215891/100000000000000 : ℝ)*(upper2) + (298532511/100000000000000 : ℝ)*(upper3) + (142512853/100000000000000 : ℝ)*(upper4) + (76577790148329/2500000000000 : ℝ)*(major0) + (76577790148329/2500000000000 : ℝ)*(major1) + (76577790148329/2500000000000 : ℝ)*(major2) + (2155519470887461/50000000000000 : ℝ)*(sp0) + (2155533326443551/50000000000000 : ℝ)*(sp1) + (4311066506710683/100000000000000 : ℝ)*(sp2) + (907570791541377/50000000000000 : ℝ)*(sp3) + (14539056237/50000000000000 : ℝ)*(sp4) + (1657393011/12500000000000 : ℝ)*(sp7) + (1815154842226843/100000000000000 : ℝ)*(f.failure) + (1077767004971849/25000000000000 : ℝ)*(f.sum) + (555967149923/708750000000000000000000000 : ℝ)*base65 + (47628901927856639/10125000000000000000000000000000 : ℝ)*base67 + (39100071444356639/10125000000000000000000000000000 : ℝ)*base69 + (18156486805143361/10125000000000000000000000000000 : ℝ)*base72 + (4821989105191/1417500000000000000000000000 : ℝ)*base73 + (109572052516143361/10125000000000000000000000000000 : ℝ)*base76 + (98973297681018361/10125000000000000000000000000000 : ℝ)*base78 + (102396922787643361/10125000000000000000000000000000 : ℝ)*base80 + (729044499571/88593750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (114763969/10000000000000000000000 : ℝ)*base89 + (114763969/10000000000000000000000 : ℝ)*base91 + (114763969/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52331755672970965032882571/35437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (226149647/100000000000000 : ℝ)*(base8) + (974461571/100000000000000 : ℝ)*(base15) + (78214719/100000000000000 : ℝ)*(base29) + (1732657/10000000000000 : ℝ)*(lower2) + (281219/2500000000000 : ℝ)*(lower4) + (3099939696675721/100000000000000 : ℝ)*(major0) + (77498494372261/2500000000000 : ℝ)*(major1) + (77498494372261/2500000000000 : ℝ)*(major2) + (40682308783/100000000000000 : ℝ)*(sp2) + (2156537579/100000000000000 : ℝ)*(sp3) + (2181450300721993/50000000000000 : ℝ)*(sp4) + (4362899774917343/100000000000000 : ℝ)*(sp5) + (4362860067070129/100000000000000 : ℝ)*(sp6) + (459244129106299/25000000000000 : ℝ)*(sp7) + (73479146918511/4000000000000 : ℝ)*(f.failure) + (2181450413796817/50000000000000 : ℝ)*(f.sum) + (8500275175421/2126250000000000000000000000 : ℝ)*base65 + (40945101357867847/30375000000000000000000000000000 : ℝ)*base68 + (244295587366382153/30375000000000000000000000000000 : ℝ)*base69 + (97393380738556485131/8505000000000000000000000000000000 : ℝ)*base71 + (5450334557659/42525000000000000000000000000 : ℝ)*base73 + (1344629159221379929/212625000000000000000000000000000 : ℝ)*base76 + (36979655674513514869/8505000000000000000000000000000000 : ℝ)*base78 + (336917071489379929/212625000000000000000000000000000 : ℝ)*base80 + (2979295402301/2657812500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (3/100000000000000 : ℝ)*base88 + (2508413/400000000000000000000 : ℝ)*base89 + (2508413/400000000000000000000 : ℝ)*base91 + (2508413/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1579_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168752083/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8837/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10869/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3947/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1579_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1579_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168752083/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10869/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3947/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1579_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1579_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1579_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4653/1024 : ℝ) ≤ p) (hpb : p ≤ (4655/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168752083/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10869/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3947/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1579_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

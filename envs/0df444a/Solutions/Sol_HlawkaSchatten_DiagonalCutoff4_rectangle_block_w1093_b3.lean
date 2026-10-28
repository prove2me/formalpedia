-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1093_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:57:23.289836+00:00
-- url     : https://prove2.me/submissions/f09654c3-e024-4496-b4d4-79a6db806da3

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
theorem support_rectangle_w1093_box_0 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1031005539/5000000000 : ℝ)*x 0 + (2688498443/5000000000 : ℝ)*x 1 + (5376996971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1031005539/5000000000 : ℝ)^4143 ≤ (3069768569109/25000000000000 : ℝ)^3119 := by
    have hnat : (1031005539 : ℕ)^4143*25000000000000^3119 ≤ 3069768569109^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031005539 5000000000 3069768569109 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688498443/5000000000 : ℝ)^4143 ≤ (43860462394089/100000000000000 : ℝ)^3119 := by
    have hnat : (2688498443 : ℕ)^4143*100000000000000^3119 ≤ 43860462394089^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688498443 5000000000 43860462394089 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376996971/10000000000 : ℝ)^4143 ≤ (342659869649/781250000000 : ℝ)^3119 := by
    have hnat : (5376996971 : ℕ)^4143*781250000000^3119 ≤ 342659869649^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376996971 10000000000 342659869649 781250000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1031005539/5000000000 : ℝ), (2688498443/5000000000 : ℝ), (5376996971/10000000000 : ℝ)] ![(3069768569109/25000000000000 : ℝ), (43860462394089/100000000000000 : ℝ), (342659869649/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1031005539/5000000000 : ℝ)|^4143 ≤ (3069768569109/25000000000000 : ℝ)^3119
        have hw : |(-1031005539/5000000000 : ℝ)|=(1031005539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688498443/5000000000 : ℝ)|^4143 ≤ (43860462394089/100000000000000 : ℝ)^3119
        have hw : |(2688498443/5000000000 : ℝ)|=(2688498443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376996971/10000000000 : ℝ)|^4143 ≤ (342659869649/781250000000 : ℝ)^3119
        have hw : |(5376996971/10000000000 : ℝ)|=(5376996971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_box_1 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16548433/31250000 : ℝ)*x 0 + (-434482059/2000000000 : ℝ)*x 1 + (5376996971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16548433/31250000 : ℝ)^4143 ≤ (2148981217451/5000000000000 : ℝ)^3119 := by
    have hnat : (16548433 : ℕ)^4143*5000000000000^3119 ≤ 2148981217451^3119*31250000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16548433 31250000 2148981217451 5000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (434482059/2000000000 : ℝ)^4143 ≤ (13159912321249/100000000000000 : ℝ)^3119 := by
    have hnat : (434482059 : ℕ)^4143*100000000000000^3119 ≤ 13159912321249^3119*2000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434482059 2000000000 13159912321249 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376996971/10000000000 : ℝ)^4143 ≤ (342659869649/781250000000 : ℝ)^3119 := by
    have hnat : (5376996971 : ℕ)^4143*781250000000^3119 ≤ 342659869649^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376996971 10000000000 342659869649 781250000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16548433/31250000 : ℝ), (-434482059/2000000000 : ℝ), (5376996971/10000000000 : ℝ)] ![(2148981217451/5000000000000 : ℝ), (13159912321249/100000000000000 : ℝ), (342659869649/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16548433/31250000 : ℝ)|^4143 ≤ (2148981217451/5000000000000 : ℝ)^3119
        have hw : |(16548433/31250000 : ℝ)|=(16548433/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-434482059/2000000000 : ℝ)|^4143 ≤ (13159912321249/100000000000000 : ℝ)^3119
        have hw : |(-434482059/2000000000 : ℝ)|=(434482059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376996971/10000000000 : ℝ)|^4143 ≤ (342659869649/781250000000 : ℝ)^3119
        have hw : |(5376996971/10000000000 : ℝ)|=(5376996971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_box_2 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295498709/10000000000 : ℝ)*x 0 + (268849837/500000000 : ℝ)*x 1 + (-2172410407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295498709/10000000000 : ℝ)^4143 ≤ (2686226622211/6250000000000 : ℝ)^3119 := by
    have hnat : (5295498709 : ℕ)^4143*6250000000000^3119 ≤ 2686226622211^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295498709 10000000000 2686226622211 6250000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268849837/500000000 : ℝ)^4143 ≤ (10965115203041/25000000000000 : ℝ)^3119 := by
    have hnat : (268849837 : ℕ)^4143*25000000000000^3119 ≤ 10965115203041^3119*500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268849837 500000000 10965115203041 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2172410407/10000000000 : ℝ)^4143 ≤ (205623644101/1562500000000 : ℝ)^3119 := by
    have hnat : (2172410407 : ℕ)^4143*1562500000000^3119 ≤ 205623644101^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172410407 10000000000 205623644101 1562500000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295498709/10000000000 : ℝ), (268849837/500000000 : ℝ), (-2172410407/10000000000 : ℝ)] ![(2686226622211/6250000000000 : ℝ), (10965115203041/25000000000000 : ℝ), (205623644101/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295498709/10000000000 : ℝ)|^4143 ≤ (2686226622211/6250000000000 : ℝ)^3119
        have hw : |(5295498709/10000000000 : ℝ)|=(5295498709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(268849837/500000000 : ℝ)|^4143 ≤ (10965115203041/25000000000000 : ℝ)^3119
        have hw : |(268849837/500000000 : ℝ)|=(268849837/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2172410407/10000000000 : ℝ)|^4143 ≤ (205623644101/1562500000000 : ℝ)^3119
        have hw : |(-2172410407/10000000000 : ℝ)|=(2172410407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_box_3 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4479703207/10000000000 : ℝ)*x 0 + (4319727849/10000000000 : ℝ)*x 1 + (215986407/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4479703207/10000000000 : ℝ)^4143 ≤ (17207618162601/50000000000000 : ℝ)^3119 := by
    have hnat : (4479703207 : ℕ)^4143*50000000000000^3119 ≤ 17207618162601^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479703207 10000000000 17207618162601 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4319727849/10000000000 : ℝ)^4143 ≤ (16396190180887/50000000000000 : ℝ)^3119 := by
    have hnat : (4319727849 : ℕ)^4143*50000000000000^3119 ≤ 16396190180887^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319727849 10000000000 16396190180887 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215986407/500000000 : ℝ)^4143 ≤ (6558476659221/20000000000000 : ℝ)^3119 := by
    have hnat : (215986407 : ℕ)^4143*20000000000000^3119 ≤ 6558476659221^3119*500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215986407 500000000 6558476659221 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4479703207/10000000000 : ℝ), (4319727849/10000000000 : ℝ), (215986407/500000000 : ℝ)] ![(17207618162601/50000000000000 : ℝ), (16396190180887/50000000000000 : ℝ), (6558476659221/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4479703207/10000000000 : ℝ)|^4143 ≤ (17207618162601/50000000000000 : ℝ)^3119
        have hw : |(4479703207/10000000000 : ℝ)|=(4479703207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4319727849/10000000000 : ℝ)|^4143 ≤ (16396190180887/50000000000000 : ℝ)^3119
        have hw : |(4319727849/10000000000 : ℝ)|=(4319727849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215986407/500000000 : ℝ)|^4143 ≤ (6558476659221/20000000000000 : ℝ)^3119
        have hw : |(215986407/500000000 : ℝ)|=(215986407/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_box_4 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1160231633/5000000000 : ℝ)*x 0 + (5156722/9765625 : ℝ)*x 1 + (5280482909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1160231633/5000000000 : ℝ)^4143 ≤ (3591090165929/25000000000000 : ℝ)^3119 := by
    have hnat : (1160231633 : ℕ)^4143*25000000000000^3119 ≤ 3591090165929^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1160231633 5000000000 3591090165929 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5156722/9765625 : ℝ)^4143 ≤ (4281782191691/10000000000000 : ℝ)^3119 := by
    have hnat : (5156722 : ℕ)^4143*10000000000000^3119 ≤ 4281782191691^3119*9765625^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5156722 9765625 4281782191691 10000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280482909/10000000000 : ℝ)^4143 ≤ (42817817403919/100000000000000 : ℝ)^3119 := by
    have hnat : (5280482909 : ℕ)^4143*100000000000000^3119 ≤ 42817817403919^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280482909 10000000000 42817817403919 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1160231633/5000000000 : ℝ), (5156722/9765625 : ℝ), (5280482909/10000000000 : ℝ)] ![(3591090165929/25000000000000 : ℝ), (4281782191691/10000000000000 : ℝ), (42817817403919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1160231633/5000000000 : ℝ)|^4143 ≤ (3591090165929/25000000000000 : ℝ)^3119
        have hw : |(-1160231633/5000000000 : ℝ)|=(1160231633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5156722/9765625 : ℝ)|^4143 ≤ (4281782191691/10000000000000 : ℝ)^3119
        have hw : |(5156722/9765625 : ℝ)|=(5156722/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280482909/10000000000 : ℝ)|^4143 ≤ (42817817403919/100000000000000 : ℝ)^3119
        have hw : |(5280482909/10000000000 : ℝ)|=(5280482909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_box_5 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363761027/10000000000 : ℝ)*x 0 + (-442045391/2000000000 : ℝ)*x 1 + (330030189/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363761027/10000000000 : ℝ)^4143 ≤ (21858554250839/50000000000000 : ℝ)^3119 := by
    have hnat : (5363761027 : ℕ)^4143*50000000000000^3119 ≤ 21858554250839^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363761027 10000000000 21858554250839 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442045391/2000000000 : ℝ)^4143 ≤ (105195881521/781250000000 : ℝ)^3119 := by
    have hnat : (442045391 : ℕ)^4143*781250000000^3119 ≤ 105195881521^3119*2000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442045391 2000000000 105195881521 781250000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (330030189/625000000 : ℝ)^4143 ≤ (5352227330321/12500000000000 : ℝ)^3119 := by
    have hnat : (330030189 : ℕ)^4143*12500000000000^3119 ≤ 5352227330321^3119*625000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330030189 625000000 5352227330321 12500000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363761027/10000000000 : ℝ), (-442045391/2000000000 : ℝ), (330030189/625000000 : ℝ)] ![(21858554250839/50000000000000 : ℝ), (105195881521/781250000000 : ℝ), (5352227330321/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363761027/10000000000 : ℝ)|^4143 ≤ (21858554250839/50000000000000 : ℝ)^3119
        have hw : |(5363761027/10000000000 : ℝ)|=(5363761027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-442045391/2000000000 : ℝ)|^4143 ≤ (105195881521/781250000000 : ℝ)^3119
        have hw : |(-442045391/2000000000 : ℝ)|=(442045391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(330030189/625000000 : ℝ)|^4143 ≤ (5352227330321/12500000000000 : ℝ)^3119
        have hw : |(330030189/625000000 : ℝ)|=(330030189/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_box_6 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536376087/1000000000 : ℝ)*x 0 + (2640241781/5000000000 : ℝ)*x 1 + (-44204529/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536376087/1000000000 : ℝ)^4143 ≤ (43717106801943/100000000000000 : ℝ)^3119 := by
    have hnat : (536376087 : ℕ)^4143*100000000000000^3119 ≤ 43717106801943^3119*1000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536376087 1000000000 43717106801943 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640241781/5000000000 : ℝ)^4143 ≤ (42817824437291/100000000000000 : ℝ)^3119 := by
    have hnat : (2640241781 : ℕ)^4143*100000000000000^3119 ≤ 42817824437291^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640241781 5000000000 42817824437291 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44204529/200000000 : ℝ)^4143 ≤ (6732534374041/50000000000000 : ℝ)^3119 := by
    have hnat : (44204529 : ℕ)^4143*50000000000000^3119 ≤ 6732534374041^3119*200000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44204529 200000000 6732534374041 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536376087/1000000000 : ℝ), (2640241781/5000000000 : ℝ), (-44204529/200000000 : ℝ)] ![(43717106801943/100000000000000 : ℝ), (42817824437291/100000000000000 : ℝ), (6732534374041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536376087/1000000000 : ℝ)|^4143 ≤ (43717106801943/100000000000000 : ℝ)^3119
        have hw : |(536376087/1000000000 : ℝ)|=(536376087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640241781/5000000000 : ℝ)|^4143 ≤ (42817824437291/100000000000000 : ℝ)^3119
        have hw : |(2640241781/5000000000 : ℝ)|=(2640241781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44204529/200000000 : ℝ)|^4143 ≤ (6732534374041/50000000000000 : ℝ)^3119
        have hw : |(-44204529/200000000 : ℝ)|=(44204529/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_box_7 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2131602747/5000000000 : ℝ)*x 0 + (1106988901/2500000000 : ℝ)*x 1 + (276747227/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131602747/5000000000 : ℝ)^4143 ≤ (16111829346353/50000000000000 : ℝ)^3119 := by
    have hnat : (2131602747 : ℕ)^4143*50000000000000^3119 ≤ 16111829346353^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131602747 5000000000 16111829346353 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1106988901/2500000000 : ℝ)^4143 ≤ (4236021313111/12500000000000 : ℝ)^3119 := by
    have hnat : (1106988901 : ℕ)^4143*12500000000000^3119 ≤ 4236021313111^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106988901 2500000000 4236021313111 12500000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276747227/625000000 : ℝ)^4143 ≤ (8472042697383/25000000000000 : ℝ)^3119 := by
    have hnat : (276747227 : ℕ)^4143*25000000000000^3119 ≤ 8472042697383^3119*625000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276747227 625000000 8472042697383 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2131602747/5000000000 : ℝ), (1106988901/2500000000 : ℝ), (276747227/625000000 : ℝ)] ![(16111829346353/50000000000000 : ℝ), (4236021313111/12500000000000 : ℝ), (8472042697383/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2131602747/5000000000 : ℝ)|^4143 ≤ (16111829346353/50000000000000 : ℝ)^3119
        have hw : |(2131602747/5000000000 : ℝ)|=(2131602747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1106988901/2500000000 : ℝ)|^4143 ≤ (4236021313111/12500000000000 : ℝ)^3119
        have hw : |(1106988901/2500000000 : ℝ)|=(1106988901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(276747227/625000000 : ℝ)|^4143 ≤ (8472042697383/25000000000000 : ℝ)^3119
        have hw : |(276747227/625000000 : ℝ)|=(276747227/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_box_8 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1133237783/5000000000 : ℝ)*x 0 + (2607470007/5000000000 : ℝ)*x 1 + (269330029/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1133237783/5000000000 : ℝ)^4143 ≤ (6961071855779/50000000000000 : ℝ)^3119 := by
    have hnat : (1133237783 : ℕ)^4143*50000000000000^3119 ≤ 6961071855779^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133237783 5000000000 6961071855779 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607470007/5000000000 : ℝ)^4143 ≤ (42113306385081/100000000000000 : ℝ)^3119 := by
    have hnat : (2607470007 : ℕ)^4143*100000000000000^3119 ≤ 42113306385081^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607470007 5000000000 42113306385081 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269330029/500000000 : ℝ)^4143 ≤ (43964549888817/100000000000000 : ℝ)^3119 := by
    have hnat : (269330029 : ℕ)^4143*100000000000000^3119 ≤ 43964549888817^3119*500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269330029 500000000 43964549888817 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1133237783/5000000000 : ℝ), (2607470007/5000000000 : ℝ), (269330029/500000000 : ℝ)] ![(6961071855779/50000000000000 : ℝ), (42113306385081/100000000000000 : ℝ), (43964549888817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1133237783/5000000000 : ℝ)|^4143 ≤ (6961071855779/50000000000000 : ℝ)^3119
        have hw : |(-1133237783/5000000000 : ℝ)|=(1133237783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607470007/5000000000 : ℝ)|^4143 ≤ (42113306385081/100000000000000 : ℝ)^3119
        have hw : |(2607470007/5000000000 : ℝ)|=(2607470007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269330029/500000000 : ℝ)|^4143 ≤ (43964549888817/100000000000000 : ℝ)^3119
        have hw : |(269330029/500000000 : ℝ)|=(269330029/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_box_9 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661087813/1250000000 : ℝ)*x 0 + (-1084288317/5000000000 : ℝ)*x 1 + (1346650249/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661087813/1250000000 : ℝ)^4143 ≤ (21453186068879/50000000000000 : ℝ)^3119 := by
    have hnat : (661087813 : ℕ)^4143*50000000000000^3119 ≤ 21453186068879^3119*1250000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661087813 1250000000 21453186068879 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084288317/5000000000 : ℝ)^4143 ≤ (13129073445857/100000000000000 : ℝ)^3119 := by
    have hnat : (1084288317 : ℕ)^4143*100000000000000^3119 ≤ 13129073445857^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084288317 5000000000 13129073445857 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346650249/2500000000 : ℝ)^4143 ≤ (43964554398861/100000000000000 : ℝ)^3119 := by
    have hnat : (1346650249 : ℕ)^4143*100000000000000^3119 ≤ 43964554398861^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346650249 2500000000 43964554398861 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661087813/1250000000 : ℝ), (-1084288317/5000000000 : ℝ), (1346650249/2500000000 : ℝ)] ![(21453186068879/50000000000000 : ℝ), (13129073445857/100000000000000 : ℝ), (43964554398861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661087813/1250000000 : ℝ)|^4143 ≤ (21453186068879/50000000000000 : ℝ)^3119
        have hw : |(661087813/1250000000 : ℝ)|=(661087813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1084288317/5000000000 : ℝ)|^4143 ≤ (13129073445857/100000000000000 : ℝ)^3119
        have hw : |(-1084288317/5000000000 : ℝ)|=(1084288317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346650249/2500000000 : ℝ)|^4143 ≤ (43964554398861/100000000000000 : ℝ)^3119
        have hw : |(1346650249/2500000000 : ℝ)|=(1346650249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_box_10 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644351253/5000000000 : ℝ)*x 0 + (538660051/1000000000 : ℝ)*x 1 + (-271072161/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644351253/5000000000 : ℝ)^4143 ≤ (42906372159311/100000000000000 : ℝ)^3119 := by
    have hnat : (2644351253 : ℕ)^4143*100000000000000^3119 ≤ 42906372159311^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644351253 5000000000 42906372159311 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538660051/1000000000 : ℝ)^4143 ≤ (8792909825983/20000000000000 : ℝ)^3119 := by
    have hnat : (538660051 : ℕ)^4143*20000000000000^3119 ≤ 8792909825983^3119*1000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538660051 1000000000 8792909825983 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271072161/1250000000 : ℝ)^4143 ≤ (6564539352631/50000000000000 : ℝ)^3119 := by
    have hnat : (271072161 : ℕ)^4143*50000000000000^3119 ≤ 6564539352631^3119*1250000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271072161 1250000000 6564539352631 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644351253/5000000000 : ℝ), (538660051/1000000000 : ℝ), (-271072161/1250000000 : ℝ)] ![(42906372159311/100000000000000 : ℝ), (8792909825983/20000000000000 : ℝ), (6564539352631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644351253/5000000000 : ℝ)|^4143 ≤ (42906372159311/100000000000000 : ℝ)^3119
        have hw : |(2644351253/5000000000 : ℝ)|=(2644351253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538660051/1000000000 : ℝ)|^4143 ≤ (8792909825983/20000000000000 : ℝ)^3119
        have hw : |(538660051/1000000000 : ℝ)|=(538660051/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-271072161/1250000000 : ℝ)|^4143 ≤ (6564539352631/50000000000000 : ℝ)^3119
        have hw : |(-271072161/1250000000 : ℝ)|=(271072161/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_box_11 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4500973453/10000000000 : ℝ)*x 0 + (538619037/1250000000 : ℝ)*x 1 + (2154476197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4500973453/10000000000 : ℝ)^4143 ≤ (34632462221439/100000000000000 : ℝ)^3119 := by
    have hnat : (4500973453 : ℕ)^4143*100000000000000^3119 ≤ 34632462221439^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500973453 10000000000 34632462221439 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538619037/1250000000 : ℝ)^4143 ≤ (2042735524197/6250000000000 : ℝ)^3119 := by
    have hnat : (538619037 : ℕ)^4143*6250000000000^3119 ≤ 2042735524197^3119*1250000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538619037 1250000000 2042735524197 6250000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2154476197/5000000000 : ℝ)^4143 ≤ (4085471171817/12500000000000 : ℝ)^3119 := by
    have hnat : (2154476197 : ℕ)^4143*12500000000000^3119 ≤ 4085471171817^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154476197 5000000000 4085471171817 12500000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4500973453/10000000000 : ℝ), (538619037/1250000000 : ℝ), (2154476197/5000000000 : ℝ)] ![(34632462221439/100000000000000 : ℝ), (2042735524197/6250000000000 : ℝ), (4085471171817/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4500973453/10000000000 : ℝ)|^4143 ≤ (34632462221439/100000000000000 : ℝ)^3119
        have hw : |(4500973453/10000000000 : ℝ)|=(4500973453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538619037/1250000000 : ℝ)|^4143 ≤ (2042735524197/6250000000000 : ℝ)^3119
        have hw : |(538619037/1250000000 : ℝ)|=(538619037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2154476197/5000000000 : ℝ)|^4143 ≤ (4085471171817/12500000000000 : ℝ)^3119
        have hw : |(2154476197/5000000000 : ℝ)|=(2154476197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_box_12 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2116349467/10000000000 : ℝ)*x 0 + (340076607/625000000 : ℝ)*x 1 + (1054493641/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116349467/10000000000 : ℝ)^4143 ≤ (12710737121159/100000000000000 : ℝ)^3119 := by
    have hnat : (2116349467 : ℕ)^4143*100000000000000^3119 ≤ 12710737121159^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116349467 10000000000 12710737121159 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340076607/625000000 : ℝ)^4143 ≤ (44557749211687/100000000000000 : ℝ)^3119 := by
    have hnat : (340076607 : ℕ)^4143*100000000000000^3119 ≤ 44557749211687^3119*625000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340076607 625000000 44557749211687 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054493641/2000000000 : ℝ)^4143 ≤ (42731513652483/100000000000000 : ℝ)^3119 := by
    have hnat : (1054493641 : ℕ)^4143*100000000000000^3119 ≤ 42731513652483^3119*2000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054493641 2000000000 42731513652483 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2116349467/10000000000 : ℝ), (340076607/625000000 : ℝ), (1054493641/2000000000 : ℝ)] ![(12710737121159/100000000000000 : ℝ), (44557749211687/100000000000000 : ℝ), (42731513652483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2116349467/10000000000 : ℝ)|^4143 ≤ (12710737121159/100000000000000 : ℝ)^3119
        have hw : |(-2116349467/10000000000 : ℝ)|=(2116349467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340076607/625000000 : ℝ)|^4143 ≤ (44557749211687/100000000000000 : ℝ)^3119
        have hw : |(340076607/625000000 : ℝ)|=(340076607/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054493641/2000000000 : ℝ)|^4143 ≤ (42731513652483/100000000000000 : ℝ)^3119
        have hw : |(1054493641/2000000000 : ℝ)|=(1054493641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_box_13 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073885591/2000000000 : ℝ)*x 0 + (-2213308499/10000000000 : ℝ)*x 1 + (527246819/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073885591/2000000000 : ℝ)^4143 ≤ (4377847121563/10000000000000 : ℝ)^3119 := by
    have hnat : (1073885591 : ℕ)^4143*10000000000000^3119 ≤ 4377847121563^3119*2000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073885591 2000000000 4377847121563 10000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2213308499/10000000000 : ℝ)^4143 ≤ (2698003057067/20000000000000 : ℝ)^3119 := by
    have hnat : (2213308499 : ℕ)^4143*20000000000000^3119 ≤ 2698003057067^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213308499 10000000000 2698003057067 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527246819/1000000000 : ℝ)^4143 ≤ (42731513491001/100000000000000 : ℝ)^3119 := by
    have hnat : (527246819 : ℕ)^4143*100000000000000^3119 ≤ 42731513491001^3119*1000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527246819 1000000000 42731513491001 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073885591/2000000000 : ℝ), (-2213308499/10000000000 : ℝ), (527246819/1000000000 : ℝ)] ![(4377847121563/10000000000000 : ℝ), (2698003057067/20000000000000 : ℝ), (42731513491001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073885591/2000000000 : ℝ)|^4143 ≤ (4377847121563/10000000000000 : ℝ)^3119
        have hw : |(1073885591/2000000000 : ℝ)|=(1073885591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2213308499/10000000000 : ℝ)|^4143 ≤ (2698003057067/20000000000000 : ℝ)^3119
        have hw : |(-2213308499/10000000000 : ℝ)|=(2213308499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527246819/1000000000 : ℝ)|^4143 ≤ (42731513491001/100000000000000 : ℝ)^3119
        have hw : |(527246819/1000000000 : ℝ)|=(527246819/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_box_14 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369427827/10000000000 : ℝ)*x 0 + (210898717/400000000 : ℝ)*x 1 + (-2213309023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369427827/10000000000 : ℝ)^4143 ≤ (43778469829379/100000000000000 : ℝ)^3119 := by
    have hnat : (5369427827 : ℕ)^4143*100000000000000^3119 ≤ 43778469829379^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369427827 10000000000 43778469829379 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210898717/400000000 : ℝ)^4143 ≤ (8546302127629/20000000000000 : ℝ)^3119 := by
    have hnat : (210898717 : ℕ)^4143*20000000000000^3119 ≤ 8546302127629^3119*400000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210898717 400000000 8546302127629 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2213309023/10000000000 : ℝ)^4143 ≤ (6745009763817/50000000000000 : ℝ)^3119 := by
    have hnat : (2213309023 : ℕ)^4143*50000000000000^3119 ≤ 6745009763817^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213309023 10000000000 6745009763817 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369427827/10000000000 : ℝ), (210898717/400000000 : ℝ), (-2213309023/10000000000 : ℝ)] ![(43778469829379/100000000000000 : ℝ), (8546302127629/20000000000000 : ℝ), (6745009763817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369427827/10000000000 : ℝ)|^4143 ≤ (43778469829379/100000000000000 : ℝ)^3119
        have hw : |(5369427827/10000000000 : ℝ)|=(5369427827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210898717/400000000 : ℝ)|^4143 ≤ (8546302127629/20000000000000 : ℝ)^3119
        have hw : |(210898717/400000000 : ℝ)|=(210898717/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2213309023/10000000000 : ℝ)|^4143 ≤ (6745009763817/50000000000000 : ℝ)^3119
        have hw : |(-2213309023/10000000000 : ℝ)|=(2213309023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_box_15 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (848999243/2000000000 : ℝ)*x 0 + (2218469069/5000000000 : ℝ)*x 1 + (554617313/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848999243/2000000000 : ℝ)^4143 ≤ (16020481988417/50000000000000 : ℝ)^3119 := by
    have hnat : (848999243 : ℕ)^4143*50000000000000^3119 ≤ 16020481988417^3119*2000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848999243 2000000000 16020481988417 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2218469069/5000000000 : ℝ)^4143 ≤ (6795903229119/20000000000000 : ℝ)^3119 := by
    have hnat : (2218469069 : ℕ)^4143*20000000000000^3119 ≤ 6795903229119^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218469069 5000000000 6795903229119 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554617313/1250000000 : ℝ)^4143 ≤ (33979519868779/100000000000000 : ℝ)^3119 := by
    have hnat : (554617313 : ℕ)^4143*100000000000000^3119 ≤ 33979519868779^3119*1250000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554617313 1250000000 33979519868779 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(848999243/2000000000 : ℝ), (2218469069/5000000000 : ℝ), (554617313/1250000000 : ℝ)] ![(16020481988417/50000000000000 : ℝ), (6795903229119/20000000000000 : ℝ), (33979519868779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(848999243/2000000000 : ℝ)|^4143 ≤ (16020481988417/50000000000000 : ℝ)^3119
        have hw : |(848999243/2000000000 : ℝ)|=(848999243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2218469069/5000000000 : ℝ)|^4143 ≤ (6795903229119/20000000000000 : ℝ)^3119
        have hw : |(2218469069/5000000000 : ℝ)|=(2218469069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(554617313/1250000000 : ℝ)|^4143 ≤ (33979519868779/100000000000000 : ℝ)^3119
        have hw : |(554617313/1250000000 : ℝ)|=(554617313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1093_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14019/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11289/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31113/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59261/100000 : ℝ) ∧ (79657/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41507/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14019/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11289/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14019/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11289/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14019/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11289/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14019/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11289/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14019/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11289/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14019/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11289/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11289/100000 : ℝ) ^ (8285/2048 : ℝ) ≤ (7354833296125667/50000000000000000000 : ℝ) := by
    have hpowers : (11289/100000 : ℝ)^8285 ≤ (7354833296125667/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11289 : ℕ)^8285*50000000000000000000^2048 ≤ 7354833296125667^2048*100000^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11289 100000 7354833296125667 50000000000000000000 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11289/100000 : ℝ)) (X := (7354833296125667/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14019/100000 : ℝ) ^ (8285/2048 : ℝ) ≤ (1104003504304423/3125000000000000000 : ℝ) := by
    have hpowers : (14019/100000 : ℝ)^8285 ≤ (1104003504304423/3125000000000000000 : ℝ)^2048 := by
      have hnat : (14019 : ℕ)^8285*3125000000000000000^2048 ≤ 1104003504304423^2048*100000^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14019 100000 1104003504304423 3125000000000000000 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14019/100000 : ℝ)) (X := (1104003504304423/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007354833296125667/25000000000000000000 : ℝ) ≤ (1250090893366957/1250000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (25007354833296125667/25000000000000000000 : ℝ)^2048 ≤ (1250090893366957/1250000000000000 : ℝ)^8285 := by
      have hnat : (25007354833296125667 : ℕ)^2048*1250000000000000^8285 ≤ 1250090893366957^8285*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007354833296125667 25000000000000000000 1250090893366957 1250000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250090893366957/1250000000000000 : ℝ)) (X := (25007354833296125667/25000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005003777872999287/10000000000000000000 : ℝ) ≤ (10001236669589687/10000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (10005003777872999287/10000000000000000000 : ℝ)^2048 ≤ (10001236669589687/10000000000000000 : ℝ)^8285 := by
      have hnat : (10005003777872999287 : ℕ)^2048*10000000000000000^8285 ≤ 10001236669589687^8285*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005003777872999287 10000000000000000000 10001236669589687 10000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001236669589687/10000000000000000 : ℝ)) (X := (10005003777872999287/10000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563604003504304423/1562500000000000000 : ℝ) ≤ (5000873096121859/5000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (1563604003504304423/1562500000000000000 : ℝ)^2048 ≤ (5000873096121859/5000000000000000 : ℝ)^8285 := by
      have hnat : (1563604003504304423 : ℕ)^2048*5000000000000000^8285 ≤ 5000873096121859^8285*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563604003504304423 1562500000000000000 5000873096121859 5000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000873096121859/5000000000000000 : ℝ)) (X := (1563604003504304423/1562500000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7354833296125667/50000000000000000000 : ℝ) ≤ ((4548413518108604827/4550000000000000000 : ℝ)+2*(169840884677/91000000000000 : ℝ)*(11289/100000 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (4548413518108604827/4550000000000000000 : ℝ)+2*(169840884677/91000000000000 : ℝ)*(11289/100000 : ℝ)=(1250090893366957/1250000000000000 : ℝ) by norm_num, show 1+2*(7354833296125667/50000000000000000000 : ℝ)=(25007354833296125667/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1104003504304423/3125000000000000000 : ℝ)+(7354833296125667/50000000000000000000 : ℝ) ≤ ((4548413518108604827/4550000000000000000 : ℝ)+(169840884677/91000000000000 : ℝ)*((14019/100000 : ℝ)+(11289/100000 : ℝ)))^(8285/2048 : ℝ) := by
    rw [show (4548413518108604827/4550000000000000000 : ℝ)+(169840884677/91000000000000 : ℝ)*((14019/100000 : ℝ)+(11289/100000 : ℝ))=(10001236669589687/10000000000000000 : ℝ) by norm_num, show 1+(1104003504304423/3125000000000000000 : ℝ)+(7354833296125667/50000000000000000000 : ℝ)=(10005003777872999287/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1104003504304423/3125000000000000000 : ℝ) ≤ ((4548413518108604827/4550000000000000000 : ℝ)+2*(169840884677/91000000000000 : ℝ)*(14019/100000 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (4548413518108604827/4550000000000000000 : ℝ)+2*(169840884677/91000000000000 : ℝ)*(14019/100000 : ℝ)=(5000873096121859/5000000000000000 : ℝ) by norm_num, show 1+2*(1104003504304423/3125000000000000000 : ℝ)=(1563604003504304423/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4548413518108604827/4550000000000000000 : ℝ)*(X 1 0+X 2 0)+(169840884677/91000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (11289/100000 : ℝ)) (hi := (14019/100000 : ℝ)) (c := (4548413518108604827/4550000000000000000 : ℝ)) (alpha := (169840884677/91000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4548413518108604827/4550000000000000000 : ℝ)*(X 0 1+X 2 1)+(169840884677/91000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (11289/100000 : ℝ)) (hi := (14019/100000 : ℝ)) (c := (4548413518108604827/4550000000000000000 : ℝ)) (alpha := (169840884677/91000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4548413518108604827/4550000000000000000 : ℝ)*(X 0 2+X 1 2)+(169840884677/91000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (11289/100000 : ℝ)) (hi := (14019/100000 : ℝ)) (c := (4548413518108604827/4550000000000000000 : ℝ)) (alpha := (169840884677/91000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1031005539/5000000000 : ℝ)*X 0 0+(2688498443/5000000000 : ℝ)*X 0 1+(5376996971/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((16548433/31250000 : ℝ)*X 1 0+(-434482059/2000000000 : ℝ)*X 1 1+(5376996971/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295498709/10000000000 : ℝ)*X 2 0+(268849837/500000000 : ℝ)*X 2 1+(-2172410407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4479703207/10000000000 : ℝ)*X 0 0+(4319727849/10000000000 : ℝ)*X 0 1+(215986407/500000000 : ℝ)*X 0 2+(4479703207/10000000000 : ℝ)*X 1 0+(4319727849/10000000000 : ℝ)*X 1 1+(215986407/500000000 : ℝ)*X 1 2+(4479703207/10000000000 : ℝ)*X 2 0+(4319727849/10000000000 : ℝ)*X 2 1+(215986407/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1160231633/5000000000 : ℝ)*X 0 0+(5156722/9765625 : ℝ)*X 0 1+(5280482909/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363761027/10000000000 : ℝ)*X 1 0+(-442045391/2000000000 : ℝ)*X 1 1+(330030189/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((536376087/1000000000 : ℝ)*X 2 0+(2640241781/5000000000 : ℝ)*X 2 1+(-44204529/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2131602747/5000000000 : ℝ)*X 0 0+(1106988901/2500000000 : ℝ)*X 0 1+(276747227/625000000 : ℝ)*X 0 2+(2131602747/5000000000 : ℝ)*X 1 0+(1106988901/2500000000 : ℝ)*X 1 1+(276747227/625000000 : ℝ)*X 1 2+(2131602747/5000000000 : ℝ)*X 2 0+(1106988901/2500000000 : ℝ)*X 2 1+(276747227/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1133237783/5000000000 : ℝ)*X 0 0+(2607470007/5000000000 : ℝ)*X 0 1+(269330029/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((661087813/1250000000 : ℝ)*X 1 0+(-1084288317/5000000000 : ℝ)*X 1 1+(1346650249/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644351253/5000000000 : ℝ)*X 2 0+(538660051/1000000000 : ℝ)*X 2 1+(-271072161/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4500973453/10000000000 : ℝ)*X 0 0+(538619037/1250000000 : ℝ)*X 0 1+(2154476197/5000000000 : ℝ)*X 0 2+(4500973453/10000000000 : ℝ)*X 1 0+(538619037/1250000000 : ℝ)*X 1 1+(2154476197/5000000000 : ℝ)*X 1 2+(4500973453/10000000000 : ℝ)*X 2 0+(538619037/1250000000 : ℝ)*X 2 1+(2154476197/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2116349467/10000000000 : ℝ)*X 0 0+(340076607/625000000 : ℝ)*X 0 1+(1054493641/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1073885591/2000000000 : ℝ)*X 1 0+(-2213308499/10000000000 : ℝ)*X 1 1+(527246819/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369427827/10000000000 : ℝ)*X 2 0+(210898717/400000000 : ℝ)*X 2 1+(-2213309023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((848999243/2000000000 : ℝ)*X 0 0+(2218469069/5000000000 : ℝ)*X 0 1+(554617313/1250000000 : ℝ)*X 0 2+(848999243/2000000000 : ℝ)*X 1 0+(2218469069/5000000000 : ℝ)*X 1 1+(554617313/1250000000 : ℝ)*X 1 2+(848999243/2000000000 : ℝ)*X 2 0+(2218469069/5000000000 : ℝ)*X 2 1+(554617313/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31113/50000 : ℝ) ≤ (-63196046437045939571697383937/101562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (7969729/50000000000000 : ℝ)*(upper1) + (64255747/50000000000000 : ℝ)*(upper4) + (1055461/625000000000 : ℝ)*(upper5) + (12123381680089/312500000000 : ℝ)*(major0) + (12123381680089/312500000000 : ℝ)*(major1) + (12123381680089/312500000000 : ℝ)*(major2) + (4769481781/25000000000000 : ℝ)*(sp1) + (1844029159/25000000000000 : ℝ)*(sp3) + (2583780855219529/50000000000000 : ℝ)*(sp4) + (645945885756883/12500000000000 : ℝ)*(sp5) + (2583723016204763/50000000000000 : ℝ)*(sp6) + (81628500052533/3125000000000 : ℝ)*(sp7) + (24453543131/100000000000000 : ℝ)*(sp8) + (70065786331/50000000000000 : ℝ)*(sp14) + (653029844449423/25000000000000 : ℝ)*(f.failure) + (1291896540995547/25000000000000 : ℝ)*(f.sum) + (1177469441243/227500000000000000000000000 : ℝ)*base65 + (9730997789441647/1421875000000000000000000000000 : ℝ)*base68 + (487566407308353/1421875000000000000000000000000 : ℝ)*base69 + (1227246612777103/1421875000000000000000000000000 : ℝ)*base71 + (133443508743/56875000000000000000000000 : ℝ)*base74 + (20204281553277103/1421875000000000000000000000000 : ℝ)*base75 + (1791473733620853/1421875000000000000000000000000 : ℝ)*base77 + (1542859171691647/1421875000000000000000000000000 : ℝ)*base80 + (1873287344933/227500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (7155137/1250000000000000000000 : ℝ)*base90 + (7155137/1250000000000000000000 : ℝ)*base92 + (7155137/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59261/100000 : ℝ) ≤ (5185560563098340420421170148951/8750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29643229/50000000000000 : ℝ)*(upper0) + (34851859/50000000000000 : ℝ)*(upper2) + (48862687/100000000000000 : ℝ)*(upper4) + (14677093/100000000000000 : ℝ)*(upper5) + (3942816054214323/100000000000000 : ℝ)*(major0) + (3942816054214323/100000000000000 : ℝ)*(major1) + (3942816054214323/100000000000000 : ℝ)*(major2) + (5211108058434401/100000000000000 : ℝ)*(sp0) + (2605553764142917/50000000000000 : ℝ)*(sp1) + (2605519487768251/50000000000000 : ℝ)*(sp2) + (1327381574773907/50000000000000 : ℝ)*(sp3) + (3457082071/50000000000000 : ℝ)*(sp5) + (37733456737/50000000000000 : ℝ)*(sp10) + (255360623/4000000000000 : ℝ)*(sp12) + (1327381574773907/50000000000000 : ℝ)*(f.failure) + (651389305306247/12500000000000 : ℝ)*(f.sum) + (1828336897417/350000000000000000000000000 : ℝ)*base65 + (235840695512008683/35000000000000000000000000000000 : ℝ)*base68 + (343688520702008683/35000000000000000000000000000000 : ℝ)*base70 + (79107916512008683/35000000000000000000000000000000 : ℝ)*base72 + (2122558534567/350000000000000000000000000 : ℝ)*base73 + (295711989862008683/35000000000000000000000000000000 : ℝ)*base76 + (40016372407991317/35000000000000000000000000000000 : ℝ)*base77 + (77239439202008683/35000000000000000000000000000000 : ℝ)*base80 + (927389843767/350000000000000000000000000 : ℝ)*base81 + (3619133/2500000000000000000000 : ℝ)*base90 + (3619133/2500000000000000000000 : ℝ)*base92 + (3619133/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79657/100000 : ℝ) ≤ (809040259547430934178325758661/1015625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4295041/3125000000000 : ℝ)*(upper0) + (18046203/100000000000000 : ℝ)*(lower1) + (158821273/100000000000000 : ℝ)*(upper2) + (208556917/50000000000000 : ℝ)*(lower5) + (17230391685213/390625000000 : ℝ)*(major0) + (17230391685213/390625000000 : ℝ)*(major1) + (17230391685213/390625000000 : ℝ)*(major2) + (1871784399/100000000000000 : ℝ)*(sp0) + (117705297159/50000000000000 : ℝ)*(sp1) + (25257804059/25000000000000 : ℝ)*(sp3) + (5825419707937139/100000000000000 : ℝ)*(sp8) + (291259308456361/5000000000000 : ℝ)*(sp9) + (5825421579721537/100000000000000 : ℝ)*(sp10) + (1484942407840241/50000000000000 : ℝ)*(sp11) + (1484992923448359/50000000000000 : ℝ)*(f.failure) + (5825421579721537/100000000000000 : ℝ)*(f.sum) + (1294526296727/162500000000000000000000000 : ℝ)*base65 + (1763943005330093/253906250000000000000000000000 : ℝ)*base67 + (2062201356242247/1015625000000000000000000000000 : ℝ)*base69 + (2671892041675811/507812500000000000000000000000 : ℝ)*base71 + (678575515827/162500000000000000000000000 : ℝ)*base73 + (1249700832925811/507812500000000000000000000000 : ℝ)*base75 + (4917971413298843/253906250000000000000000000000 : ℝ)*base77 + (13030875369417939/507812500000000000000000000000 : ℝ)*base80 + (105559367699/81250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (20030121/2500000000000000000000 : ℝ)*base90 + (20030121/2500000000000000000000 : ℝ)*base92 + (20030121/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-41507/50000 : ℝ) ≤ (-23606378709505333764063808346949/28437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57540577/100000000000000 : ℝ)*(lower0) + (206117/5000000000000 : ℝ)*(upper3) + (331888211/100000000000000 : ℝ)*(lower4) + (555710183732971/12500000000000 : ℝ)*(major0) + (555710183732971/12500000000000 : ℝ)*(major1) + (555710183732971/12500000000000 : ℝ)*(major2) + (5687887581/50000000000000 : ℝ)*(sp0) + (164595347049/100000000000000 : ℝ)*(sp5) + (616405719081/100000000000000 : ℝ)*(sp6) + (16881185537/12500000000000 : ℝ)*(sp7) + (2962835653861647/50000000000000 : ℝ)*(sp12) + (370344880509463/6250000000000 : ℝ)*(sp13) + (370316642361211/6250000000000 : ℝ)*(sp14) + (748303921820847/25000000000000 : ℝ)*(sp15) + (748337684191921/25000000000000 : ℝ)*(f.failure) + (5925682683498457/100000000000000 : ℝ)*(f.sum) + (6234114624391/1137500000000000000000000000 : ℝ)*base66 + (647545369019498983/56875000000000000000000000000000 : ℝ)*base68 + (104637823650501017/56875000000000000000000000000000 : ℝ)*base69 + (671577412225123983/56875000000000000000000000000000 : ℝ)*base72 + (27630772624307/2275000000000000000000000000 : ℝ)*base74 + (396590524651998983/56875000000000000000000000000000 : ℝ)*base76 + (830132767080748983/56875000000000000000000000000000 : ℝ)*base78 + (103632304704251017/56875000000000000000000000000000 : ℝ)*base79 + (1685086977591/1137500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (19468801/1250000000000000000000 : ℝ)*base89 + (19468801/1250000000000000000000 : ℝ)*base91 + (19468801/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1093_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14019/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11289/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59261/100000 : ℝ) else (79657/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41507/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1093_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1093_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14019/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11289/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59261/100000 : ℝ) else (79657/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41507/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1093_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14019/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11289/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59261/100000 : ℝ) else (79657/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41507/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1093_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

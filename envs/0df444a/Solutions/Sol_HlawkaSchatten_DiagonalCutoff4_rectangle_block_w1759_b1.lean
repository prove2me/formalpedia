-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1759_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:24:57.443058+00:00
-- url     : https://prove2.me/submissions/3b3b9c2e-5b65-48a9-ba06-05a46809dfa7

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
theorem support_rectangle_w1759_s3_0 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1066004871/2000000000 : ℝ)*x 0 + (1016701201/2000000000 : ℝ)*x 1 + (-691783761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066004871/2000000000 : ℝ)^5919 ≤ (23363227782909/50000000000000 : ℝ)^4895 := by
    have hnat : (1066004871 : ℕ)^5919*50000000000000^4895 ≤ 23363227782909^4895*2000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066004871 2000000000 23363227782909 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016701201/2000000000 : ℝ)^5919 ≤ (22063009760527/50000000000000 : ℝ)^4895 := by
    have hnat : (1016701201 : ℕ)^5919*50000000000000^4895 ≤ 22063009760527^4895*2000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016701201 2000000000 22063009760527 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (691783761/5000000000 : ℝ)^5919 ≤ (4573762450137/50000000000000 : ℝ)^4895 := by
    have hnat : (691783761 : ℕ)^5919*50000000000000^4895 ≤ 4573762450137^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691783761 5000000000 4573762450137 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1066004871/2000000000 : ℝ), (1016701201/2000000000 : ℝ), (-691783761/5000000000 : ℝ)] ![(23363227782909/50000000000000 : ℝ), (22063009760527/50000000000000 : ℝ), (4573762450137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1066004871/2000000000 : ℝ)|^5919 ≤ (23363227782909/50000000000000 : ℝ)^4895
        have hw : |(1066004871/2000000000 : ℝ)|=(1066004871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1016701201/2000000000 : ℝ)|^5919 ≤ (22063009760527/50000000000000 : ℝ)^4895
        have hw : |(1016701201/2000000000 : ℝ)|=(1016701201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-691783761/5000000000 : ℝ)|^5919 ≤ (4573762450137/50000000000000 : ℝ)^4895
        have hw : |(-691783761/5000000000 : ℝ)|=(691783761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s3_1 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1174116271/10000000000 : ℝ)*x 0 + (1018026701/2000000000 : ℝ)*x 1 + (1095677203/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1174116271/10000000000 : ℝ)^5919 ≤ (7500688533563/100000000000000 : ℝ)^4895 := by
    have hnat : (1174116271 : ℕ)^5919*100000000000000^4895 ≤ 7500688533563^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174116271 10000000000 7500688533563 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1018026701/2000000000 : ℝ)^5919 ≤ (22097795880843/50000000000000 : ℝ)^4895 := by
    have hnat : (1018026701 : ℕ)^5919*50000000000000^4895 ≤ 22097795880843^4895*2000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018026701 2000000000 22097795880843 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095677203/2000000000 : ℝ)^5919 ≤ (48303719695697/100000000000000 : ℝ)^4895 := by
    have hnat : (1095677203 : ℕ)^5919*100000000000000^4895 ≤ 48303719695697^4895*2000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095677203 2000000000 48303719695697 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1174116271/10000000000 : ℝ), (1018026701/2000000000 : ℝ), (1095677203/2000000000 : ℝ)] ![(7500688533563/100000000000000 : ℝ), (22097795880843/50000000000000 : ℝ), (48303719695697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1174116271/10000000000 : ℝ)|^5919 ≤ (7500688533563/100000000000000 : ℝ)^4895
        have hw : |(-1174116271/10000000000 : ℝ)|=(1174116271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1018026701/2000000000 : ℝ)|^5919 ≤ (22097795880843/50000000000000 : ℝ)^4895
        have hw : |(1018026701/2000000000 : ℝ)|=(1018026701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1095677203/2000000000 : ℝ)|^5919 ≤ (48303719695697/100000000000000 : ℝ)^4895
        have hw : |(1095677203/2000000000 : ℝ)|=(1095677203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s3_2 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5223846297/10000000000 : ℝ)*x 0 + (-98868731/1000000000 : ℝ)*x 1 + (1369596499/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5223846297/10000000000 : ℝ)^5919 ≤ (22801632554873/50000000000000 : ℝ)^4895 := by
    have hnat : (5223846297 : ℕ)^5919*50000000000000^4895 ≤ 22801632554873^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223846297 10000000000 22801632554873 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98868731/1000000000 : ℝ)^5919 ≤ (6093015382297/100000000000000 : ℝ)^4895 := by
    have hnat : (98868731 : ℕ)^5919*100000000000000^4895 ≤ 6093015382297^4895*1000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98868731 1000000000 6093015382297 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369596499/2500000000 : ℝ)^5919 ≤ (24151859746563/50000000000000 : ℝ)^4895 := by
    have hnat : (1369596499 : ℕ)^5919*50000000000000^4895 ≤ 24151859746563^4895*2500000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369596499 2500000000 24151859746563 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5223846297/10000000000 : ℝ), (-98868731/1000000000 : ℝ), (1369596499/2500000000 : ℝ)] ![(22801632554873/50000000000000 : ℝ), (6093015382297/100000000000000 : ℝ), (24151859746563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5223846297/10000000000 : ℝ)|^5919 ≤ (22801632554873/50000000000000 : ℝ)^4895
        have hw : |(5223846297/10000000000 : ℝ)|=(5223846297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-98868731/1000000000 : ℝ)|^5919 ≤ (6093015382297/100000000000000 : ℝ)^4895
        have hw : |(-98868731/1000000000 : ℝ)|=(98868731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369596499/2500000000 : ℝ)|^5919 ≤ (24151859746563/50000000000000 : ℝ)^4895
        have hw : |(1369596499/2500000000 : ℝ)|=(1369596499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s3_3 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4179077/8000000 : ℝ)*x 0 + (5478386049/10000000000 : ℝ)*x 1 + (-988687301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4179077/8000000 : ℝ)^5919 ≤ (11400816153403/25000000000000 : ℝ)^4895 := by
    have hnat : (4179077 : ℕ)^5919*25000000000000^4895 ≤ 11400816153403^4895*8000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4179077 8000000 11400816153403 25000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5478386049/10000000000 : ℝ)^5919 ≤ (48303720058193/100000000000000 : ℝ)^4895 := by
    have hnat : (5478386049 : ℕ)^5919*100000000000000^4895 ≤ 48303720058193^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478386049 10000000000 48303720058193 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (988687301/10000000000 : ℝ)^5919 ≤ (609301531523/10000000000000 : ℝ)^4895 := by
    have hnat : (988687301 : ℕ)^5919*10000000000000^4895 ≤ 609301531523^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988687301 10000000000 609301531523 10000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4179077/8000000 : ℝ), (5478386049/10000000000 : ℝ), (-988687301/10000000000 : ℝ)] ![(11400816153403/25000000000000 : ℝ), (48303720058193/100000000000000 : ℝ), (609301531523/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4179077/8000000 : ℝ)|^5919 ≤ (11400816153403/25000000000000 : ℝ)^4895
        have hw : |(4179077/8000000 : ℝ)|=(4179077/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5478386049/10000000000 : ℝ)|^5919 ≤ (48303720058193/100000000000000 : ℝ)^4895
        have hw : |(5478386049/10000000000 : ℝ)|=(5478386049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-988687301/10000000000 : ℝ)|^5919 ≤ (609301531523/10000000000000 : ℝ)^4895
        have hw : |(-988687301/10000000000 : ℝ)|=(988687301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s3_4 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4003739733/10000000000 : ℝ)*x 0 + (4694655633/10000000000 : ℝ)*x 1 + (3372078451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4003739733/10000000000 : ℝ)^5919 ≤ (8265030511843/25000000000000 : ℝ)^4895 := by
    have hnat : (4003739733 : ℕ)^5919*25000000000000^4895 ≤ 8265030511843^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4003739733 10000000000 8265030511843 25000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4694655633/10000000000 : ℝ)^5919 ≤ (40077952349181/100000000000000 : ℝ)^4895 := by
    have hnat : (4694655633 : ℕ)^5919*100000000000000^4895 ≤ 40077952349181^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4694655633 10000000000 40077952349181 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3372078451/10000000000 : ℝ)^5919 ≤ (6715481395071/25000000000000 : ℝ)^4895 := by
    have hnat : (3372078451 : ℕ)^5919*25000000000000^4895 ≤ 6715481395071^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3372078451 10000000000 6715481395071 25000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4003739733/10000000000 : ℝ), (4694655633/10000000000 : ℝ), (3372078451/10000000000 : ℝ)] ![(8265030511843/25000000000000 : ℝ), (40077952349181/100000000000000 : ℝ), (6715481395071/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4003739733/10000000000 : ℝ)|^5919 ≤ (8265030511843/25000000000000 : ℝ)^4895
        have hw : |(4003739733/10000000000 : ℝ)|=(4003739733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4694655633/10000000000 : ℝ)|^5919 ≤ (40077952349181/100000000000000 : ℝ)^4895
        have hw : |(4694655633/10000000000 : ℝ)|=(4694655633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3372078451/10000000000 : ℝ)|^5919 ≤ (6715481395071/25000000000000 : ℝ)^4895
        have hw : |(3372078451/10000000000 : ℝ)|=(3372078451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1759_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (220324357/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8901/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1829/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1829/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17801/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8901/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1829/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8901/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1829/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8901/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1829/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8901/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1829/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8901/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1829/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8901/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1829/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1829/20000 : ℝ) ^ (5903/1024 : ℝ) ≤ (102704458209167/100000000000000000000 : ℝ) := by
    have hpowers : (1829/20000 : ℝ)^5903 ≤ (102704458209167/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1829 : ℕ)^5903*100000000000000000000^1024 ≤ 102704458209167^1024*20000^5903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1829 20000 102704458209167 100000000000000000000 5903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1829/20000 : ℝ)) (X := (102704458209167/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8901/50000 : ℝ) ^ (5903/1024 : ℝ) ≤ (18662772186469/390625000000000000 : ℝ) := by
    have hpowers : (8901/50000 : ℝ)^5903 ≤ (18662772186469/390625000000000000 : ℝ)^1024 := by
      have hnat : (8901 : ℕ)^5903*390625000000000000^1024 ≤ 18662772186469^1024*50000^5903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8901 50000 18662772186469 390625000000000000 5903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8901/50000 : ℝ)) (X := (18662772186469/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000102704458209167/50000000000000000000 : ℝ) ≤ (500000178162419/500000000000000 : ℝ) ^ (5903/1024 : ℝ) := by
    have hpowers : (50000102704458209167/50000000000000000000 : ℝ)^1024 ≤ (500000178162419/500000000000000 : ℝ)^5903 := by
      have hnat : (50000102704458209167 : ℕ)^1024*500000000000000^5903 ≤ 500000178162419^5903*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000102704458209167 50000000000000000000 500000178162419 500000000000000 1024 5903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000178162419/500000000000000 : ℝ)) (X := (50000102704458209167/50000000000000000000 : ℝ)) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100004880374137945231/100000000000000000000 : ℝ) ≤ (2000016931737511/2000000000000000 : ℝ) ^ (5903/1024 : ℝ) := by
    have hpowers : (100004880374137945231/100000000000000000000 : ℝ)^1024 ≤ (2000016931737511/2000000000000000 : ℝ)^5903 := by
      have hnat : (100004880374137945231 : ℕ)^1024*2000000000000000^5903 ≤ 2000016931737511^5903*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100004880374137945231 100000000000000000000 2000016931737511 2000000000000000 1024 5903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000016931737511/2000000000000000 : ℝ)) (X := (100004880374137945231/100000000000000000000 : ℝ)) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (195331162772186469/195312500000000000 : ℝ) ≤ (1000016575412673/1000000000000000 : ℝ) ^ (5903/1024 : ℝ) := by
    have hpowers : (195331162772186469/195312500000000000 : ℝ)^1024 ≤ (1000016575412673/1000000000000000 : ℝ)^5903 := by
      have hnat : (195331162772186469 : ℕ)^1024*1000000000000000^5903 ≤ 1000016575412673^5903*195312500000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195331162772186469 195312500000000000 1000016575412673 1000000000000000 1024 5903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000016575412673/1000000000000000 : ℝ)) (X := (195331162772186469/195312500000000000 : ℝ)) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(102704458209167/100000000000000000000 : ℝ) ≤ ((8656854761145871491/8657000000000000000 : ℝ)+2*(3243817567/34628000000000 : ℝ)*(1829/20000 : ℝ))^(5903/1024 : ℝ) := by
    rw [show (8656854761145871491/8657000000000000000 : ℝ)+2*(3243817567/34628000000000 : ℝ)*(1829/20000 : ℝ)=(500000178162419/500000000000000 : ℝ) by norm_num, show 1+2*(102704458209167/100000000000000000000 : ℝ)=(50000102704458209167/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18662772186469/390625000000000000 : ℝ)+(102704458209167/100000000000000000000 : ℝ) ≤ ((8656854761145871491/8657000000000000000 : ℝ)+(3243817567/34628000000000 : ℝ)*((8901/50000 : ℝ)+(1829/20000 : ℝ)))^(5903/1024 : ℝ) := by
    rw [show (8656854761145871491/8657000000000000000 : ℝ)+(3243817567/34628000000000 : ℝ)*((8901/50000 : ℝ)+(1829/20000 : ℝ))=(2000016931737511/2000000000000000 : ℝ) by norm_num, show 1+(18662772186469/390625000000000000 : ℝ)+(102704458209167/100000000000000000000 : ℝ)=(100004880374137945231/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18662772186469/390625000000000000 : ℝ) ≤ ((8656854761145871491/8657000000000000000 : ℝ)+2*(3243817567/34628000000000 : ℝ)*(8901/50000 : ℝ))^(5903/1024 : ℝ) := by
    rw [show (8656854761145871491/8657000000000000000 : ℝ)+2*(3243817567/34628000000000 : ℝ)*(8901/50000 : ℝ)=(1000016575412673/1000000000000000 : ℝ) by norm_num, show 1+2*(18662772186469/390625000000000000 : ℝ)=(195331162772186469/195312500000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8656854761145871491/8657000000000000000 : ℝ)*(X 1 0+X 2 0)+(3243817567/34628000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5903/1024 : ℝ)) (lo := (1829/20000 : ℝ)) (hi := (8901/50000 : ℝ)) (c := (8656854761145871491/8657000000000000000 : ℝ)) (alpha := (3243817567/34628000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8656854761145871491/8657000000000000000 : ℝ)*(X 0 1+X 2 1)+(3243817567/34628000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5903/1024 : ℝ)) (lo := (1829/20000 : ℝ)) (hi := (8901/50000 : ℝ)) (c := (8656854761145871491/8657000000000000000 : ℝ)) (alpha := (3243817567/34628000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8656854761145871491/8657000000000000000 : ℝ)*(X 0 2+X 1 2)+(3243817567/34628000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5903/1024 : ℝ)) (lo := (1829/20000 : ℝ)) (hi := (8901/50000 : ℝ)) (c := (8656854761145871491/8657000000000000000 : ℝ)) (alpha := (3243817567/34628000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1066004871/2000000000 : ℝ)*X 2 0+(1016701201/2000000000 : ℝ)*X 2 1+(-691783761/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s3_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1174116271/10000000000 : ℝ)*X 0 0+(1018026701/2000000000 : ℝ)*X 0 1+(1095677203/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s3_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5223846297/10000000000 : ℝ)*X 1 0+(-98868731/1000000000 : ℝ)*X 1 1+(1369596499/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s3_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4179077/8000000 : ℝ)*X 2 0+(5478386049/10000000000 : ℝ)*X 2 1+(-988687301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s3_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4003739733/10000000000 : ℝ)*X 0 0+(4694655633/10000000000 : ℝ)*X 0 1+(3372078451/10000000000 : ℝ)*X 0 2+(4003739733/10000000000 : ℝ)*X 1 0+(4694655633/10000000000 : ℝ)*X 1 1+(3372078451/10000000000 : ℝ)*X 1 2+(4003739733/10000000000 : ℝ)*X 2 0+(4694655633/10000000000 : ℝ)*X 2 1+(3372078451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s3_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (720690010453713356858530191/108212500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (436494927/50000000000000 : ℝ)*(base19) + (448778523/50000000000000 : ℝ)*(base23) + (48795721/20000000000000 : ℝ)*(lower1) + (145860003/100000000000000 : ℝ)*(upper3) + (10298103/50000000000000 : ℝ)*(lower4) + (70083571/50000000000000 : ℝ)*(upper5) + (416466823016311/25000000000000 : ℝ)*(major0) + (416466823016311/25000000000000 : ℝ)*(major1) + (416466823016311/25000000000000 : ℝ)*(major2) + (20450571/5000000000000 : ℝ)*(sp0) + (2575636709222453/100000000000000 : ℝ)*(sp1) + (1287817918116299/50000000000000 : ℝ)*(sp2) + (2575635402653987/100000000000000 : ℝ)*(sp3) + (378048826454817/50000000000000 : ℝ)*(sp4) + (378048826454817/50000000000000 : ℝ)*(f.failure) + (2575636709222453/100000000000000 : ℝ)*(f.sum) + (5855797873323/8657000000000000000000000000 : ℝ)*base66 + (200031113608164701/216425000000000000000000000000000 : ℝ)*base67 + (2098416929788314701/216425000000000000000000000000000 : ℝ)*base69 + (2537697869024739701/216425000000000000000000000000000 : ℝ)*base71 + (8461761099923/4328500000000000000000000000 : ℝ)*base73 + (9404339973484789701/216425000000000000000000000000000 : ℝ)*base75 + (1538324429942039701/216425000000000000000000000000000 : ℝ)*base77 + (389399374743514701/216425000000000000000000000000000 : ℝ)*base79 + (64263983319941/8657000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (54922331/5000000000000000000000 : ℝ)*base90 + (54922331/5000000000000000000000 : ℝ)*base92 + (54922331/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1759_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (220324357/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8901/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1829/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1829/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17801/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1759_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1759_box_0 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-801425449/10000000000 : ℝ)*x 0 + (5415743227/10000000000 : ℝ)*x 1 + (1083148591/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (801425449/10000000000 : ℝ)^5919 ≤ (4726709475243/100000000000000 : ℝ)^4895 := by
    have hnat : (801425449 : ℕ)^5919*100000000000000^4895 ≤ 4726709475243^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801425449 10000000000 4726709475243 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415743227/10000000000 : ℝ)^5919 ≤ (297729041879/625000000000 : ℝ)^4895 := by
    have hnat : (5415743227 : ℕ)^5919*625000000000^4895 ≤ 297729041879^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415743227 10000000000 297729041879 625000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083148591/2000000000 : ℝ)^5919 ≤ (9527328761529/20000000000000 : ℝ)^4895 := by
    have hnat : (1083148591 : ℕ)^5919*20000000000000^4895 ≤ 9527328761529^4895*2000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083148591 2000000000 9527328761529 20000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-801425449/10000000000 : ℝ), (5415743227/10000000000 : ℝ), (1083148591/2000000000 : ℝ)] ![(4726709475243/100000000000000 : ℝ), (297729041879/625000000000 : ℝ), (9527328761529/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-801425449/10000000000 : ℝ)|^5919 ≤ (4726709475243/100000000000000 : ℝ)^4895
        have hw : |(-801425449/10000000000 : ℝ)|=(801425449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415743227/10000000000 : ℝ)|^5919 ≤ (297729041879/625000000000 : ℝ)^4895
        have hw : |(5415743227/10000000000 : ℝ)|=(5415743227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083148591/2000000000 : ℝ)|^5919 ≤ (9527328761529/20000000000000 : ℝ)^4895
        have hw : |(1083148591/2000000000 : ℝ)|=(1083148591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_box_1 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (51934009/100000000 : ℝ)*x 0 + (-279888253/2500000000 : ℝ)*x 1 + (2707871647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51934009/100000000 : ℝ)^5919 ≤ (22641039188759/50000000000000 : ℝ)^4895 := by
    have hnat : (51934009 : ℕ)^5919*50000000000000^4895 ≤ 22641039188759^4895*100000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51934009 100000000 22641039188759 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (279888253/2500000000 : ℝ)^5919 ≤ (3540637099541/50000000000000 : ℝ)^4895 := by
    have hnat : (279888253 : ℕ)^5919*50000000000000^4895 ≤ 3540637099541^4895*2500000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279888253 2500000000 3540637099541 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707871647/5000000000 : ℝ)^5919 ≤ (47636647413253/100000000000000 : ℝ)^4895 := by
    have hnat : (2707871647 : ℕ)^5919*100000000000000^4895 ≤ 47636647413253^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707871647 5000000000 47636647413253 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(51934009/100000000 : ℝ), (-279888253/2500000000 : ℝ), (2707871647/5000000000 : ℝ)] ![(22641039188759/50000000000000 : ℝ), (3540637099541/50000000000000 : ℝ), (47636647413253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(51934009/100000000 : ℝ)|^5919 ≤ (22641039188759/50000000000000 : ℝ)^4895
        have hw : |(51934009/100000000 : ℝ)|=(51934009/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-279888253/2500000000 : ℝ)|^5919 ≤ (3540637099541/50000000000000 : ℝ)^4895
        have hw : |(-279888253/2500000000 : ℝ)|=(279888253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707871647/5000000000 : ℝ)|^5919 ≤ (47636647413253/100000000000000 : ℝ)^4895
        have hw : |(2707871647/5000000000 : ℝ)|=(2707871647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_box_2 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5193400879/10000000000 : ℝ)*x 0 + (5415743311/10000000000 : ℝ)*x 1 + (-1119553017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5193400879/10000000000 : ℝ)^5919 ≤ (2830129884757/6250000000000 : ℝ)^4895 := by
    have hnat : (5193400879 : ℕ)^5919*6250000000000^4895 ≤ 2830129884757^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193400879 10000000000 2830129884757 6250000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415743311/10000000000 : ℝ)^5919 ≤ (9527329518813/20000000000000 : ℝ)^4895 := by
    have hnat : (5415743311 : ℕ)^5919*20000000000000^4895 ≤ 9527329518813^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415743311 10000000000 9527329518813 20000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119553017/10000000000 : ℝ)^5919 ≤ (7081274237323/100000000000000 : ℝ)^4895 := by
    have hnat : (1119553017 : ℕ)^5919*100000000000000^4895 ≤ 7081274237323^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119553017 10000000000 7081274237323 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5193400879/10000000000 : ℝ), (5415743311/10000000000 : ℝ), (-1119553017/10000000000 : ℝ)] ![(2830129884757/6250000000000 : ℝ), (9527329518813/20000000000000 : ℝ), (7081274237323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5193400879/10000000000 : ℝ)|^5919 ≤ (2830129884757/6250000000000 : ℝ)^4895
        have hw : |(5193400879/10000000000 : ℝ)|=(5193400879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415743311/10000000000 : ℝ)|^5919 ≤ (9527329518813/20000000000000 : ℝ)^4895
        have hw : |(5415743311/10000000000 : ℝ)|=(5415743311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1119553017/10000000000 : ℝ)|^5919 ≤ (7081274237323/100000000000000 : ℝ)^4895
        have hw : |(-1119553017/10000000000 : ℝ)|=(1119553017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_box_3 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4527557043/10000000000 : ℝ)*x 0 + (1889028777/5000000000 : ℝ)*x 1 + (1889028729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4527557043/10000000000 : ℝ)^5919 ≤ (149841837473/390625000000 : ℝ)^4895 := by
    have hnat : (4527557043 : ℕ)^5919*390625000000^4895 ≤ 149841837473^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527557043 10000000000 149841837473 390625000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1889028777/5000000000 : ℝ)^5919 ≤ (7705061317747/25000000000000 : ℝ)^4895 := by
    have hnat : (1889028777 : ℕ)^5919*25000000000000^4895 ≤ 7705061317747^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889028777 5000000000 7705061317747 25000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1889028729/5000000000 : ℝ)^5919 ≤ (15410122162011/50000000000000 : ℝ)^4895 := by
    have hnat : (1889028729 : ℕ)^5919*50000000000000^4895 ≤ 15410122162011^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889028729 5000000000 15410122162011 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4527557043/10000000000 : ℝ), (1889028777/5000000000 : ℝ), (1889028729/5000000000 : ℝ)] ![(149841837473/390625000000 : ℝ), (7705061317747/25000000000000 : ℝ), (15410122162011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4527557043/10000000000 : ℝ)|^5919 ≤ (149841837473/390625000000 : ℝ)^4895
        have hw : |(4527557043/10000000000 : ℝ)|=(4527557043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1889028777/5000000000 : ℝ)|^5919 ≤ (7705061317747/25000000000000 : ℝ)^4895
        have hw : |(1889028777/5000000000 : ℝ)|=(1889028777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1889028729/5000000000 : ℝ)|^5919 ≤ (15410122162011/50000000000000 : ℝ)^4895
        have hw : |(1889028729/5000000000 : ℝ)|=(1889028729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_box_4 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-792629847/5000000000 : ℝ)*x 0 + (512939799/1000000000 : ℝ)*x 1 + (2564699089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (792629847/5000000000 : ℝ)^5919 ≤ (673979983007/6250000000000 : ℝ)^4895 := by
    have hnat : (792629847 : ℕ)^5919*6250000000000^4895 ≤ 673979983007^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792629847 5000000000 673979983007 6250000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512939799/1000000000 : ℝ)^5919 ≤ (44608159139941/100000000000000 : ℝ)^4895 := by
    have hnat : (512939799 : ℕ)^5919*100000000000000^4895 ≤ 44608159139941^4895*1000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512939799 1000000000 44608159139941 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2564699089/5000000000 : ℝ)^5919 ≤ (44608161116917/100000000000000 : ℝ)^4895 := by
    have hnat : (2564699089 : ℕ)^5919*100000000000000^4895 ≤ 44608161116917^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564699089 5000000000 44608161116917 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-792629847/5000000000 : ℝ), (512939799/1000000000 : ℝ), (2564699089/5000000000 : ℝ)] ![(673979983007/6250000000000 : ℝ), (44608159139941/100000000000000 : ℝ), (44608161116917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-792629847/5000000000 : ℝ)|^5919 ≤ (673979983007/6250000000000 : ℝ)^4895
        have hw : |(-792629847/5000000000 : ℝ)|=(792629847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(512939799/1000000000 : ℝ)|^5919 ≤ (44608159139941/100000000000000 : ℝ)^4895
        have hw : |(512939799/1000000000 : ℝ)|=(512939799/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2564699089/5000000000 : ℝ)|^5919 ≤ (44608161116917/100000000000000 : ℝ)^4895
        have hw : |(2564699089/5000000000 : ℝ)|=(2564699089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_box_5 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692184031/5000000000 : ℝ)*x 0 + (-1249735073/10000000000 : ℝ)*x 1 + (2564699069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692184031/5000000000 : ℝ)^5919 ≤ (11825785659123/25000000000000 : ℝ)^4895 := by
    have hnat : (2692184031 : ℕ)^5919*25000000000000^4895 ≤ 11825785659123^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692184031 5000000000 11825785659123 25000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1249735073/10000000000 : ℝ)^5919 ≤ (63192942581/781250000000 : ℝ)^4895 := by
    have hnat : (1249735073 : ℕ)^5919*781250000000^4895 ≤ 63192942581^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249735073 10000000000 63192942581 781250000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2564699069/5000000000 : ℝ)^5919 ≤ (11152040174071/25000000000000 : ℝ)^4895 := by
    have hnat : (2564699069 : ℕ)^5919*25000000000000^4895 ≤ 11152040174071^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564699069 5000000000 11152040174071 25000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692184031/5000000000 : ℝ), (-1249735073/10000000000 : ℝ), (2564699069/5000000000 : ℝ)] ![(11825785659123/25000000000000 : ℝ), (63192942581/781250000000 : ℝ), (11152040174071/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692184031/5000000000 : ℝ)|^5919 ≤ (11825785659123/25000000000000 : ℝ)^4895
        have hw : |(2692184031/5000000000 : ℝ)|=(2692184031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1249735073/10000000000 : ℝ)|^5919 ≤ (63192942581/781250000000 : ℝ)^4895
        have hw : |(-1249735073/10000000000 : ℝ)|=(1249735073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2564699069/5000000000 : ℝ)|^5919 ≤ (11152040174071/25000000000000 : ℝ)^4895
        have hw : |(2564699069/5000000000 : ℝ)|=(2564699069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_box_6 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538436821/1000000000 : ℝ)*x 0 + (1025879613/2000000000 : ℝ)*x 1 + (-1249734971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538436821/1000000000 : ℝ)^5919 ≤ (47303144208709/100000000000000 : ℝ)^4895 := by
    have hnat : (538436821 : ℕ)^5919*100000000000000^4895 ≤ 47303144208709^4895*1000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538436821 1000000000 47303144208709 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025879613/2000000000 : ℝ)^5919 ≤ (11152039982157/25000000000000 : ℝ)^4895 := by
    have hnat : (1025879613 : ℕ)^5919*25000000000000^4895 ≤ 11152039982157^4895*2000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025879613 2000000000 11152039982157 25000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1249734971/10000000000 : ℝ)^5919 ≤ (4044347926043/50000000000000 : ℝ)^4895 := by
    have hnat : (1249734971 : ℕ)^5919*50000000000000^4895 ≤ 4044347926043^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249734971 10000000000 4044347926043 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538436821/1000000000 : ℝ), (1025879613/2000000000 : ℝ), (-1249734971/10000000000 : ℝ)] ![(47303144208709/100000000000000 : ℝ), (11152039982157/25000000000000 : ℝ), (4044347926043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538436821/1000000000 : ℝ)|^5919 ≤ (47303144208709/100000000000000 : ℝ)^4895
        have hw : |(538436821/1000000000 : ℝ)|=(538436821/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1025879613/2000000000 : ℝ)|^5919 ≤ (11152039982157/25000000000000 : ℝ)^4895
        have hw : |(1025879613/2000000000 : ℝ)|=(1025879613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1249734971/10000000000 : ℝ)|^5919 ≤ (4044347926043/50000000000000 : ℝ)^4895
        have hw : |(-1249734971/10000000000 : ℝ)|=(1249734971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_box_7 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (171974787/500000000 : ℝ)*x 0 + (4320021607/10000000000 : ℝ)*x 1 + (1382407/3200000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171974787/500000000 : ℝ)^5919 ≤ (27512667680487/100000000000000 : ℝ)^4895 := by
    have hnat : (171974787 : ℕ)^5919*100000000000000^4895 ≤ 27512667680487^4895*500000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171974787 500000000 27512667680487 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4320021607/10000000000 : ℝ)^5919 ≤ (18121832397039/50000000000000 : ℝ)^4895 := by
    have hnat : (4320021607 : ℕ)^5919*50000000000000^4895 ≤ 18121832397039^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320021607 10000000000 18121832397039 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1382407/3200000 : ℝ)^5919 ≤ (18121833756437/50000000000000 : ℝ)^4895 := by
    have hnat : (1382407 : ℕ)^5919*50000000000000^4895 ≤ 18121833756437^4895*3200000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382407 3200000 18121833756437 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171974787/500000000 : ℝ), (4320021607/10000000000 : ℝ), (1382407/3200000 : ℝ)] ![(27512667680487/100000000000000 : ℝ), (18121832397039/50000000000000 : ℝ), (18121833756437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171974787/500000000 : ℝ)|^5919 ≤ (27512667680487/100000000000000 : ℝ)^4895
        have hw : |(171974787/500000000 : ℝ)|=(171974787/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4320021607/10000000000 : ℝ)|^5919 ≤ (18121832397039/50000000000000 : ℝ)^4895
        have hw : |(4320021607/10000000000 : ℝ)|=(4320021607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1382407/3200000 : ℝ)|^5919 ≤ (18121833756437/50000000000000 : ℝ)^4895
        have hw : |(1382407/3200000 : ℝ)|=(1382407/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_box_8 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-353644433/2500000000 : ℝ)*x 0 + (1227618959/2500000000 : ℝ)*x 1 + (68460897/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (353644433/2500000000 : ℝ)^5919 ≤ (4698009074963/50000000000000 : ℝ)^4895 := by
    have hnat : (353644433 : ℕ)^5919*50000000000000^4895 ≤ 4698009074963^4895*2500000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353644433 2500000000 4698009074963 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1227618959/2500000000 : ℝ)^5919 ≤ (1692656243809/4000000000000 : ℝ)^4895 := by
    have hnat : (1227618959 : ℕ)^5919*4000000000000^4895 ≤ 1692656243809^4895*2500000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1227618959 2500000000 1692656243809 4000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68460897/125000000 : ℝ)^5919 ≤ (12071893934149/25000000000000 : ℝ)^4895 := by
    have hnat : (68460897 : ℕ)^5919*25000000000000^4895 ≤ 12071893934149^4895*125000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68460897 125000000 12071893934149 25000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-353644433/2500000000 : ℝ), (1227618959/2500000000 : ℝ), (68460897/125000000 : ℝ)] ![(4698009074963/50000000000000 : ℝ), (1692656243809/4000000000000 : ℝ), (12071893934149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-353644433/2500000000 : ℝ)|^5919 ≤ (4698009074963/50000000000000 : ℝ)^4895
        have hw : |(-353644433/2500000000 : ℝ)|=(353644433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1227618959/2500000000 : ℝ)|^5919 ≤ (1692656243809/4000000000000 : ℝ)^4895
        have hw : |(1227618959/2500000000 : ℝ)|=(1227618959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68460897/125000000 : ℝ)|^5919 ≤ (12071893934149/25000000000000 : ℝ)^4895
        have hw : |(68460897/125000000 : ℝ)|=(68460897/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_box_9 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152707799/10000000000 : ℝ)*x 0 + (-8723317/80000000 : ℝ)*x 1 + (5476871711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152707799/10000000000 : ℝ)^5919 ≤ (22426698748431/50000000000000 : ℝ)^4895 := by
    have hnat : (5152707799 : ℕ)^5919*50000000000000^4895 ≤ 22426698748431^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152707799 10000000000 22426698748431 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8723317/80000000 : ℝ)^5919 ≤ (3429513634189/50000000000000 : ℝ)^4895 := by
    have hnat : (8723317 : ℕ)^5919*50000000000000^4895 ≤ 3429513634189^4895*80000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8723317 80000000 3429513634189 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5476871711/10000000000 : ℝ)^5919 ≤ (24143787607103/50000000000000 : ℝ)^4895 := by
    have hnat : (5476871711 : ℕ)^5919*50000000000000^4895 ≤ 24143787607103^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476871711 10000000000 24143787607103 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152707799/10000000000 : ℝ), (-8723317/80000000 : ℝ), (5476871711/10000000000 : ℝ)] ![(22426698748431/50000000000000 : ℝ), (3429513634189/50000000000000 : ℝ), (24143787607103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152707799/10000000000 : ℝ)|^5919 ≤ (22426698748431/50000000000000 : ℝ)^4895
        have hw : |(5152707799/10000000000 : ℝ)|=(5152707799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8723317/80000000 : ℝ)|^5919 ≤ (3429513634189/50000000000000 : ℝ)^4895
        have hw : |(-8723317/80000000 : ℝ)|=(8723317/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5476871711/10000000000 : ℝ)|^5919 ≤ (24143787607103/50000000000000 : ℝ)^4895
        have hw : |(5476871711/10000000000 : ℝ)|=(5476871711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_box_10 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (322044231/625000000 : ℝ)*x 0 + (5476872029/10000000000 : ℝ)*x 1 + (-1090414323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (322044231/625000000 : ℝ)^5919 ≤ (1401668637897/3125000000000 : ℝ)^4895 := by
    have hnat : (322044231 : ℕ)^5919*3125000000000^4895 ≤ 1401668637897^4895*625000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322044231 625000000 1401668637897 3125000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5476872029/10000000000 : ℝ)^5919 ≤ (6035947325551/12500000000000 : ℝ)^4895 := by
    have hnat : (5476872029 : ℕ)^5919*12500000000000^4895 ≤ 6035947325551^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476872029 10000000000 6035947325551 12500000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090414323/10000000000 : ℝ)^5919 ≤ (428689060707/6250000000000 : ℝ)^4895 := by
    have hnat : (1090414323 : ℕ)^5919*6250000000000^4895 ≤ 428689060707^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090414323 10000000000 428689060707 6250000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(322044231/625000000 : ℝ), (5476872029/10000000000 : ℝ), (-1090414323/10000000000 : ℝ)] ![(1401668637897/3125000000000 : ℝ), (6035947325551/12500000000000 : ℝ), (428689060707/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(322044231/625000000 : ℝ)|^5919 ≤ (1401668637897/3125000000000 : ℝ)^4895
        have hw : |(322044231/625000000 : ℝ)|=(322044231/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5476872029/10000000000 : ℝ)|^5919 ≤ (6035947325551/12500000000000 : ℝ)^4895
        have hw : |(5476872029/10000000000 : ℝ)|=(5476872029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1090414323/10000000000 : ℝ)|^5919 ≤ (428689060707/6250000000000 : ℝ)^4895
        have hw : |(-1090414323/10000000000 : ℝ)|=(1090414323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_box_11 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4749338869/10000000000 : ℝ)*x 0 + (3661929829/10000000000 : ℝ)*x 1 + (3661928023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4749338869/10000000000 : ℝ)^5919 ≤ (40643121977879/100000000000000 : ℝ)^4895 := by
    have hnat : (4749338869 : ℕ)^5919*100000000000000^4895 ≤ 40643121977879^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4749338869 10000000000 40643121977879 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3661929829/10000000000 : ℝ)^5919 ≤ (3709805981701/12500000000000 : ℝ)^4895 := by
    have hnat : (3661929829 : ℕ)^5919*12500000000000^4895 ≤ 3709805981701^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3661929829 10000000000 3709805981701 12500000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3661928023/10000000000 : ℝ)^5919 ≤ (29678430154779/100000000000000 : ℝ)^4895 := by
    have hnat : (3661928023 : ℕ)^5919*100000000000000^4895 ≤ 29678430154779^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3661928023 10000000000 29678430154779 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4749338869/10000000000 : ℝ), (3661929829/10000000000 : ℝ), (3661928023/10000000000 : ℝ)] ![(40643121977879/100000000000000 : ℝ), (3709805981701/12500000000000 : ℝ), (29678430154779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4749338869/10000000000 : ℝ)|^5919 ≤ (40643121977879/100000000000000 : ℝ)^4895
        have hw : |(4749338869/10000000000 : ℝ)|=(4749338869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3661929829/10000000000 : ℝ)|^5919 ≤ (3709805981701/12500000000000 : ℝ)^4895
        have hw : |(3661929829/10000000000 : ℝ)|=(3661929829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3661928023/10000000000 : ℝ)|^5919 ≤ (29678430154779/100000000000000 : ℝ)^4895
        have hw : |(3661928023/10000000000 : ℝ)|=(3661928023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_box_12 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-7663251/80000000 : ℝ)*x 0 + (140554173/250000000 : ℝ)*x 1 + (5099578279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7663251/80000000 : ℝ)^5919 ≤ (366524442121/6250000000000 : ℝ)^4895 := by
    have hnat : (7663251 : ℕ)^5919*6250000000000^4895 ≤ 366524442121^4895*80000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7663251 80000000 366524442121 6250000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140554173/250000000 : ℝ)^5919 ≤ (9968167562591/20000000000000 : ℝ)^4895 := by
    have hnat : (140554173 : ℕ)^5919*20000000000000^4895 ≤ 9968167562591^4895*250000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140554173 250000000 9968167562591 20000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5099578279/10000000000 : ℝ)^5919 ≤ (44294771105937/100000000000000 : ℝ)^4895 := by
    have hnat : (5099578279 : ℕ)^5919*100000000000000^4895 ≤ 44294771105937^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5099578279 10000000000 44294771105937 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7663251/80000000 : ℝ), (140554173/250000000 : ℝ), (5099578279/10000000000 : ℝ)] ![(366524442121/6250000000000 : ℝ), (9968167562591/20000000000000 : ℝ), (44294771105937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7663251/80000000 : ℝ)|^5919 ≤ (366524442121/6250000000000 : ℝ)^4895
        have hw : |(-7663251/80000000 : ℝ)|=(7663251/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140554173/250000000 : ℝ)|^5919 ≤ (9968167562591/20000000000000 : ℝ)^4895
        have hw : |(140554173/250000000 : ℝ)|=(140554173/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5099578279/10000000000 : ℝ)|^5919 ≤ (44294771105937/100000000000000 : ℝ)^4895
        have hw : |(5099578279/10000000000 : ℝ)|=(5099578279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_box_13 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (675541223/1250000000 : ℝ)*x 0 + (-15783229/125000000 : ℝ)*x 1 + (509957847/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675541223/1250000000 : ℝ)^5919 ≤ (11878819993499/25000000000000 : ℝ)^4895 := by
    have hnat : (675541223 : ℕ)^5919*25000000000000^4895 ≤ 11878819993499^4895*1250000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675541223 1250000000 11878819993499 25000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15783229/125000000 : ℝ)^5919 ≤ (2047486724239/25000000000000 : ℝ)^4895 := by
    have hnat : (15783229 : ℕ)^5919*25000000000000^4895 ≤ 2047486724239^4895*125000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15783229 125000000 2047486724239 25000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (509957847/1000000000 : ℝ)^5919 ≤ (44294773112013/100000000000000 : ℝ)^4895 := by
    have hnat : (509957847 : ℕ)^5919*100000000000000^4895 ≤ 44294773112013^4895*1000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509957847 1000000000 44294773112013 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675541223/1250000000 : ℝ), (-15783229/125000000 : ℝ), (509957847/1000000000 : ℝ)] ![(11878819993499/25000000000000 : ℝ), (2047486724239/25000000000000 : ℝ), (44294773112013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675541223/1250000000 : ℝ)|^5919 ≤ (11878819993499/25000000000000 : ℝ)^4895
        have hw : |(675541223/1250000000 : ℝ)|=(675541223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15783229/125000000 : ℝ)|^5919 ≤ (2047486724239/25000000000000 : ℝ)^4895
        have hw : |(-15783229/125000000 : ℝ)|=(15783229/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(509957847/1000000000 : ℝ)|^5919 ≤ (44294773112013/100000000000000 : ℝ)^4895
        have hw : |(509957847/1000000000 : ℝ)|=(509957847/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_box_14 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5404329709/10000000000 : ℝ)*x 0 + (5099577647/10000000000 : ℝ)*x 1 + (-315664881/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5404329709/10000000000 : ℝ)^5919 ≤ (47515279176647/100000000000000 : ℝ)^4895 := by
    have hnat : (5404329709 : ℕ)^5919*100000000000000^4895 ≤ 47515279176647^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404329709 10000000000 47515279176647 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5099577647/10000000000 : ℝ)^5919 ≤ (22147382234017/50000000000000 : ℝ)^4895 := by
    have hnat : (5099577647 : ℕ)^5919*50000000000000^4895 ≤ 22147382234017^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5099577647 10000000000 22147382234017 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315664881/2500000000 : ℝ)^5919 ≤ (8189956340117/100000000000000 : ℝ)^4895 := by
    have hnat : (315664881 : ℕ)^5919*100000000000000^4895 ≤ 8189956340117^4895*2500000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315664881 2500000000 8189956340117 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5404329709/10000000000 : ℝ), (5099577647/10000000000 : ℝ), (-315664881/2500000000 : ℝ)] ![(47515279176647/100000000000000 : ℝ), (22147382234017/50000000000000 : ℝ), (8189956340117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5404329709/10000000000 : ℝ)|^5919 ≤ (47515279176647/100000000000000 : ℝ)^4895
        have hw : |(5404329709/10000000000 : ℝ)|=(5404329709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5099577647/10000000000 : ℝ)|^5919 ≤ (22147382234017/50000000000000 : ℝ)^4895
        have hw : |(5099577647/10000000000 : ℝ)|=(5099577647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-315664881/2500000000 : ℝ)|^5919 ≤ (8189956340117/100000000000000 : ℝ)^4895
        have hw : |(-315664881/2500000000 : ℝ)|=(315664881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_box_15 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1660496987/5000000000 : ℝ)*x 0 + (4376230367/10000000000 : ℝ)*x 1 + (218811681/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1660496987/5000000000 : ℝ)^5919 ≤ (13185320810467/50000000000000 : ℝ)^4895 := by
    have hnat : (1660496987 : ℕ)^5919*50000000000000^4895 ≤ 13185320810467^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1660496987 5000000000 13185320810467 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4376230367/10000000000 : ℝ)^5919 ≤ (36814662632031/100000000000000 : ℝ)^4895 := by
    have hnat : (4376230367 : ℕ)^5919*100000000000000^4895 ≤ 36814662632031^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376230367 10000000000 36814662632031 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218811681/500000000 : ℝ)^5919 ≤ (36814695722307/100000000000000 : ℝ)^4895 := by
    have hnat : (218811681 : ℕ)^5919*100000000000000^4895 ≤ 36814695722307^4895*500000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218811681 500000000 36814695722307 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1660496987/5000000000 : ℝ), (4376230367/10000000000 : ℝ), (218811681/500000000 : ℝ)] ![(13185320810467/50000000000000 : ℝ), (36814662632031/100000000000000 : ℝ), (36814695722307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1660496987/5000000000 : ℝ)|^5919 ≤ (13185320810467/50000000000000 : ℝ)^4895
        have hw : |(1660496987/5000000000 : ℝ)|=(1660496987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4376230367/10000000000 : ℝ)|^5919 ≤ (36814662632031/100000000000000 : ℝ)^4895
        have hw : |(4376230367/10000000000 : ℝ)|=(4376230367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218811681/500000000 : ℝ)|^5919 ≤ (36814695722307/100000000000000 : ℝ)^4895
        have hw : |(218811681/500000000 : ℝ)|=(218811681/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1759_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (220324357/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17801/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1829/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2159/3125 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58553/100000 : ℝ) ∧ (82073/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (93063/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17801/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1829/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17801/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1829/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17801/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1829/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17801/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1829/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17801/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1829/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17801/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1829/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1829/20000 : ℝ) ^ (5903/1024 : ℝ) ≤ (102704458209167/100000000000000000000 : ℝ) := by
    have hpowers : (1829/20000 : ℝ)^5903 ≤ (102704458209167/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1829 : ℕ)^5903*100000000000000000000^1024 ≤ 102704458209167^1024*20000^5903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1829 20000 102704458209167 100000000000000000000 5903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1829/20000 : ℝ)) (X := (102704458209167/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17801/100000 : ℝ) ^ (5903/1024 : ℝ) ≤ (4776122780477261/100000000000000000000 : ℝ) := by
    have hpowers : (17801/100000 : ℝ)^5903 ≤ (4776122780477261/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17801 : ℕ)^5903*100000000000000000000^1024 ≤ 4776122780477261^1024*100000^5903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17801 100000 4776122780477261 100000000000000000000 5903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17801/100000 : ℝ)) (X := (4776122780477261/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000102704458209167/50000000000000000000 : ℝ) ≤ (500000178162419/500000000000000 : ℝ) ^ (5903/1024 : ℝ) := by
    have hpowers : (50000102704458209167/50000000000000000000 : ℝ)^1024 ≤ (500000178162419/500000000000000 : ℝ)^5903 := by
      have hnat : (50000102704458209167 : ℕ)^1024*500000000000000^5903 ≤ 500000178162419^5903*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000102704458209167 50000000000000000000 500000178162419 500000000000000 1024 5903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000178162419/500000000000000 : ℝ)) (X := (50000102704458209167/50000000000000000000 : ℝ)) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25001219706809671607/25000000000000000000 : ℝ) ≤ (10000084631854403/10000000000000000 : ℝ) ^ (5903/1024 : ℝ) := by
    have hpowers : (25001219706809671607/25000000000000000000 : ℝ)^1024 ≤ (10000084631854403/10000000000000000 : ℝ)^5903 := by
      have hnat : (25001219706809671607 : ℕ)^1024*10000000000000000^5903 ≤ 10000084631854403^5903*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001219706809671607 25000000000000000000 10000084631854403 10000000000000000 1024 5903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000084631854403/10000000000000000 : ℝ)) (X := (25001219706809671607/25000000000000000000 : ℝ)) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50004776122780477261/50000000000000000000 : ℝ) ≤ (5000082850230213/5000000000000000 : ℝ) ^ (5903/1024 : ℝ) := by
    have hpowers : (50004776122780477261/50000000000000000000 : ℝ)^1024 ≤ (5000082850230213/5000000000000000 : ℝ)^5903 := by
      have hnat : (50004776122780477261 : ℕ)^1024*5000000000000000^5903 ≤ 5000082850230213^5903*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004776122780477261 50000000000000000000 5000082850230213 5000000000000000 1024 5903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000082850230213/5000000000000000 : ℝ)) (X := (50004776122780477261/50000000000000000000 : ℝ)) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(102704458209167/100000000000000000000 : ℝ) ≤ ((8655854809867381661/8656000000000000000 : ℝ)+2*(81068606023/865600000000000 : ℝ)*(1829/20000 : ℝ))^(5903/1024 : ℝ) := by
    rw [show (8655854809867381661/8656000000000000000 : ℝ)+2*(81068606023/865600000000000 : ℝ)*(1829/20000 : ℝ)=(500000178162419/500000000000000 : ℝ) by norm_num, show 1+2*(102704458209167/100000000000000000000 : ℝ)=(50000102704458209167/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4776122780477261/100000000000000000000 : ℝ)+(102704458209167/100000000000000000000 : ℝ) ≤ ((8655854809867381661/8656000000000000000 : ℝ)+(81068606023/865600000000000 : ℝ)*((17801/100000 : ℝ)+(1829/20000 : ℝ)))^(5903/1024 : ℝ) := by
    rw [show (8655854809867381661/8656000000000000000 : ℝ)+(81068606023/865600000000000 : ℝ)*((17801/100000 : ℝ)+(1829/20000 : ℝ))=(10000084631854403/10000000000000000 : ℝ) by norm_num, show 1+(4776122780477261/100000000000000000000 : ℝ)+(102704458209167/100000000000000000000 : ℝ)=(25001219706809671607/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4776122780477261/100000000000000000000 : ℝ) ≤ ((8655854809867381661/8656000000000000000 : ℝ)+2*(81068606023/865600000000000 : ℝ)*(17801/100000 : ℝ))^(5903/1024 : ℝ) := by
    rw [show (8655854809867381661/8656000000000000000 : ℝ)+2*(81068606023/865600000000000 : ℝ)*(17801/100000 : ℝ)=(5000082850230213/5000000000000000 : ℝ) by norm_num, show 1+2*(4776122780477261/100000000000000000000 : ℝ)=(50004776122780477261/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8655854809867381661/8656000000000000000 : ℝ)*(X 1 0+X 2 0)+(81068606023/865600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5903/1024 : ℝ)) (lo := (1829/20000 : ℝ)) (hi := (17801/100000 : ℝ)) (c := (8655854809867381661/8656000000000000000 : ℝ)) (alpha := (81068606023/865600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8655854809867381661/8656000000000000000 : ℝ)*(X 0 1+X 2 1)+(81068606023/865600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5903/1024 : ℝ)) (lo := (1829/20000 : ℝ)) (hi := (17801/100000 : ℝ)) (c := (8655854809867381661/8656000000000000000 : ℝ)) (alpha := (81068606023/865600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8655854809867381661/8656000000000000000 : ℝ)*(X 0 2+X 1 2)+(81068606023/865600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5903/1024 : ℝ)) (lo := (1829/20000 : ℝ)) (hi := (17801/100000 : ℝ)) (c := (8655854809867381661/8656000000000000000 : ℝ)) (alpha := (81068606023/865600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-801425449/10000000000 : ℝ)*X 0 0+(5415743227/10000000000 : ℝ)*X 0 1+(1083148591/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((51934009/100000000 : ℝ)*X 1 0+(-279888253/2500000000 : ℝ)*X 1 1+(2707871647/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5193400879/10000000000 : ℝ)*X 2 0+(5415743311/10000000000 : ℝ)*X 2 1+(-1119553017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4527557043/10000000000 : ℝ)*X 0 0+(1889028777/5000000000 : ℝ)*X 0 1+(1889028729/5000000000 : ℝ)*X 0 2+(4527557043/10000000000 : ℝ)*X 1 0+(1889028777/5000000000 : ℝ)*X 1 1+(1889028729/5000000000 : ℝ)*X 1 2+(4527557043/10000000000 : ℝ)*X 2 0+(1889028777/5000000000 : ℝ)*X 2 1+(1889028729/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-792629847/5000000000 : ℝ)*X 0 0+(512939799/1000000000 : ℝ)*X 0 1+(2564699089/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2692184031/5000000000 : ℝ)*X 1 0+(-1249735073/10000000000 : ℝ)*X 1 1+(2564699069/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((538436821/1000000000 : ℝ)*X 2 0+(1025879613/2000000000 : ℝ)*X 2 1+(-1249734971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((171974787/500000000 : ℝ)*X 0 0+(4320021607/10000000000 : ℝ)*X 0 1+(1382407/3200000 : ℝ)*X 0 2+(171974787/500000000 : ℝ)*X 1 0+(4320021607/10000000000 : ℝ)*X 1 1+(1382407/3200000 : ℝ)*X 1 2+(171974787/500000000 : ℝ)*X 2 0+(4320021607/10000000000 : ℝ)*X 2 1+(1382407/3200000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-353644433/2500000000 : ℝ)*X 0 0+(1227618959/2500000000 : ℝ)*X 0 1+(68460897/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5152707799/10000000000 : ℝ)*X 1 0+(-8723317/80000000 : ℝ)*X 1 1+(5476871711/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((322044231/625000000 : ℝ)*X 2 0+(5476872029/10000000000 : ℝ)*X 2 1+(-1090414323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4749338869/10000000000 : ℝ)*X 0 0+(3661929829/10000000000 : ℝ)*X 0 1+(3661928023/10000000000 : ℝ)*X 0 2+(4749338869/10000000000 : ℝ)*X 1 0+(3661929829/10000000000 : ℝ)*X 1 1+(3661928023/10000000000 : ℝ)*X 1 2+(4749338869/10000000000 : ℝ)*X 2 0+(3661929829/10000000000 : ℝ)*X 2 1+(3661928023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-7663251/80000000 : ℝ)*X 0 0+(140554173/250000000 : ℝ)*X 0 1+(5099578279/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((675541223/1250000000 : ℝ)*X 1 0+(-15783229/125000000 : ℝ)*X 1 1+(509957847/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5404329709/10000000000 : ℝ)*X 2 0+(5099577647/10000000000 : ℝ)*X 2 1+(-315664881/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1660496987/5000000000 : ℝ)*X 0 0+(4376230367/10000000000 : ℝ)*X 0 1+(218811681/500000000 : ℝ)*X 0 2+(1660496987/5000000000 : ℝ)*X 1 0+(4376230367/10000000000 : ℝ)*X 1 1+(218811681/500000000 : ℝ)*X 1 2+(1660496987/5000000000 : ℝ)*X 2 0+(4376230367/10000000000 : ℝ)*X 2 1+(218811681/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2159/3125 : ℝ) ≤ (-149500579244921902696330204517931/216400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11853251/100000000000000 : ℝ)*(lower2) + (6509973/25000000000000 : ℝ)*(lower3) + (6469411/50000000000000 : ℝ)*(upper5) + (540211193868881/50000000000000 : ℝ)*(major0) + (540211193868881/50000000000000 : ℝ)*(major1) + (540211193868881/50000000000000 : ℝ)*(major2) + (3989037/25000000000000 : ℝ)*(sp2) + (40062583/100000000000000 : ℝ)*(sp3) + (846747553218171/50000000000000 : ℝ)*(sp4) + (846744322814799/50000000000000 : ℝ)*(sp5) + (1693495094930329/100000000000000 : ℝ)*(sp6) + (490378056326353/100000000000000 : ℝ)*(sp7) + (890027/20000000000000 : ℝ)*(sp12) + (6465256879/100000000000000 : ℝ)*(sp13) + (61297262048617/12500000000000 : ℝ)*(f.failure) + (1693495110886477/100000000000000 : ℝ)*(f.sum) + (125639500687977/21640000000000000000000000000 : ℝ)*base66 + (4974526707961778659/432800000000000000000000000000000 : ℝ)*base68 + (188568215783378659/432800000000000000000000000000000 : ℝ)*base70 + (2655646400912178659/432800000000000000000000000000000 : ℝ)*base72 + (146526190712897/21640000000000000000000000000 : ℝ)*base74 + (2125037081489778659/432800000000000000000000000000000 : ℝ)*base76 + (3926958301528178659/432800000000000000000000000000000 : ℝ)*base78 + (1589361007524178659/432800000000000000000000000000000 : ℝ)*base80 + (55794942251303/21640000000000000000000000000 : ℝ)*base81 + (18264269/1250000000000000000000 : ℝ)*base89 + (18264269/1250000000000000000000 : ℝ)*base91 + (18264269/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58553/100000 : ℝ) ≤ (126714945162884090527479226024077/216400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3647437/25000000000000 : ℝ)*(upper0) + (5915703/20000000000000 : ℝ)*(upper3) + (4507617/50000000000000 : ℝ)*(upper4) + (1209322189476819/100000000000000 : ℝ)*(major0) + (1209322189476819/100000000000000 : ℝ)*(major1) + (1209322189476819/100000000000000 : ℝ)*(major2) + (74009707807821/4000000000000 : ℝ)*(sp0) + (1850242016672709/100000000000000 : ℝ)*(sp1) + (462560335281619/25000000000000 : ℝ)*(sp2) + (548882389432517/100000000000000 : ℝ)*(sp3) + (1073244593/100000000000000 : ℝ)*(sp5) + (1748790827/100000000000000 : ℝ)*(sp6) + (269726597/100000000000000 : ℝ)*(sp7) + (197360889/50000000000000 : ℝ)*(sp8) + (274441329579557/50000000000000 : ℝ)*(f.failure) + (925121544958651/50000000000000 : ℝ)*(f.sum) + (4052559910363/43280000000000000000000000000 : ℝ)*base66 + (5118452423134413641/865600000000000000000000000000000 : ℝ)*base68 + (7273239354136013641/865600000000000000000000000000000 : ℝ)*base70 + (2841760389337613641/865600000000000000000000000000000 : ℝ)*base72 + (51063478119163/43280000000000000000000000000 : ℝ)*base74 + (464475360863986359/865600000000000000000000000000000 : ℝ)*base75 + (5401820177382413641/865600000000000000000000000000000 : ℝ)*base78 + (7658240724779213641/865600000000000000000000000000000 : ℝ)*base80 + (155358628929723/43280000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (26369849/5000000000000000000000 : ℝ)*base89 + (26369849/5000000000000000000000 : ℝ)*base91 + (26369849/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (82073/100000 : ℝ) ≤ (177612284233444798127454631475577/216400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65172441/100000000000000 : ℝ)*(upper1) + (42931277/100000000000000 : ℝ)*(upper4) + (20324139/100000000000000 : ℝ)*(lower5) + (579808293319227/50000000000000 : ℝ)*(major0) + (579808293319227/50000000000000 : ℝ)*(major1) + (579808293319227/50000000000000 : ℝ)*(major2) + (16176832431/100000000000000 : ℝ)*(sp1) + (15597822717/50000000000000 : ℝ)*(sp2) + (5497874921/100000000000000 : ℝ)*(sp3) + (243846911/20000000000000 : ℝ)*(sp4) + (2758673203313/156250000000 : ℝ)*(sp8) + (1765535892522443/100000000000000 : ℝ)*(sp9) + (1765520873709441/100000000000000 : ℝ)*(sp10) + (52631696707091/10000000000000 : ℝ)*(sp11) + (65790308118229/12500000000000 : ℝ)*(f.failure) + (14124416554839/800000000000 : ℝ)*(f.sum) + (11438375287899/21640000000000000000000000000 : ℝ)*base66 + (104646436077506047/432800000000000000000000000000000 : ℝ)*base67 + (3577686328954306047/432800000000000000000000000000000 : ℝ)*base69 + (4072803248160706047/432800000000000000000000000000000 : ℝ)*base71 + (126185288822059/21640000000000000000000000000 : ℝ)*base74 + (6751203712892706047/432800000000000000000000000000000 : ℝ)*base75 + (2132442449228706047/432800000000000000000000000000000 : ℝ)*base77 + (2012781224867106047/432800000000000000000000000000000 : ℝ)*base79 + (70662812123941/21640000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (9403753/1250000000000000000000 : ℝ)*base89 + (9403753/1250000000000000000000 : ℝ)*base91 + (9403753/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-93063/100000 : ℝ) ≤ (-402767841093199311160402212776679/432800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92219307/100000000000000 : ℝ)*(upper3) + (243362951/100000000000000 : ℝ)*(lower4) + (94936459/50000000000000 : ℝ)*(upper5) + (1217583776659313/100000000000000 : ℝ)*(major0) + (1217583776659313/100000000000000 : ℝ)*(major1) + (1217583776659313/100000000000000 : ℝ)*(major2) + (22214277/781250000000 : ℝ)*(sp4) + (860498781/4000000000000 : ℝ)*(sp5) + (136239206703/100000000000000 : ℝ)*(sp6) + (12760852513/50000000000000 : ℝ)*(sp7) + (478388158184091/25000000000000 : ℝ)*(sp12) + (239191745461787/12500000000000 : ℝ)*(sp13) + (956709618478559/50000000000000 : ℝ)*(sp14) + (276303437964151/50000000000000 : ℝ)*(sp15) + (34539524852083/6250000000000 : ℝ)*(f.failure) + (95677773808191/5000000000000 : ℝ)*(f.sum) + (224590642868521/43280000000000000000000000000 : ℝ)*base66 + (2003977827161448893/865600000000000000000000000000000 : ℝ)*base67 + (11568482348924648893/865600000000000000000000000000000 : ℝ)*base69 + (1932449026768151107/865600000000000000000000000000000 : ℝ)*base72 + (130611937870681/43280000000000000000000000000 : ℝ)*base74 + (2401138803827048893/865600000000000000000000000000000 : ℝ)*base75 + (563501927155048893/865600000000000000000000000000000 : ℝ)*base77 + (137930953736151107/865600000000000000000000000000000 : ℝ)*base80 + (113062946134599/43280000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (835631/625000000000000000000 : ℝ)*base89 + (835631/625000000000000000000 : ℝ)*base91 + (835631/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1759_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (220324357/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17801/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1829/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2159/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(58553/100000 : ℝ) else (82073/100000 : ℝ) ≤ X j i ∧ X j i ≤ (93063/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1759_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1759_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (220324357/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8901/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1829/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2159/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(58553/100000 : ℝ) else (82073/100000 : ℝ) ≤ X j i ∧ X j i ≤ (93063/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1759_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1759_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (220324357/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8901/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1829/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2159/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(58553/100000 : ℝ) else (82073/100000 : ℝ) ≤ X j i ∧ X j i ≤ (93063/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1759_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

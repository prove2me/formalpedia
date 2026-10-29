-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1655_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:17:38.169045+00:00
-- url     : https://prove2.me/submissions/a4ee5ddb-cdb7-4083-ba24-03d5a72f4b6e

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
theorem support_rectangle_w1655_s3_0 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-798607879/5000000000 : ℝ)*x 0 + (1361529151/2500000000 : ℝ)*x 1 + (41473387/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (798607879/5000000000 : ℝ)^4939 ≤ (4942729869273/50000000000000 : ℝ)^3915 := by
    have hnat : (798607879 : ℕ)^4939*50000000000000^3915 ≤ 4942729869273^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      798607879 5000000000 4942729869273 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1361529151/2500000000 : ℝ)^4939 ≤ (4645776718521/10000000000000 : ℝ)^3915 := by
    have hnat : (1361529151 : ℕ)^4939*10000000000000^3915 ≤ 4645776718521^3915*2500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361529151 2500000000 4645776718521 10000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41473387/80000000 : ℝ)^4939 ≤ (4365677305251/10000000000000 : ℝ)^3915 := by
    have hnat : (41473387 : ℕ)^4939*10000000000000^3915 ≤ 4365677305251^3915*80000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41473387 80000000 4365677305251 10000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-798607879/5000000000 : ℝ), (1361529151/2500000000 : ℝ), (41473387/80000000 : ℝ)] ![(4942729869273/50000000000000 : ℝ), (4645776718521/10000000000000 : ℝ), (4365677305251/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-798607879/5000000000 : ℝ)|^4939 ≤ (4942729869273/50000000000000 : ℝ)^3915
        have hw : |(-798607879/5000000000 : ℝ)|=(798607879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1361529151/2500000000 : ℝ)|^4939 ≤ (4645776718521/10000000000000 : ℝ)^3915
        have hw : |(1361529151/2500000000 : ℝ)|=(1361529151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41473387/80000000 : ℝ)|^4939 ≤ (4365677305251/10000000000000 : ℝ)^3915
        have hw : |(41473387/80000000 : ℝ)|=(41473387/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s3_1 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (13367509/25000000 : ℝ)*x 0 + (-13856291/80000000 : ℝ)*x 1 + (1296043347/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13367509/25000000 : ℝ)^4939 ≤ (22696849138099/50000000000000 : ℝ)^3915 := by
    have hnat : (13367509 : ℕ)^4939*50000000000000^3915 ≤ 22696849138099^3915*25000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13367509 25000000 22696849138099 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13856291/80000000 : ℝ)^4939 ≤ (2737382128743/25000000000000 : ℝ)^3915 := by
    have hnat : (13856291 : ℕ)^4939*25000000000000^3915 ≤ 2737382128743^3915*80000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13856291 80000000 2737382128743 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296043347/2500000000 : ℝ)^4939 ≤ (43656773190619/100000000000000 : ℝ)^3915 := by
    have hnat : (1296043347 : ℕ)^4939*100000000000000^3915 ≤ 43656773190619^3915*2500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296043347 2500000000 43656773190619 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13367509/25000000 : ℝ), (-13856291/80000000 : ℝ), (1296043347/2500000000 : ℝ)] ![(22696849138099/50000000000000 : ℝ), (2737382128743/25000000000000 : ℝ), (43656773190619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13367509/25000000 : ℝ)|^4939 ≤ (22696849138099/50000000000000 : ℝ)^3915
        have hw : |(13367509/25000000 : ℝ)|=(13367509/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13856291/80000000 : ℝ)|^4939 ≤ (2737382128743/25000000000000 : ℝ)^3915
        have hw : |(-13856291/80000000 : ℝ)|=(13856291/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1296043347/2500000000 : ℝ)|^4939 ≤ (43656773190619/100000000000000 : ℝ)^3915
        have hw : |(1296043347/2500000000 : ℝ)|=(1296043347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s3_2 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673501803/5000000000 : ℝ)*x 0 + (2592086697/5000000000 : ℝ)*x 1 + (-43300909/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673501803/5000000000 : ℝ)^4939 ≤ (45393698340459/100000000000000 : ℝ)^3915 := by
    have hnat : (2673501803 : ℕ)^4939*100000000000000^3915 ≤ 45393698340459^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673501803 5000000000 45393698340459 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592086697/5000000000 : ℝ)^4939 ≤ (21828386627181/50000000000000 : ℝ)^3915 := by
    have hnat : (2592086697 : ℕ)^4939*50000000000000^3915 ≤ 21828386627181^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592086697 5000000000 21828386627181 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43300909/250000000 : ℝ)^4939 ≤ (10949528395343/100000000000000 : ℝ)^3915 := by
    have hnat : (43300909 : ℕ)^4939*100000000000000^3915 ≤ 10949528395343^3915*250000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43300909 250000000 10949528395343 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673501803/5000000000 : ℝ), (2592086697/5000000000 : ℝ), (-43300909/250000000 : ℝ)] ![(45393698340459/100000000000000 : ℝ), (21828386627181/50000000000000 : ℝ), (10949528395343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673501803/5000000000 : ℝ)|^4939 ≤ (45393698340459/100000000000000 : ℝ)^3915
        have hw : |(2673501803/5000000000 : ℝ)|=(2673501803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592086697/5000000000 : ℝ)|^4939 ≤ (21828386627181/50000000000000 : ℝ)^3915
        have hw : |(2592086697/5000000000 : ℝ)|=(2592086697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-43300909/250000000 : ℝ)|^4939 ≤ (10949528395343/100000000000000 : ℝ)^3915
        have hw : |(-43300909/250000000 : ℝ)|=(43300909/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s3_3 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2088451477/5000000000 : ℝ)*x 0 + (15383729/40000000 : ℝ)*x 1 + (4527915771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2088451477/5000000000 : ℝ)^4939 ≤ (8310473773301/25000000000000 : ℝ)^3915 := by
    have hnat : (2088451477 : ℕ)^4939*25000000000000^3915 ≤ 8310473773301^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088451477 5000000000 8310473773301 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15383729/40000000 : ℝ)^4939 ≤ (29954042389131/100000000000000 : ℝ)^3915 := by
    have hnat : (15383729 : ℕ)^4939*100000000000000^3915 ≤ 29954042389131^3915*40000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15383729 40000000 29954042389131 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4527915771/10000000000 : ℝ)^4939 ≤ (36804062497703/100000000000000 : ℝ)^3915 := by
    have hnat : (4527915771 : ℕ)^4939*100000000000000^3915 ≤ 36804062497703^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527915771 10000000000 36804062497703 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2088451477/5000000000 : ℝ), (15383729/40000000 : ℝ), (4527915771/10000000000 : ℝ)] ![(8310473773301/25000000000000 : ℝ), (29954042389131/100000000000000 : ℝ), (36804062497703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2088451477/5000000000 : ℝ)|^4939 ≤ (8310473773301/25000000000000 : ℝ)^3915
        have hw : |(2088451477/5000000000 : ℝ)|=(2088451477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(15383729/40000000 : ℝ)|^4939 ≤ (29954042389131/100000000000000 : ℝ)^3915
        have hw : |(15383729/40000000 : ℝ)|=(15383729/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4527915771/10000000000 : ℝ)|^4939 ≤ (36804062497703/100000000000000 : ℝ)^3915
        have hw : |(4527915771/10000000000 : ℝ)|=(4527915771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s3_4 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1597279423/10000000000 : ℝ)*x 0 + (2593080333/5000000000 : ℝ)*x 1 + (170128387/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1597279423/10000000000 : ℝ)^4939 ≤ (1977191367661/20000000000000 : ℝ)^3915 := by
    have hnat : (1597279423 : ℕ)^4939*20000000000000^3915 ≤ 1977191367661^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1597279423 10000000000 1977191367661 20000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593080333/5000000000 : ℝ)^4939 ≤ (43677886668043/100000000000000 : ℝ)^3915 := by
    have hnat : (2593080333 : ℕ)^4939*100000000000000^3915 ≤ 43677886668043^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593080333 5000000000 43677886668043 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170128387/312500000 : ℝ)^4939 ≤ (23218078238497/50000000000000 : ℝ)^3915 := by
    have hnat : (170128387 : ℕ)^4939*50000000000000^3915 ≤ 23218078238497^3915*312500000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170128387 312500000 23218078238497 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1597279423/10000000000 : ℝ), (2593080333/5000000000 : ℝ), (170128387/312500000 : ℝ)] ![(1977191367661/20000000000000 : ℝ), (43677886668043/100000000000000 : ℝ), (23218078238497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1597279423/10000000000 : ℝ)|^4939 ≤ (1977191367661/20000000000000 : ℝ)^3915
        have hw : |(-1597279423/10000000000 : ℝ)|=(1597279423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593080333/5000000000 : ℝ)|^4939 ≤ (43677886668043/100000000000000 : ℝ)^3915
        have hw : |(2593080333/5000000000 : ℝ)|=(2593080333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(170128387/312500000 : ℝ)|^4939 ≤ (23218078238497/50000000000000 : ℝ)^3915
        have hw : |(170128387/312500000 : ℝ)|=(170128387/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s3_5 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276983911/10000000000 : ℝ)*x 0 + (-294420299/2000000000 : ℝ)*x 1 + (2722054161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276983911/10000000000 : ℝ)^4939 ≤ (22322535440527/50000000000000 : ℝ)^3915 := by
    have hnat : (5276983911 : ℕ)^4939*50000000000000^3915 ≤ 22322535440527^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276983911 10000000000 22322535440527 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (294420299/2000000000 : ℝ)^4939 ≤ (8918773306519/100000000000000 : ℝ)^3915 := by
    have hnat : (294420299 : ℕ)^4939*100000000000000^3915 ≤ 8918773306519^3915*2000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294420299 2000000000 8918773306519 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2722054161/5000000000 : ℝ)^4939 ≤ (11609038952459/25000000000000 : ℝ)^3915 := by
    have hnat : (2722054161 : ℕ)^4939*25000000000000^3915 ≤ 11609038952459^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722054161 5000000000 11609038952459 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276983911/10000000000 : ℝ), (-294420299/2000000000 : ℝ), (2722054161/5000000000 : ℝ)] ![(22322535440527/50000000000000 : ℝ), (8918773306519/100000000000000 : ℝ), (11609038952459/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276983911/10000000000 : ℝ)|^4939 ≤ (22322535440527/50000000000000 : ℝ)^3915
        have hw : |(5276983911/10000000000 : ℝ)|=(5276983911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-294420299/2000000000 : ℝ)|^4939 ≤ (8918773306519/100000000000000 : ℝ)^3915
        have hw : |(-294420299/2000000000 : ℝ)|=(294420299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2722054161/5000000000 : ℝ)|^4939 ≤ (11609038952459/25000000000000 : ℝ)^3915
        have hw : |(2722054161/5000000000 : ℝ)|=(2722054161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s3_6 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276983937/10000000000 : ℝ)*x 0 + (1088821661/2000000000 : ℝ)*x 1 + (-36802537/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276983937/10000000000 : ℝ)^4939 ≤ (22322535579279/50000000000000 : ℝ)^3915 := by
    have hnat : (5276983937 : ℕ)^4939*50000000000000^3915 ≤ 22322535579279^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276983937 10000000000 22322535579279 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088821661/2000000000 : ℝ)^4939 ≤ (23218077813453/50000000000000 : ℝ)^3915 := by
    have hnat : (1088821661 : ℕ)^4939*50000000000000^3915 ≤ 23218077813453^3915*2000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088821661 2000000000 23218077813453 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36802537/250000000 : ℝ)^4939 ≤ (8918773191871/100000000000000 : ℝ)^3915 := by
    have hnat : (36802537 : ℕ)^4939*100000000000000^3915 ≤ 8918773191871^3915*250000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36802537 250000000 8918773191871 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276983937/10000000000 : ℝ), (1088821661/2000000000 : ℝ), (-36802537/250000000 : ℝ)] ![(22322535579279/50000000000000 : ℝ), (23218077813453/50000000000000 : ℝ), (8918773191871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276983937/10000000000 : ℝ)|^4939 ≤ (22322535579279/50000000000000 : ℝ)^3915
        have hw : |(5276983937/10000000000 : ℝ)|=(5276983937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088821661/2000000000 : ℝ)|^4939 ≤ (23218077813453/50000000000000 : ℝ)^3915
        have hw : |(1088821661/2000000000 : ℝ)|=(1088821661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-36802537/250000000 : ℝ)|^4939 ≤ (8918773191871/100000000000000 : ℝ)^3915
        have hw : |(-36802537/250000000 : ℝ)|=(36802537/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s3_7 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (417706881/1000000000 : ℝ)*x 0 + (4522741479/10000000000 : ℝ)*x 1 + (1925580523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417706881/1000000000 : ℝ)^4939 ≤ (33243560315019/100000000000000 : ℝ)^3915 := by
    have hnat : (417706881 : ℕ)^4939*100000000000000^3915 ≤ 33243560315019^3915*1000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417706881 1000000000 33243560315019 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4522741479/10000000000 : ℝ)^4939 ≤ (183755059253/500000000000 : ℝ)^3915 := by
    have hnat : (4522741479 : ℕ)^4939*500000000000^3915 ≤ 183755059253^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522741479 10000000000 183755059253 500000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1925580523/5000000000 : ℝ)^4939 ≤ (30005427814349/100000000000000 : ℝ)^3915 := by
    have hnat : (1925580523 : ℕ)^4939*100000000000000^3915 ≤ 30005427814349^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925580523 5000000000 30005427814349 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(417706881/1000000000 : ℝ), (4522741479/10000000000 : ℝ), (1925580523/5000000000 : ℝ)] ![(33243560315019/100000000000000 : ℝ), (183755059253/500000000000 : ℝ), (30005427814349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(417706881/1000000000 : ℝ)|^4939 ≤ (33243560315019/100000000000000 : ℝ)^3915
        have hw : |(417706881/1000000000 : ℝ)|=(417706881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4522741479/10000000000 : ℝ)|^4939 ≤ (183755059253/500000000000 : ℝ)^3915
        have hw : |(4522741479/10000000000 : ℝ)|=(4522741479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1925580523/5000000000 : ℝ)|^4939 ≤ (30005427814349/100000000000000 : ℝ)^3915
        have hw : |(1925580523/5000000000 : ℝ)|=(1925580523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1655_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90088869/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16329/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1329/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2673/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8131/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16329/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1329/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16329/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1329/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16329/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1329/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16329/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1329/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16329/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1329/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16329/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1329/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1329/12500 : ℝ) ^ (4935/1024 : ℝ) ≤ (2036716275811831/100000000000000000000 : ℝ) := by
    have hpowers : (1329/12500 : ℝ)^4935 ≤ (2036716275811831/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1329 : ℕ)^4935*100000000000000000000^1024 ≤ 2036716275811831^1024*12500^4935 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1329 12500 2036716275811831 100000000000000000000 4935 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1329/12500 : ℝ)) (X := (2036716275811831/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16329/100000 : ℝ) ^ (4935/1024 : ℝ) ≤ (16106006246062489/100000000000000000000 : ℝ) := by
    have hpowers : (16329/100000 : ℝ)^4935 ≤ (16106006246062489/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16329 : ℕ)^4935*100000000000000000000^1024 ≤ 16106006246062489^1024*100000^4935 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16329 100000 16106006246062489 100000000000000000000 4935 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16329/100000 : ℝ)) (X := (16106006246062489/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002036716275811831/50000000000000000000 : ℝ) ≤ (5000042260664713/5000000000000000 : ℝ) ^ (4935/1024 : ℝ) := by
    have hpowers : (50002036716275811831/50000000000000000000 : ℝ)^1024 ≤ (5000042260664713/5000000000000000 : ℝ)^4935 := by
      have hnat : (50002036716275811831 : ℕ)^1024*5000000000000000^4935 ≤ 5000042260664713^4935*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002036716275811831 50000000000000000000 5000042260664713 5000000000000000 1024 4935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000042260664713/5000000000000000 : ℝ)) (X := (50002036716275811831/50000000000000000000 : ℝ)) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1250226784031523429/1250000000000000000 : ℝ) ≤ (5000188214918033/5000000000000000 : ℝ) ^ (4935/1024 : ℝ) := by
    have hpowers : (1250226784031523429/1250000000000000000 : ℝ)^1024 ≤ (5000188214918033/5000000000000000 : ℝ)^4935 := by
      have hnat : (1250226784031523429 : ℕ)^1024*5000000000000000^4935 ≤ 5000188214918033^4935*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250226784031523429 1250000000000000000 5000188214918033 5000000000000000 1024 4935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000188214918033/5000000000000000 : ℝ)) (X := (1250226784031523429/1250000000000000000 : ℝ)) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016106006246062489/50000000000000000000 : ℝ) ≤ (5000334169171353/5000000000000000 : ℝ) ^ (4935/1024 : ℝ) := by
    have hpowers : (50016106006246062489/50000000000000000000 : ℝ)^1024 ≤ (5000334169171353/5000000000000000 : ℝ)^4935 := by
      have hnat : (50016106006246062489 : ℕ)^1024*5000000000000000^4935 ≤ 5000334169171353^4935*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016106006246062489 50000000000000000000 5000334169171353 5000000000000000 1024 4935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000334169171353/5000000000000000 : ℝ)) (X := (50016106006246062489/50000000000000000000 : ℝ)) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2036716275811831/100000000000000000000 : ℝ) ≤ ((9494045729254757827/9495000000000000000 : ℝ)+2*(3648856333/7121250000000 : ℝ)*(1329/12500 : ℝ))^(4935/1024 : ℝ) := by
    rw [show (9494045729254757827/9495000000000000000 : ℝ)+2*(3648856333/7121250000000 : ℝ)*(1329/12500 : ℝ)=(5000042260664713/5000000000000000 : ℝ) by norm_num, show 1+2*(2036716275811831/100000000000000000000 : ℝ)=(50002036716275811831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16106006246062489/100000000000000000000 : ℝ)+(2036716275811831/100000000000000000000 : ℝ) ≤ ((9494045729254757827/9495000000000000000 : ℝ)+(3648856333/7121250000000 : ℝ)*((16329/100000 : ℝ)+(1329/12500 : ℝ)))^(4935/1024 : ℝ) := by
    rw [show (9494045729254757827/9495000000000000000 : ℝ)+(3648856333/7121250000000 : ℝ)*((16329/100000 : ℝ)+(1329/12500 : ℝ))=(5000188214918033/5000000000000000 : ℝ) by norm_num, show 1+(16106006246062489/100000000000000000000 : ℝ)+(2036716275811831/100000000000000000000 : ℝ)=(1250226784031523429/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16106006246062489/100000000000000000000 : ℝ) ≤ ((9494045729254757827/9495000000000000000 : ℝ)+2*(3648856333/7121250000000 : ℝ)*(16329/100000 : ℝ))^(4935/1024 : ℝ) := by
    rw [show (9494045729254757827/9495000000000000000 : ℝ)+2*(3648856333/7121250000000 : ℝ)*(16329/100000 : ℝ)=(5000334169171353/5000000000000000 : ℝ) by norm_num, show 1+2*(16106006246062489/100000000000000000000 : ℝ)=(50016106006246062489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9494045729254757827/9495000000000000000 : ℝ)*(X 1 0+X 2 0)+(3648856333/7121250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4935/1024 : ℝ)) (lo := (1329/12500 : ℝ)) (hi := (16329/100000 : ℝ)) (c := (9494045729254757827/9495000000000000000 : ℝ)) (alpha := (3648856333/7121250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9494045729254757827/9495000000000000000 : ℝ)*(X 0 1+X 2 1)+(3648856333/7121250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4935/1024 : ℝ)) (lo := (1329/12500 : ℝ)) (hi := (16329/100000 : ℝ)) (c := (9494045729254757827/9495000000000000000 : ℝ)) (alpha := (3648856333/7121250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9494045729254757827/9495000000000000000 : ℝ)*(X 0 2+X 1 2)+(3648856333/7121250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4935/1024 : ℝ)) (lo := (1329/12500 : ℝ)) (hi := (16329/100000 : ℝ)) (c := (9494045729254757827/9495000000000000000 : ℝ)) (alpha := (3648856333/7121250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-798607879/5000000000 : ℝ)*X 0 0+(1361529151/2500000000 : ℝ)*X 0 1+(41473387/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((13367509/25000000 : ℝ)*X 1 0+(-13856291/80000000 : ℝ)*X 1 1+(1296043347/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673501803/5000000000 : ℝ)*X 2 0+(2592086697/5000000000 : ℝ)*X 2 1+(-43300909/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2088451477/5000000000 : ℝ)*X 0 0+(15383729/40000000 : ℝ)*X 0 1+(4527915771/10000000000 : ℝ)*X 0 2+(2088451477/5000000000 : ℝ)*X 1 0+(15383729/40000000 : ℝ)*X 1 1+(4527915771/10000000000 : ℝ)*X 1 2+(2088451477/5000000000 : ℝ)*X 2 0+(15383729/40000000 : ℝ)*X 2 1+(4527915771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1597279423/10000000000 : ℝ)*X 0 0+(2593080333/5000000000 : ℝ)*X 0 1+(170128387/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276983911/10000000000 : ℝ)*X 1 0+(-294420299/2000000000 : ℝ)*X 1 1+(2722054161/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5276983937/10000000000 : ℝ)*X 2 0+(1088821661/2000000000 : ℝ)*X 2 1+(-36802537/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((417706881/1000000000 : ℝ)*X 0 0+(4522741479/10000000000 : ℝ)*X 0 1+(1925580523/5000000000 : ℝ)*X 0 2+(417706881/1000000000 : ℝ)*X 1 0+(4522741479/10000000000 : ℝ)*X 1 1+(1925580523/5000000000 : ℝ)*X 1 2+(417706881/1000000000 : ℝ)*X 2 0+(4522741479/10000000000 : ℝ)*X 2 1+(1925580523/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57634853366818528057204283/5275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1752958459/100000000000000 : ℝ)*(base19) + (1644289711/100000000000000 : ℝ)*(base23) + (30197909/50000000000000 : ℝ)*(lower2) + (67381951/25000000000000 : ℝ)*(upper3) + (40348551/20000000000000 : ℝ)*(upper5) + (264199742679929/10000000000000 : ℝ)*(major0) + (264199742679929/10000000000000 : ℝ)*(major1) + (264199742679929/10000000000000 : ℝ)*(major2) + (3817643743742653/100000000000000 : ℝ)*(sp0) + (1908832144901411/50000000000000 : ℝ)*(sp1) + (381766439847157/10000000000000 : ℝ)*(sp2) + (733159648773711/50000000000000 : ℝ)*(sp3) + (22299018627/100000000000000 : ℝ)*(sp4) + (4574544291/50000000000000 : ℝ)*(sp7) + (293265689327201/20000000000000 : ℝ)*(f.failure) + (11930206383629/312500000000 : ℝ)*(f.sum) + (26567772944459/5697000000000000000000000000 : ℝ)*base65 + (525216796245537151/284850000000000000000000000000000 : ℝ)*base68 + (35819858144787151/284850000000000000000000000000000 : ℝ)*base70 + (3173889660565137151/284850000000000000000000000000000 : ℝ)*base72 + (7621644625901/1424250000000000000000000000 : ℝ)*base73 + (3688271466405837151/284850000000000000000000000000000 : ℝ)*base76 + (1223898344932137151/284850000000000000000000000000000 : ℝ)*base78 + (3403447327367637151/284850000000000000000000000000000 : ℝ)*base80 + (21850436542561/2848500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (9025669/1000000000000000000000 : ℝ)*base89 + (9025669/1000000000000000000000 : ℝ)*base91 + (9025669/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62507281802492599820873999/13187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (321519791/50000000000000 : ℝ)*(base19) + (370223483/50000000000000 : ℝ)*(base23) + (67591193/100000000000000 : ℝ)*(upper3) + (21239183/50000000000000 : ℝ)*(lower4) + (1133621/800000000000 : ℝ)*(upper5) + (670722521315263/25000000000000 : ℝ)*(major0) + (670722521315263/25000000000000 : ℝ)*(major1) + (670722521315263/25000000000000 : ℝ)*(major2) + (7745584121/100000000000000 : ℝ)*(sp1) + (758045997/10000000000000 : ℝ)*(sp2) + (387675583282329/10000000000000 : ℝ)*(sp4) + (969186861049897/25000000000000 : ℝ)*(sp5) + (1938373755958177/50000000000000 : ℝ)*(sp6) + (744512089851259/50000000000000 : ℝ)*(sp7) + (744512089851259/50000000000000 : ℝ)*(f.failure) + (387675583282329/10000000000000 : ℝ)*(f.sum) + (10489446752107/2848500000000000000000000000 : ℝ)*base66 + (2242274845115690503/712125000000000000000000000000000 : ℝ)*base67 + (8137586043562940503/712125000000000000000000000000000 : ℝ)*base69 + (1573893842310440503/712125000000000000000000000000000 : ℝ)*base71 + (11679434162783/5697000000000000000000000000 : ℝ)*base74 + (10427865552684440503/712125000000000000000000000000000 : ℝ)*base75 + (4681896999154190503/712125000000000000000000000000000 : ℝ)*base77 + (8148606118119440503/712125000000000000000000000000000 : ℝ)*base79 + (1436767607821/284850000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1536071/2500000000000000000000 : ℝ)*base89 + (1536071/2500000000000000000000 : ℝ)*base91 + (1536071/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1655_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90088869/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16329/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1329/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2673/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8131/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1655_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1655_s4_0 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-798629189/5000000000 : ℝ)*x 0 + (5445912669/10000000000 : ℝ)*x 1 + (648043579/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (798629189/5000000000 : ℝ)^4939 ≤ (1977158503447/20000000000000 : ℝ)^3915 := by
    have hnat : (798629189 : ℕ)^4939*20000000000000^3915 ≤ 1977158503447^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      798629189 5000000000 1977158503447 20000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5445912669/10000000000 : ℝ)^4939 ≤ (23227786259953/50000000000000 : ℝ)^3915 := by
    have hnat : (5445912669 : ℕ)^4939*50000000000000^3915 ≤ 23227786259953^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445912669 10000000000 23227786259953 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (648043579/1250000000 : ℝ)^4939 ≤ (2182931747693/5000000000000 : ℝ)^3915 := by
    have hnat : (648043579 : ℕ)^4939*5000000000000^3915 ≤ 2182931747693^3915*1250000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648043579 1250000000 2182931747693 5000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-798629189/5000000000 : ℝ), (5445912669/10000000000 : ℝ), (648043579/1250000000 : ℝ)] ![(1977158503447/20000000000000 : ℝ), (23227786259953/50000000000000 : ℝ), (2182931747693/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-798629189/5000000000 : ℝ)|^4939 ≤ (1977158503447/20000000000000 : ℝ)^3915
        have hw : |(-798629189/5000000000 : ℝ)|=(798629189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5445912669/10000000000 : ℝ)|^4939 ≤ (23227786259953/50000000000000 : ℝ)^3915
        have hw : |(5445912669/10000000000 : ℝ)|=(5445912669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(648043579/1250000000 : ℝ)|^4939 ≤ (2182931747693/5000000000000 : ℝ)^3915
        have hw : |(648043579/1250000000 : ℝ)|=(648043579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s4_1 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673475643/5000000000 : ℝ)*x 0 + (-865934781/5000000000 : ℝ)*x 1 + (5184351351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673475643/5000000000 : ℝ)^4939 ≤ (45393137990261/100000000000000 : ℝ)^3915 := by
    have hnat : (2673475643 : ℕ)^4939*100000000000000^3915 ≤ 45393137990261^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673475643 5000000000 45393137990261 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (865934781/5000000000 : ℝ)^4939 ≤ (10948198152171/100000000000000 : ℝ)^3915 := by
    have hnat : (865934781 : ℕ)^4939*100000000000000^3915 ≤ 10948198152171^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865934781 5000000000 10948198152171 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184351351/10000000000 : ℝ)^4939 ≤ (10914665960049/25000000000000 : ℝ)^3915 := by
    have hnat : (5184351351 : ℕ)^4939*25000000000000^3915 ≤ 10914665960049^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184351351 10000000000 10914665960049 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673475643/5000000000 : ℝ), (-865934781/5000000000 : ℝ), (5184351351/10000000000 : ℝ)] ![(45393137990261/100000000000000 : ℝ), (10948198152171/100000000000000 : ℝ), (10914665960049/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673475643/5000000000 : ℝ)|^4939 ≤ (45393137990261/100000000000000 : ℝ)^3915
        have hw : |(2673475643/5000000000 : ℝ)|=(2673475643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-865934781/5000000000 : ℝ)|^4939 ≤ (10948198152171/100000000000000 : ℝ)^3915
        have hw : |(-865934781/5000000000 : ℝ)|=(865934781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184351351/10000000000 : ℝ)|^4939 ≤ (10914665960049/25000000000000 : ℝ)^3915
        have hw : |(5184351351/10000000000 : ℝ)|=(5184351351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s4_2 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673473239/5000000000 : ℝ)*x 0 + (5184350173/10000000000 : ℝ)*x 1 + (-432969397/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673473239/5000000000 : ℝ)^4939 ≤ (45393086496377/100000000000000 : ℝ)^3915 := by
    have hnat : (2673473239 : ℕ)^4939*100000000000000^3915 ≤ 45393086496377^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673473239 5000000000 45393086496377 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184350173/10000000000 : ℝ)^4939 ≤ (21829325662631/50000000000000 : ℝ)^3915 := by
    have hnat : (5184350173 : ℕ)^4939*50000000000000^3915 ≤ 21829325662631^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184350173 10000000000 21829325662631 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (432969397/2500000000 : ℝ)^4939 ≤ (2189652432031/20000000000000 : ℝ)^3915 := by
    have hnat : (432969397 : ℕ)^4939*20000000000000^3915 ≤ 2189652432031^3915*2500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432969397 2500000000 2189652432031 20000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673473239/5000000000 : ℝ), (5184350173/10000000000 : ℝ), (-432969397/2500000000 : ℝ)] ![(45393086496377/100000000000000 : ℝ), (21829325662631/50000000000000 : ℝ), (2189652432031/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673473239/5000000000 : ℝ)|^4939 ≤ (45393086496377/100000000000000 : ℝ)^3915
        have hw : |(2673473239/5000000000 : ℝ)|=(2673473239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184350173/10000000000 : ℝ)|^4939 ≤ (21829325662631/50000000000000 : ℝ)^3915
        have hw : |(5184350173/10000000000 : ℝ)|=(5184350173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-432969397/2500000000 : ℝ)|^4939 ≤ (2189652432031/20000000000000 : ℝ)^3915
        have hw : |(-432969397/2500000000 : ℝ)|=(432969397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s4_3 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4176914743/10000000000 : ℝ)*x 0 + (961606863/2500000000 : ℝ)*x 1 + (4527429711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4176914743/10000000000 : ℝ)^4939 ≤ (33242013456153/100000000000000 : ℝ)^3915 := by
    have hnat : (4176914743 : ℕ)^4939*100000000000000^3915 ≤ 33242013456153^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4176914743 10000000000 33242013456153 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (961606863/2500000000 : ℝ)^4939 ≤ (7489727037533/25000000000000 : ℝ)^3915 := by
    have hnat : (961606863 : ℕ)^4939*25000000000000^3915 ≤ 7489727037533^3915*2500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961606863 2500000000 7489727037533 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4527429711/10000000000 : ℝ)^4939 ≤ (9199769594497/25000000000000 : ℝ)^3915 := by
    have hnat : (4527429711 : ℕ)^4939*25000000000000^3915 ≤ 9199769594497^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527429711 10000000000 9199769594497 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4176914743/10000000000 : ℝ), (961606863/2500000000 : ℝ), (4527429711/10000000000 : ℝ)] ![(33242013456153/100000000000000 : ℝ), (7489727037533/25000000000000 : ℝ), (9199769594497/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4176914743/10000000000 : ℝ)|^4939 ≤ (33242013456153/100000000000000 : ℝ)^3915
        have hw : |(4176914743/10000000000 : ℝ)|=(4176914743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(961606863/2500000000 : ℝ)|^4939 ≤ (7489727037533/25000000000000 : ℝ)^3915
        have hw : |(961606863/2500000000 : ℝ)|=(961606863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4527429711/10000000000 : ℝ)|^4939 ≤ (9199769594497/25000000000000 : ℝ)^3915
        have hw : |(4527429711/10000000000 : ℝ)|=(4527429711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s4_4 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1597319207/10000000000 : ℝ)*x 0 + (5186331383/10000000000 : ℝ)*x 1 + (680488869/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1597319207/10000000000 : ℝ)^4939 ≤ (9886267476557/100000000000000 : ℝ)^3915 := by
    have hnat : (1597319207 : ℕ)^4939*100000000000000^3915 ≤ 9886267476557^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1597319207 10000000000 9886267476557 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186331383/10000000000 : ℝ)^4939 ≤ (43679700518797/100000000000000 : ℝ)^3915 := by
    have hnat : (5186331383 : ℕ)^4939*100000000000000^3915 ≤ 43679700518797^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186331383 10000000000 43679700518797 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (680488869/1250000000 : ℝ)^4939 ≤ (1451063499967/3125000000000 : ℝ)^3915 := by
    have hnat : (680488869 : ℕ)^4939*3125000000000^3915 ≤ 1451063499967^3915*1250000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680488869 1250000000 1451063499967 3125000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1597319207/10000000000 : ℝ), (5186331383/10000000000 : ℝ), (680488869/1250000000 : ℝ)] ![(9886267476557/100000000000000 : ℝ), (43679700518797/100000000000000 : ℝ), (1451063499967/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1597319207/10000000000 : ℝ)|^4939 ≤ (9886267476557/100000000000000 : ℝ)^3915
        have hw : |(-1597319207/10000000000 : ℝ)|=(1597319207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186331383/10000000000 : ℝ)|^4939 ≤ (43679700518797/100000000000000 : ℝ)^3915
        have hw : |(5186331383/10000000000 : ℝ)|=(5186331383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(680488869/1250000000 : ℝ)|^4939 ≤ (1451063499967/3125000000000 : ℝ)^3915
        have hw : |(680488869/1250000000 : ℝ)|=(680488869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s4_5 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277030603/10000000000 : ℝ)*x 0 + (-368078561/2500000000 : ℝ)*x 1 + (5443910889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277030603/10000000000 : ℝ)^4939 ≤ (44645569235097/100000000000000 : ℝ)^3915 := by
    have hnat : (5277030603 : ℕ)^4939*100000000000000^3915 ≤ 44645569235097^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277030603 10000000000 44645569235097 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (368078561/2500000000 : ℝ)^4939 ≤ (8920399418189/100000000000000 : ℝ)^3915 := by
    have hnat : (368078561 : ℕ)^4939*100000000000000^3915 ≤ 8920399418189^3915*2500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368078561 2500000000 8920399418189 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5443910889/10000000000 : ℝ)^4939 ≤ (46434031321033/100000000000000 : ℝ)^3915 := by
    have hnat : (5443910889 : ℕ)^4939*100000000000000^3915 ≤ 46434031321033^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443910889 10000000000 46434031321033 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277030603/10000000000 : ℝ), (-368078561/2500000000 : ℝ), (5443910889/10000000000 : ℝ)] ![(44645569235097/100000000000000 : ℝ), (8920399418189/100000000000000 : ℝ), (46434031321033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277030603/10000000000 : ℝ)|^4939 ≤ (44645569235097/100000000000000 : ℝ)^3915
        have hw : |(5277030603/10000000000 : ℝ)|=(5277030603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-368078561/2500000000 : ℝ)|^4939 ≤ (8920399418189/100000000000000 : ℝ)^3915
        have hw : |(-368078561/2500000000 : ℝ)|=(368078561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5443910889/10000000000 : ℝ)|^4939 ≤ (46434031321033/100000000000000 : ℝ)^3915
        have hw : |(5443910889/10000000000 : ℝ)|=(5443910889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s4_6 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055406123/2000000000 : ℝ)*x 0 + (5443910623/10000000000 : ℝ)*x 1 + (-368078651/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055406123/2000000000 : ℝ)^4939 ≤ (5580696170397/12500000000000 : ℝ)^3915 := by
    have hnat : (1055406123 : ℕ)^4939*12500000000000^3915 ≤ 5580696170397^3915*2000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055406123 2000000000 5580696170397 12500000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443910623/10000000000 : ℝ)^4939 ≤ (23217014229369/50000000000000 : ℝ)^3915 := by
    have hnat : (5443910623 : ℕ)^4939*50000000000000^3915 ≤ 23217014229369^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443910623 10000000000 23217014229369 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (368078651/2500000000 : ℝ)^4939 ≤ (8920402169841/100000000000000 : ℝ)^3915 := by
    have hnat : (368078651 : ℕ)^4939*100000000000000^3915 ≤ 8920402169841^3915*2500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368078651 2500000000 8920402169841 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055406123/2000000000 : ℝ), (5443910623/10000000000 : ℝ), (-368078651/2500000000 : ℝ)] ![(5580696170397/12500000000000 : ℝ), (23217014229369/50000000000000 : ℝ), (8920402169841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055406123/2000000000 : ℝ)|^4939 ≤ (5580696170397/12500000000000 : ℝ)^3915
        have hw : |(1055406123/2000000000 : ℝ)|=(1055406123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443910623/10000000000 : ℝ)|^4939 ≤ (23217014229369/50000000000000 : ℝ)^3915
        have hw : |(5443910623/10000000000 : ℝ)|=(5443910623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-368078651/2500000000 : ℝ)|^4939 ≤ (8920402169841/100000000000000 : ℝ)^3915
        have hw : |(-368078651/2500000000 : ℝ)|=(368078651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s4_7 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2088547109/5000000000 : ℝ)*x 0 + (226112973/500000000 : ℝ)*x 1 + (1925818897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2088547109/5000000000 : ℝ)^4939 ≤ (33243815417091/100000000000000 : ℝ)^3915 := by
    have hnat : (2088547109 : ℕ)^4939*100000000000000^3915 ≤ 33243815417091^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088547109 5000000000 33243815417091 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226112973/500000000 : ℝ)^4939 ≤ (18373035322639/50000000000000 : ℝ)^3915 := by
    have hnat : (226112973 : ℕ)^4939*50000000000000^3915 ≤ 18373035322639^3915*500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226112973 500000000 18373035322639 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1925818897/5000000000 : ℝ)^4939 ≤ (15005056955887/50000000000000 : ℝ)^3915 := by
    have hnat : (1925818897 : ℕ)^4939*50000000000000^3915 ≤ 15005056955887^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925818897 5000000000 15005056955887 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2088547109/5000000000 : ℝ), (226112973/500000000 : ℝ), (1925818897/5000000000 : ℝ)] ![(33243815417091/100000000000000 : ℝ), (18373035322639/50000000000000 : ℝ), (15005056955887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2088547109/5000000000 : ℝ)|^4939 ≤ (33243815417091/100000000000000 : ℝ)^3915
        have hw : |(2088547109/5000000000 : ℝ)|=(2088547109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226112973/500000000 : ℝ)|^4939 ≤ (18373035322639/50000000000000 : ℝ)^3915
        have hw : |(226112973/500000000 : ℝ)|=(226112973/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1925818897/5000000000 : ℝ)|^4939 ≤ (15005056955887/50000000000000 : ℝ)^3915
        have hw : |(1925818897/5000000000 : ℝ)|=(1925818897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1655_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90088869/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8131/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2673/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1337/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8129/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8131/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2673/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8131/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2673/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8131/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2673/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8131/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2673/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8131/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2673/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8131/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2673/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2673/25000 : ℝ) ^ (4935/1024 : ℝ) ≤ (2092709303034387/100000000000000000000 : ℝ) := by
    have hpowers : (2673/25000 : ℝ)^4935 ≤ (2092709303034387/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2673 : ℕ)^4935*100000000000000000000^1024 ≤ 2092709303034387^1024*25000^4935 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2673 25000 2092709303034387 100000000000000000000 4935 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2673/25000 : ℝ)) (X := (2092709303034387/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8131/50000 : ℝ) ^ (4935/1024 : ℝ) ≤ (7895003112546331/50000000000000000000 : ℝ) := by
    have hpowers : (8131/50000 : ℝ)^4935 ≤ (7895003112546331/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8131 : ℕ)^4935*50000000000000000000^1024 ≤ 7895003112546331^1024*50000^4935 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8131 50000 7895003112546331 50000000000000000000 4935 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8131/50000 : ℝ)) (X := (7895003112546331/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002092709303034387/50000000000000000000 : ℝ) ≤ (312502713904239/312500000000000 : ℝ) ^ (4935/1024 : ℝ) := by
    have hpowers : (50002092709303034387/50000000000000000000 : ℝ)^1024 ≤ (312502713904239/312500000000000 : ℝ)^4935 := by
      have hnat : (50002092709303034387 : ℕ)^1024*312500000000000^4935 ≤ 312502713904239^4935*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002092709303034387 50000000000000000000 312502713904239 312500000000000 1024 4935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312502713904239/312500000000000 : ℝ)) (X := (50002092709303034387/50000000000000000000 : ℝ)) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100017882715528127049/100000000000000000000 : ℝ) ≤ (5000185517763417/5000000000000000 : ℝ) ^ (4935/1024 : ℝ) := by
    have hpowers : (100017882715528127049/100000000000000000000 : ℝ)^1024 ≤ (5000185517763417/5000000000000000 : ℝ)^4935 := by
      have hnat : (100017882715528127049 : ℕ)^1024*5000000000000000^4935 ≤ 5000185517763417^4935*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100017882715528127049 100000000000000000000 5000185517763417 5000000000000000 1024 4935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000185517763417/5000000000000000 : ℝ)) (X := (100017882715528127049/100000000000000000000 : ℝ)) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25007895003112546331/25000000000000000000 : ℝ) ≤ (500032761305901/500000000000000 : ℝ) ^ (4935/1024 : ℝ) := by
    have hpowers : (25007895003112546331/25000000000000000000 : ℝ)^1024 ≤ (500032761305901/500000000000000 : ℝ)^4935 := by
      have hnat : (25007895003112546331 : ℕ)^1024*500000000000000^4935 ≤ 500032761305901^4935*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007895003112546331 25000000000000000000 500032761305901 500000000000000 1024 4935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500032761305901/500000000000000 : ℝ)) (X := (25007895003112546331/25000000000000000000 : ℝ)) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2092709303034387/100000000000000000000 : ℝ) ≤ ((3480900412168102371/3481250000000000000 : ℝ)+2*(142095295593/278500000000000 : ℝ)*(2673/25000 : ℝ))^(4935/1024 : ℝ) := by
    rw [show (3480900412168102371/3481250000000000000 : ℝ)+2*(142095295593/278500000000000 : ℝ)*(2673/25000 : ℝ)=(312502713904239/312500000000000 : ℝ) by norm_num, show 1+2*(2092709303034387/100000000000000000000 : ℝ)=(50002092709303034387/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7895003112546331/50000000000000000000 : ℝ)+(2092709303034387/100000000000000000000 : ℝ) ≤ ((3480900412168102371/3481250000000000000 : ℝ)+(142095295593/278500000000000 : ℝ)*((8131/50000 : ℝ)+(2673/25000 : ℝ)))^(4935/1024 : ℝ) := by
    rw [show (3480900412168102371/3481250000000000000 : ℝ)+(142095295593/278500000000000 : ℝ)*((8131/50000 : ℝ)+(2673/25000 : ℝ))=(5000185517763417/5000000000000000 : ℝ) by norm_num, show 1+(7895003112546331/50000000000000000000 : ℝ)+(2092709303034387/100000000000000000000 : ℝ)=(100017882715528127049/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7895003112546331/50000000000000000000 : ℝ) ≤ ((3480900412168102371/3481250000000000000 : ℝ)+2*(142095295593/278500000000000 : ℝ)*(8131/50000 : ℝ))^(4935/1024 : ℝ) := by
    rw [show (3480900412168102371/3481250000000000000 : ℝ)+2*(142095295593/278500000000000 : ℝ)*(8131/50000 : ℝ)=(500032761305901/500000000000000 : ℝ) by norm_num, show 1+2*(7895003112546331/50000000000000000000 : ℝ)=(25007895003112546331/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3480900412168102371/3481250000000000000 : ℝ)*(X 1 0+X 2 0)+(142095295593/278500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4935/1024 : ℝ)) (lo := (2673/25000 : ℝ)) (hi := (8131/50000 : ℝ)) (c := (3480900412168102371/3481250000000000000 : ℝ)) (alpha := (142095295593/278500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3480900412168102371/3481250000000000000 : ℝ)*(X 0 1+X 2 1)+(142095295593/278500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4935/1024 : ℝ)) (lo := (2673/25000 : ℝ)) (hi := (8131/50000 : ℝ)) (c := (3480900412168102371/3481250000000000000 : ℝ)) (alpha := (142095295593/278500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3480900412168102371/3481250000000000000 : ℝ)*(X 0 2+X 1 2)+(142095295593/278500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4935/1024 : ℝ)) (lo := (2673/25000 : ℝ)) (hi := (8131/50000 : ℝ)) (c := (3480900412168102371/3481250000000000000 : ℝ)) (alpha := (142095295593/278500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-798629189/5000000000 : ℝ)*X 0 0+(5445912669/10000000000 : ℝ)*X 0 1+(648043579/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673475643/5000000000 : ℝ)*X 1 0+(-865934781/5000000000 : ℝ)*X 1 1+(5184351351/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673473239/5000000000 : ℝ)*X 2 0+(5184350173/10000000000 : ℝ)*X 2 1+(-432969397/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4176914743/10000000000 : ℝ)*X 0 0+(961606863/2500000000 : ℝ)*X 0 1+(4527429711/10000000000 : ℝ)*X 0 2+(4176914743/10000000000 : ℝ)*X 1 0+(961606863/2500000000 : ℝ)*X 1 1+(4527429711/10000000000 : ℝ)*X 1 2+(4176914743/10000000000 : ℝ)*X 2 0+(961606863/2500000000 : ℝ)*X 2 1+(4527429711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1597319207/10000000000 : ℝ)*X 0 0+(5186331383/10000000000 : ℝ)*X 0 1+(680488869/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277030603/10000000000 : ℝ)*X 1 0+(-368078561/2500000000 : ℝ)*X 1 1+(5443910889/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055406123/2000000000 : ℝ)*X 2 0+(5443910623/10000000000 : ℝ)*X 2 1+(-368078651/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2088547109/5000000000 : ℝ)*X 0 0+(226112973/500000000 : ℝ)*X 0 1+(1925818897/5000000000 : ℝ)*X 0 2+(2088547109/5000000000 : ℝ)*X 1 0+(226112973/500000000 : ℝ)*X 1 1+(1925818897/5000000000 : ℝ)*X 1 2+(2088547109/5000000000 : ℝ)*X 2 0+(226112973/500000000 : ℝ)*X 2 1+(1925818897/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (137421422017246099474331091/21757812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (283362687/100000000000000 : ℝ)*(base19) + (390040021/20000000000000 : ℝ)*(base23) + (3026547369/100000000000000 : ℝ)*(upper2) + (399900621/50000000000000 : ℝ)*(lower5) + (661479549832637/25000000000000 : ℝ)*(major0) + (661479549832637/25000000000000 : ℝ)*(major1) + (661479549832637/25000000000000 : ℝ)*(major2) + (1911643187690501/50000000000000 : ℝ)*(sp0) + (1911665699940559/50000000000000 : ℝ)*(sp1) + (3823287247608709/100000000000000 : ℝ)*(sp2) + (91779399326789/6250000000000 : ℝ)*(sp3) + (22653931401/50000000000000 : ℝ)*(sp4) + (4248543499/10000000000000 : ℝ)*(sp6) + (34115656739/100000000000000 : ℝ)*(sp7) + (367126126221341/25000000000000 : ℝ)*(f.failure) + (955832920810951/25000000000000 : ℝ)*(f.sum) + (5644995765783/1740625000000000000000000000 : ℝ)*base65 + (1126794542847769827/87031250000000000000000000000000 : ℝ)*base67 + (849389247497457327/87031250000000000000000000000000 : ℝ)*base69 + (286077890593082327/87031250000000000000000000000000 : ℝ)*base71 + (3493068254341/3481250000000000000000000000 : ℝ)*base73 + (11801050145894827/87031250000000000000000000000000 : ℝ)*base75 + (269134820557457327/87031250000000000000000000000000 : ℝ)*base77 + (777561989861676077/87031250000000000000000000000000 : ℝ)*base79 + (13102157300657/6962500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4353329/1250000000000000000000 : ℝ)*base89 + (4353329/1250000000000000000000 : ℝ)*base91 + (4353329/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (323779930453442392207204137/43515625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1164672431/100000000000000 : ℝ)*(base19) + (77982283/6250000000000 : ℝ)*(base23) + (9444823/3125000000000 : ℝ)*(lower1) + (57035151/100000000000000 : ℝ)*(upper3) + (4921129/6250000000000 : ℝ)*(lower4) + (20926121/12500000000000 : ℝ)*(upper5) + (335839562390521/12500000000000 : ℝ)*(major0) + (335839562390521/12500000000000 : ℝ)*(major1) + (335839562390521/12500000000000 : ℝ)*(major2) + (5659867391/100000000000000 : ℝ)*(sp1) + (970571220512239/25000000000000 : ℝ)*(sp4) + (1941139028754567/50000000000000 : ℝ)*(sp5) + (970570908583107/25000000000000 : ℝ)*(sp6) + (1491147868181233/100000000000000 : ℝ)*(sp7) + (1491147868181233/100000000000000 : ℝ)*(f.failure) + (970571220512239/25000000000000 : ℝ)*(f.sum) + (5577130984363/6962500000000000000000000000 : ℝ)*base66 + (423421563596812791/43515625000000000000000000000000 : ℝ)*base67 + (167445869627906541/43515625000000000000000000000000 : ℝ)*base69 + (408589128178219041/43515625000000000000000000000000 : ℝ)*base71 + (10131356279637/6962500000000000000000000000 : ℝ)*base73 + (126309735007898583/21757812500000000000000000000000 : ℝ)*base75 + (31032744604469041/43515625000000000000000000000000 : ℝ)*base77 + (490548919200562791/43515625000000000000000000000000 : ℝ)*base79 + (5032862528313/6962500000000000000000000000 : ℝ)*base82 + (32004523/5000000000000000000000 : ℝ)*base90 + (32004523/5000000000000000000000 : ℝ)*base92 + (32004523/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1655_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90088869/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8131/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2673/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1337/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8129/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1655_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1655_box_0 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-670526849/5000000000 : ℝ)*x 0 + (1081367469/2000000000 : ℝ)*x 1 + (5406838147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670526849/5000000000 : ℝ)^4939 ≤ (1585815406251/20000000000000 : ℝ)^3915 := by
    have hnat : (670526849 : ℕ)^4939*20000000000000^3915 ≤ 1585815406251^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670526849 5000000000 1585815406251 20000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081367469/2000000000 : ℝ)^4939 ≤ (23017728583761/50000000000000 : ℝ)^3915 := by
    have hnat : (1081367469 : ℕ)^4939*50000000000000^3915 ≤ 23017728583761^3915*2000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081367469 2000000000 23017728583761 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406838147/10000000000 : ℝ)^4939 ≤ (46035465782037/100000000000000 : ℝ)^3915 := by
    have hnat : (5406838147 : ℕ)^4939*100000000000000^3915 ≤ 46035465782037^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406838147 10000000000 46035465782037 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-670526849/5000000000 : ℝ), (1081367469/2000000000 : ℝ), (5406838147/10000000000 : ℝ)] ![(1585815406251/20000000000000 : ℝ), (23017728583761/50000000000000 : ℝ), (46035465782037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-670526849/5000000000 : ℝ)|^4939 ≤ (1585815406251/20000000000000 : ℝ)^3915
        have hw : |(-670526849/5000000000 : ℝ)|=(670526849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081367469/2000000000 : ℝ)|^4939 ≤ (23017728583761/50000000000000 : ℝ)^3915
        have hw : |(1081367469/2000000000 : ℝ)|=(1081367469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406838147/10000000000 : ℝ)|^4939 ≤ (46035465782037/100000000000000 : ℝ)^3915
        have hw : |(5406838147/10000000000 : ℝ)|=(5406838147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_box_1 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1312750761/2500000000 : ℝ)*x 0 + (-1560105747/10000000000 : ℝ)*x 1 + (2703418793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312750761/2500000000 : ℝ)^4939 ≤ (11091987606727/25000000000000 : ℝ)^3915 := by
    have hnat : (1312750761 : ℕ)^4939*25000000000000^3915 ≤ 11091987606727^3915*2500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312750761 2500000000 11091987606727 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1560105747/10000000000 : ℝ)^4939 ≤ (149946715631/1562500000000 : ℝ)^3915 := by
    have hnat : (1560105747 : ℕ)^4939*1562500000000^3915 ≤ 149946715631^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560105747 10000000000 149946715631 1562500000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703418793/5000000000 : ℝ)^4939 ≤ (46035459756173/100000000000000 : ℝ)^3915 := by
    have hnat : (2703418793 : ℕ)^4939*100000000000000^3915 ≤ 46035459756173^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703418793 5000000000 46035459756173 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312750761/2500000000 : ℝ), (-1560105747/10000000000 : ℝ), (2703418793/5000000000 : ℝ)] ![(11091987606727/25000000000000 : ℝ), (149946715631/1562500000000 : ℝ), (46035459756173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312750761/2500000000 : ℝ)|^4939 ≤ (11091987606727/25000000000000 : ℝ)^3915
        have hw : |(1312750761/2500000000 : ℝ)|=(1312750761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1560105747/10000000000 : ℝ)|^4939 ≤ (149946715631/1562500000000 : ℝ)^3915
        have hw : |(-1560105747/10000000000 : ℝ)|=(1560105747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703418793/5000000000 : ℝ)|^4939 ≤ (46035459756173/100000000000000 : ℝ)^3915
        have hw : |(2703418793/5000000000 : ℝ)|=(2703418793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_box_2 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251003133/10000000000 : ℝ)*x 0 + (5406838233/10000000000 : ℝ)*x 1 + (-1560104729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251003133/10000000000 : ℝ)^4939 ≤ (22183975687799/50000000000000 : ℝ)^3915 := by
    have hnat : (5251003133 : ℕ)^4939*50000000000000^3915 ≤ 22183975687799^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251003133 10000000000 22183975687799 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406838233/10000000000 : ℝ)^4939 ≤ (46035466705787/100000000000000 : ℝ)^3915 := by
    have hnat : (5406838233 : ℕ)^4939*100000000000000^3915 ≤ 46035466705787^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406838233 10000000000 46035466705787 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1560104729/10000000000 : ℝ)^4939 ≤ (9596581900551/100000000000000 : ℝ)^3915 := by
    have hnat : (1560104729 : ℕ)^4939*100000000000000^3915 ≤ 9596581900551^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560104729 10000000000 9596581900551 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251003133/10000000000 : ℝ), (5406838233/10000000000 : ℝ), (-1560104729/10000000000 : ℝ)] ![(22183975687799/50000000000000 : ℝ), (46035466705787/100000000000000 : ℝ), (9596581900551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251003133/10000000000 : ℝ)|^4939 ≤ (22183975687799/50000000000000 : ℝ)^3915
        have hw : |(5251003133/10000000000 : ℝ)|=(5251003133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406838233/10000000000 : ℝ)|^4939 ≤ (46035466705787/100000000000000 : ℝ)^3915
        have hw : |(5406838233/10000000000 : ℝ)|=(5406838233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1560104729/10000000000 : ℝ)|^4939 ≤ (9596581900551/100000000000000 : ℝ)^3915
        have hw : |(-1560104729/10000000000 : ℝ)|=(1560104729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_box_3 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (222670161/500000000 : ℝ)*x 0 + (1012658373/2500000000 : ℝ)*x 1 + (2025316131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (222670161/500000000 : ℝ)^4939 ≤ (3604164189557/10000000000000 : ℝ)^3915 := by
    have hnat : (222670161 : ℕ)^4939*10000000000000^3915 ≤ 3604164189557^3915*500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222670161 500000000 3604164189557 10000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1012658373/2500000000 : ℝ)^4939 ≤ (31979185171309/100000000000000 : ℝ)^3915 := by
    have hnat : (1012658373 : ℕ)^4939*100000000000000^3915 ≤ 31979185171309^3915*2500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012658373 2500000000 31979185171309 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2025316131/5000000000 : ℝ)^4939 ≤ (1279166916829/4000000000000 : ℝ)^3915 := by
    have hnat : (2025316131 : ℕ)^4939*4000000000000^3915 ≤ 1279166916829^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025316131 5000000000 1279166916829 4000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(222670161/500000000 : ℝ), (1012658373/2500000000 : ℝ), (2025316131/5000000000 : ℝ)] ![(3604164189557/10000000000000 : ℝ), (31979185171309/100000000000000 : ℝ), (1279166916829/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(222670161/500000000 : ℝ)|^4939 ≤ (3604164189557/10000000000000 : ℝ)^3915
        have hw : |(222670161/500000000 : ℝ)|=(222670161/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1012658373/2500000000 : ℝ)|^4939 ≤ (31979185171309/100000000000000 : ℝ)^3915
        have hw : |(1012658373/2500000000 : ℝ)|=(1012658373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2025316131/5000000000 : ℝ)|^4939 ≤ (1279166916829/4000000000000 : ℝ)^3915
        have hw : |(2025316131/5000000000 : ℝ)|=(2025316131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_box_4 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-372808121/2000000000 : ℝ)*x 0 + (5215862541/10000000000 : ℝ)*x 1 + (5215862303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (372808121/2000000000 : ℝ)^4939 ≤ (3003150260191/25000000000000 : ℝ)^3915 := by
    have hnat : (372808121 : ℕ)^4939*25000000000000^3915 ≤ 3003150260191^3915*2000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372808121 2000000000 3003150260191 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215862541/10000000000 : ℝ)^4939 ≤ (43993700741513/100000000000000 : ℝ)^3915 := by
    have hnat : (5215862541 : ℕ)^4939*100000000000000^3915 ≤ 43993700741513^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215862541 10000000000 43993700741513 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215862303/10000000000 : ℝ)^4939 ≤ (21996849104509/50000000000000 : ℝ)^3915 := by
    have hnat : (5215862303 : ℕ)^4939*50000000000000^3915 ≤ 21996849104509^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215862303 10000000000 21996849104509 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-372808121/2000000000 : ℝ), (5215862541/10000000000 : ℝ), (5215862303/10000000000 : ℝ)] ![(3003150260191/25000000000000 : ℝ), (43993700741513/100000000000000 : ℝ), (21996849104509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-372808121/2000000000 : ℝ)|^4939 ≤ (3003150260191/25000000000000 : ℝ)^3915
        have hw : |(-372808121/2000000000 : ℝ)|=(372808121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215862541/10000000000 : ℝ)|^4939 ≤ (43993700741513/100000000000000 : ℝ)^3915
        have hw : |(5215862541/10000000000 : ℝ)|=(5215862541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215862303/10000000000 : ℝ)|^4939 ≤ (21996849104509/50000000000000 : ℝ)^3915
        have hw : |(5215862303/10000000000 : ℝ)|=(5215862303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_box_5 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381996739/10000000000 : ℝ)*x 0 + (-1642138747/10000000000 : ℝ)*x 1 + (1043172533/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381996739/10000000000 : ℝ)^4939 ≤ (45768797528349/100000000000000 : ℝ)^3915 := by
    have hnat : (5381996739 : ℕ)^4939*100000000000000^3915 ≤ 45768797528349^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381996739 10000000000 45768797528349 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1642138747/10000000000 : ℝ)^4939 ≤ (2559375099133/25000000000000 : ℝ)^3915 := by
    have hnat : (1642138747 : ℕ)^4939*25000000000000^3915 ≤ 2559375099133^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1642138747 10000000000 2559375099133 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043172533/2000000000 : ℝ)^4939 ≤ (10998425515241/25000000000000 : ℝ)^3915 := by
    have hnat : (1043172533 : ℕ)^4939*25000000000000^3915 ≤ 10998425515241^3915*2000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043172533 2000000000 10998425515241 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381996739/10000000000 : ℝ), (-1642138747/10000000000 : ℝ), (1043172533/2000000000 : ℝ)] ![(45768797528349/100000000000000 : ℝ), (2559375099133/25000000000000 : ℝ), (10998425515241/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381996739/10000000000 : ℝ)|^4939 ≤ (45768797528349/100000000000000 : ℝ)^3915
        have hw : |(5381996739/10000000000 : ℝ)|=(5381996739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1642138747/10000000000 : ℝ)|^4939 ≤ (2559375099133/25000000000000 : ℝ)^3915
        have hw : |(-1642138747/10000000000 : ℝ)|=(1642138747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043172533/2000000000 : ℝ)|^4939 ≤ (10998425515241/25000000000000 : ℝ)^3915
        have hw : |(1043172533/2000000000 : ℝ)|=(1043172533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_box_6 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381997141/10000000000 : ℝ)*x 0 + (651982777/1250000000 : ℝ)*x 1 + (-821069403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381997141/10000000000 : ℝ)^4939 ≤ (915376036823/2000000000000 : ℝ)^3915 := by
    have hnat : (5381997141 : ℕ)^4939*2000000000000^3915 ≤ 915376036823^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381997141 10000000000 915376036823 2000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651982777/1250000000 : ℝ)^4939 ≤ (21996848641637/50000000000000 : ℝ)^3915 := by
    have hnat : (651982777 : ℕ)^4939*50000000000000^3915 ≤ 21996848641637^3915*1250000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651982777 1250000000 21996848641637 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (821069403/5000000000 : ℝ)^4939 ≤ (10237500860559/100000000000000 : ℝ)^3915 := by
    have hnat : (821069403 : ℕ)^4939*100000000000000^3915 ≤ 10237500860559^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821069403 5000000000 10237500860559 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381997141/10000000000 : ℝ), (651982777/1250000000 : ℝ), (-821069403/5000000000 : ℝ)] ![(915376036823/2000000000000 : ℝ), (21996848641637/50000000000000 : ℝ), (10237500860559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381997141/10000000000 : ℝ)|^4939 ≤ (915376036823/2000000000000 : ℝ)^3915
        have hw : |(5381997141/10000000000 : ℝ)|=(5381997141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651982777/1250000000 : ℝ)|^4939 ≤ (21996848641637/50000000000000 : ℝ)^3915
        have hw : |(651982777/1250000000 : ℝ)|=(651982777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-821069403/5000000000 : ℝ)|^4939 ≤ (10237500860559/100000000000000 : ℝ)^3915
        have hw : |(-821069403/5000000000 : ℝ)|=(821069403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_box_7 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3893865639/10000000000 : ℝ)*x 0 + (4330078807/10000000000 : ℝ)*x 1 + (4330078729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3893865639/10000000000 : ℝ)^4939 ≤ (7606446045239/25000000000000 : ℝ)^3915 := by
    have hnat : (3893865639 : ℕ)^4939*25000000000000^3915 ≤ 7606446045239^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3893865639 10000000000 7606446045239 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4330078807/10000000000 : ℝ)^4939 ≤ (17393554148597/50000000000000 : ℝ)^3915 := by
    have hnat : (4330078807 : ℕ)^4939*50000000000000^3915 ≤ 17393554148597^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330078807 10000000000 17393554148597 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4330078729/10000000000 : ℝ)^4939 ≤ (34787107506653/100000000000000 : ℝ)^3915 := by
    have hnat : (4330078729 : ℕ)^4939*100000000000000^3915 ≤ 34787107506653^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330078729 10000000000 34787107506653 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3893865639/10000000000 : ℝ), (4330078807/10000000000 : ℝ), (4330078729/10000000000 : ℝ)] ![(7606446045239/25000000000000 : ℝ), (17393554148597/50000000000000 : ℝ), (34787107506653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3893865639/10000000000 : ℝ)|^4939 ≤ (7606446045239/25000000000000 : ℝ)^3915
        have hw : |(3893865639/10000000000 : ℝ)|=(3893865639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4330078807/10000000000 : ℝ)|^4939 ≤ (17393554148597/50000000000000 : ℝ)^3915
        have hw : |(4330078807/10000000000 : ℝ)|=(4330078807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4330078729/10000000000 : ℝ)|^4939 ≤ (34787107506653/100000000000000 : ℝ)^3915
        have hw : |(4330078729/10000000000 : ℝ)|=(4330078729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_box_8 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1752443323/10000000000 : ℝ)*x 0 + (634799793/1250000000 : ℝ)*x 1 + (5436231743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1752443323/10000000000 : ℝ)^4939 ≤ (1111252958901/10000000000000 : ℝ)^3915 := by
    have hnat : (1752443323 : ℕ)^4939*10000000000000^3915 ≤ 1111252958901^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1752443323 10000000000 1111252958901 10000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (634799793/1250000000 : ℝ)^4939 ≤ (42536055301057/100000000000000 : ℝ)^3915 := by
    have hnat : (634799793 : ℕ)^4939*100000000000000^3915 ≤ 42536055301057^3915*1250000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634799793 1250000000 42536055301057 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436231743/10000000000 : ℝ)^4939 ≤ (5793926885391/12500000000000 : ℝ)^3915 := by
    have hnat : (5436231743 : ℕ)^4939*12500000000000^3915 ≤ 5793926885391^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436231743 10000000000 5793926885391 12500000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1752443323/10000000000 : ℝ), (634799793/1250000000 : ℝ), (5436231743/10000000000 : ℝ)] ![(1111252958901/10000000000000 : ℝ), (42536055301057/100000000000000 : ℝ), (5793926885391/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1752443323/10000000000 : ℝ)|^4939 ≤ (1111252958901/10000000000000 : ℝ)^3915
        have hw : |(-1752443323/10000000000 : ℝ)|=(1752443323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(634799793/1250000000 : ℝ)|^4939 ≤ (42536055301057/100000000000000 : ℝ)^3915
        have hw : |(634799793/1250000000 : ℝ)|=(634799793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436231743/10000000000 : ℝ)|^4939 ≤ (5793926885391/12500000000000 : ℝ)^3915
        have hw : |(5436231743/10000000000 : ℝ)|=(5436231743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_box_9 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230843031/10000000000 : ℝ)*x 0 + (-386763547/2500000000 : ℝ)*x 1 + (5436231941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230843031/10000000000 : ℝ)^4939 ≤ (44153163993861/100000000000000 : ℝ)^3915 := by
    have hnat : (5230843031 : ℕ)^4939*100000000000000^3915 ≤ 44153163993861^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230843031 10000000000 44153163993861 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386763547/2500000000 : ℝ)^4939 ≤ (9495418774853/100000000000000 : ℝ)^3915 := by
    have hnat : (386763547 : ℕ)^4939*100000000000000^3915 ≤ 9495418774853^3915*2500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386763547 2500000000 9495418774853 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436231941/10000000000 : ℝ)^4939 ≤ (23175708606461/50000000000000 : ℝ)^3915 := by
    have hnat : (5436231941 : ℕ)^4939*50000000000000^3915 ≤ 23175708606461^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436231941 10000000000 23175708606461 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230843031/10000000000 : ℝ), (-386763547/2500000000 : ℝ), (5436231941/10000000000 : ℝ)] ![(44153163993861/100000000000000 : ℝ), (9495418774853/100000000000000 : ℝ), (23175708606461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230843031/10000000000 : ℝ)|^4939 ≤ (44153163993861/100000000000000 : ℝ)^3915
        have hw : |(5230843031/10000000000 : ℝ)|=(5230843031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-386763547/2500000000 : ℝ)|^4939 ≤ (9495418774853/100000000000000 : ℝ)^3915
        have hw : |(-386763547/2500000000 : ℝ)|=(386763547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436231941/10000000000 : ℝ)|^4939 ≤ (23175708606461/50000000000000 : ℝ)^3915
        have hw : |(5436231941/10000000000 : ℝ)|=(5436231941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_box_10 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307710761/2500000000 : ℝ)*x 0 + (1359058007/2500000000 : ℝ)*x 1 + (-1547054049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307710761/2500000000 : ℝ)^4939 ≤ (8830632826459/20000000000000 : ℝ)^3915 := by
    have hnat : (1307710761 : ℕ)^4939*20000000000000^3915 ≤ 8830632826459^3915*2500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307710761 2500000000 8830632826459 20000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359058007/2500000000 : ℝ)^4939 ≤ (2317570907437/5000000000000 : ℝ)^3915 := by
    have hnat : (1359058007 : ℕ)^4939*5000000000000^3915 ≤ 2317570907437^3915*2500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359058007 2500000000 2317570907437 5000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1547054049/10000000000 : ℝ)^4939 ≤ (7418295077/78125000000 : ℝ)^3915 := by
    have hnat : (1547054049 : ℕ)^4939*78125000000^3915 ≤ 7418295077^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1547054049 10000000000 7418295077 78125000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307710761/2500000000 : ℝ), (1359058007/2500000000 : ℝ), (-1547054049/10000000000 : ℝ)] ![(8830632826459/20000000000000 : ℝ), (2317570907437/5000000000000 : ℝ), (7418295077/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307710761/2500000000 : ℝ)|^4939 ≤ (8830632826459/20000000000000 : ℝ)^3915
        have hw : |(1307710761/2500000000 : ℝ)|=(1307710761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359058007/2500000000 : ℝ)|^4939 ≤ (2317570907437/5000000000000 : ℝ)^3915
        have hw : |(1359058007/2500000000 : ℝ)|=(1359058007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1547054049/10000000000 : ℝ)|^4939 ≤ (7418295077/78125000000 : ℝ)^3915
        have hw : |(-1547054049/10000000000 : ℝ)|=(1547054049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_box_11 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (907429939/2000000000 : ℝ)*x 0 + (801508679/2000000000 : ℝ)*x 1 + (4007543107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (907429939/2000000000 : ℝ)^4939 ≤ (36898774873177/100000000000000 : ℝ)^3915 := by
    have hnat : (907429939 : ℕ)^4939*100000000000000^3915 ≤ 36898774873177^3915*2000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907429939 2000000000 36898774873177 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (801508679/2000000000 : ℝ)^4939 ≤ (31550613985427/100000000000000 : ℝ)^3915 := by
    have hnat : (801508679 : ℕ)^4939*100000000000000^3915 ≤ 31550613985427^3915*2000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801508679 2000000000 31550613985427 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4007543107/10000000000 : ℝ)^4939 ≤ (3155061112501/10000000000000 : ℝ)^3915 := by
    have hnat : (4007543107 : ℕ)^4939*10000000000000^3915 ≤ 3155061112501^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4007543107 10000000000 3155061112501 10000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(907429939/2000000000 : ℝ), (801508679/2000000000 : ℝ), (4007543107/10000000000 : ℝ)] ![(36898774873177/100000000000000 : ℝ), (31550613985427/100000000000000 : ℝ), (3155061112501/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(907429939/2000000000 : ℝ)|^4939 ≤ (36898774873177/100000000000000 : ℝ)^3915
        have hw : |(907429939/2000000000 : ℝ)|=(907429939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(801508679/2000000000 : ℝ)|^4939 ≤ (31550613985427/100000000000000 : ℝ)^3915
        have hw : |(801508679/2000000000 : ℝ)|=(801508679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4007543107/10000000000 : ℝ)|^4939 ≤ (3155061112501/10000000000000 : ℝ)^3915
        have hw : |(4007543107/10000000000 : ℝ)|=(4007543107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_box_12 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1450826679/10000000000 : ℝ)*x 0 + (5539086047/10000000000 : ℝ)*x 1 + (2598027093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1450826679/10000000000 : ℝ)^4939 ≤ (2189118571541/25000000000000 : ℝ)^3915 := by
    have hnat : (1450826679 : ℕ)^4939*25000000000000^3915 ≤ 2189118571541^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1450826679 10000000000 2189118571541 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5539086047/10000000000 : ℝ)^4939 ≤ (23730247813021/50000000000000 : ℝ)^3915 := by
    have hnat : (5539086047 : ℕ)^4939*50000000000000^3915 ≤ 23730247813021^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5539086047 10000000000 23730247813021 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598027093/5000000000 : ℝ)^4939 ≤ (43783030071579/100000000000000 : ℝ)^3915 := by
    have hnat : (2598027093 : ℕ)^4939*100000000000000^3915 ≤ 43783030071579^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598027093 5000000000 43783030071579 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1450826679/10000000000 : ℝ), (5539086047/10000000000 : ℝ), (2598027093/5000000000 : ℝ)] ![(2189118571541/25000000000000 : ℝ), (23730247813021/50000000000000 : ℝ), (43783030071579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1450826679/10000000000 : ℝ)|^4939 ≤ (2189118571541/25000000000000 : ℝ)^3915
        have hw : |(-1450826679/10000000000 : ℝ)|=(1450826679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5539086047/10000000000 : ℝ)|^4939 ≤ (23730247813021/50000000000000 : ℝ)^3915
        have hw : |(5539086047/10000000000 : ℝ)|=(5539086047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2598027093/5000000000 : ℝ)|^4939 ≤ (43783030071579/100000000000000 : ℝ)^3915
        have hw : |(2598027093/5000000000 : ℝ)|=(2598027093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_box_13 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395593419/10000000000 : ℝ)*x 0 + (-165036569/1000000000 : ℝ)*x 1 + (5196054901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395593419/10000000000 : ℝ)^4939 ≤ (11478678942061/25000000000000 : ℝ)^3915 := by
    have hnat : (5395593419 : ℕ)^4939*25000000000000^3915 ≤ 11478678942061^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395593419 10000000000 11478678942061 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (165036569/1000000000 : ℝ)^4939 ≤ (10302246544157/100000000000000 : ℝ)^3915 := by
    have hnat : (165036569 : ℕ)^4939*100000000000000^3915 ≤ 10302246544157^3915*1000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165036569 1000000000 10302246544157 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5196054901/10000000000 : ℝ)^4939 ≤ (5472879709017/12500000000000 : ℝ)^3915 := by
    have hnat : (5196054901 : ℕ)^4939*12500000000000^3915 ≤ 5472879709017^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196054901 10000000000 5472879709017 12500000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395593419/10000000000 : ℝ), (-165036569/1000000000 : ℝ), (5196054901/10000000000 : ℝ)] ![(11478678942061/25000000000000 : ℝ), (10302246544157/100000000000000 : ℝ), (5472879709017/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395593419/10000000000 : ℝ)|^4939 ≤ (11478678942061/25000000000000 : ℝ)^3915
        have hw : |(5395593419/10000000000 : ℝ)|=(5395593419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-165036569/1000000000 : ℝ)|^4939 ≤ (10302246544157/100000000000000 : ℝ)^3915
        have hw : |(-165036569/1000000000 : ℝ)|=(165036569/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5196054901/10000000000 : ℝ)|^4939 ≤ (5472879709017/12500000000000 : ℝ)^3915
        have hw : |(5196054901/10000000000 : ℝ)|=(5196054901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_box_14 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697797011/5000000000 : ℝ)*x 0 + (1039210911/2000000000 : ℝ)*x 1 + (-206295667/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697797011/5000000000 : ℝ)^4939 ≤ (11478680560429/25000000000000 : ℝ)^3915 := by
    have hnat : (2697797011 : ℕ)^4939*25000000000000^3915 ≤ 11478680560429^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697797011 5000000000 11478680560429 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039210911/2000000000 : ℝ)^4939 ≤ (5472879249263/12500000000000 : ℝ)^3915 := by
    have hnat : (1039210911 : ℕ)^4939*12500000000000^3915 ≤ 5472879249263^3915*2000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039210911 2000000000 5472879249263 12500000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206295667/1250000000 : ℝ)^4939 ≤ (10302243756353/100000000000000 : ℝ)^3915 := by
    have hnat : (206295667 : ℕ)^4939*100000000000000^3915 ≤ 10302243756353^3915*1250000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206295667 1250000000 10302243756353 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697797011/5000000000 : ℝ), (1039210911/2000000000 : ℝ), (-206295667/1250000000 : ℝ)] ![(11478680560429/25000000000000 : ℝ), (5472879249263/12500000000000 : ℝ), (10302243756353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697797011/5000000000 : ℝ)|^4939 ≤ (11478680560429/25000000000000 : ℝ)^3915
        have hw : |(2697797011/5000000000 : ℝ)|=(2697797011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039210911/2000000000 : ℝ)|^4939 ≤ (5472879249263/12500000000000 : ℝ)^3915
        have hw : |(1039210911/2000000000 : ℝ)|=(1039210911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-206295667/1250000000 : ℝ)|^4939 ≤ (10302243756353/100000000000000 : ℝ)^3915
        have hw : |(-206295667/1250000000 : ℝ)|=(206295667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_box_15 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3834201891/10000000000 : ℝ)*x 0 + (4359010213/10000000000 : ℝ)*x 1 + (4359009621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3834201891/10000000000 : ℝ)^4939 ≤ (1193553202197/4000000000000 : ℝ)^3915 := by
    have hnat : (3834201891 : ℕ)^4939*4000000000000^3915 ≤ 1193553202197^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3834201891 10000000000 1193553202197 4000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4359010213/10000000000 : ℝ)^4939 ≤ (17540293985357/50000000000000 : ℝ)^3915 := by
    have hnat : (4359010213 : ℕ)^4939*50000000000000^3915 ≤ 17540293985357^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359010213 10000000000 17540293985357 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4359009621/10000000000 : ℝ)^4939 ≤ (35080581960251/100000000000000 : ℝ)^3915 := by
    have hnat : (4359009621 : ℕ)^4939*100000000000000^3915 ≤ 35080581960251^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359009621 10000000000 35080581960251 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3834201891/10000000000 : ℝ), (4359010213/10000000000 : ℝ), (4359009621/10000000000 : ℝ)] ![(1193553202197/4000000000000 : ℝ), (17540293985357/50000000000000 : ℝ), (35080581960251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3834201891/10000000000 : ℝ)|^4939 ≤ (1193553202197/4000000000000 : ℝ)^3915
        have hw : |(3834201891/10000000000 : ℝ)|=(3834201891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4359010213/10000000000 : ℝ)|^4939 ≤ (17540293985357/50000000000000 : ℝ)^3915
        have hw : |(4359010213/10000000000 : ℝ)|=(4359010213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4359009621/10000000000 : ℝ)|^4939 ≤ (35080581960251/100000000000000 : ℝ)^3915
        have hw : |(4359009621/10000000000 : ℝ)|=(4359009621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1655_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90088869/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8129/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1337/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(65089/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1467/2500 : ℝ) ∧ (81287/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (5517/6250 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8129/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1337/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8129/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1337/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8129/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1337/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8129/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1337/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8129/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1337/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8129/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1337/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1337/12500 : ℝ) ^ (4935/1024 : ℝ) ≤ (1048242544714607/50000000000000000000 : ℝ) := by
    have hpowers : (1337/12500 : ℝ)^4935 ≤ (1048242544714607/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1337 : ℕ)^4935*50000000000000000000^1024 ≤ 1048242544714607^1024*12500^4935 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1337 12500 1048242544714607 50000000000000000000 4935 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1337/12500 : ℝ)) (X := (1048242544714607/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8129/50000 : ℝ) ^ (4935/1024 : ℝ) ≤ (15771297183677761/100000000000000000000 : ℝ) := by
    have hpowers : (8129/50000 : ℝ)^4935 ≤ (15771297183677761/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8129 : ℕ)^4935*100000000000000000000^1024 ≤ 15771297183677761^1024*50000^4935 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8129 50000 15771297183677761 100000000000000000000 4935 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8129/50000 : ℝ)) (X := (15771297183677761/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001048242544714607/25000000000000000000 : ℝ) ≤ (10000087001623669/10000000000000000 : ℝ) ^ (4935/1024 : ℝ) := by
    have hpowers : (25001048242544714607/25000000000000000000 : ℝ)^1024 ≤ (10000087001623669/10000000000000000 : ℝ)^4935 := by
      have hnat : (25001048242544714607 : ℕ)^1024*10000000000000000^4935 ≤ 10000087001623669^4935*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001048242544714607 25000000000000000000 10000087001623669 10000000000000000 1024 4935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000087001623669/10000000000000000 : ℝ)) (X := (25001048242544714607/25000000000000000000 : ℝ)) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4000714711290924279/4000000000000000000 : ℝ) ≤ (10000370725709463/10000000000000000 : ℝ) ^ (4935/1024 : ℝ) := by
    have hpowers : (4000714711290924279/4000000000000000000 : ℝ)^1024 ≤ (10000370725709463/10000000000000000 : ℝ)^4935 := by
      have hnat : (4000714711290924279 : ℕ)^1024*10000000000000000^4935 ≤ 10000370725709463^4935*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4000714711290924279 4000000000000000000 10000370725709463 10000000000000000 1024 4935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000370725709463/10000000000000000 : ℝ)) (X := (4000714711290924279/4000000000000000000 : ℝ)) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50015771297183677761/50000000000000000000 : ℝ) ≤ (10000654449795257/10000000000000000 : ℝ) ^ (4935/1024 : ℝ) := by
    have hpowers : (50015771297183677761/50000000000000000000 : ℝ)^1024 ≤ (10000654449795257/10000000000000000 : ℝ)^4935 := by
      have hnat : (50015771297183677761 : ℕ)^1024*10000000000000000^4935 ≤ 10000654449795257^4935*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015771297183677761 50000000000000000000 10000654449795257 10000000000000000 1024 4935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000654449795257/10000000000000000 : ℝ)) (X := (50015771297183677761/50000000000000000000 : ℝ)) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1048242544714607/50000000000000000000 : ℝ) ≤ ((5561441447738754173/5562000000000000000 : ℝ)+2*(141862042897/278100000000000 : ℝ)*(1337/12500 : ℝ))^(4935/1024 : ℝ) := by
    rw [show (5561441447738754173/5562000000000000000 : ℝ)+2*(141862042897/278100000000000 : ℝ)*(1337/12500 : ℝ)=(10000087001623669/10000000000000000 : ℝ) by norm_num, show 1+2*(1048242544714607/50000000000000000000 : ℝ)=(25001048242544714607/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15771297183677761/100000000000000000000 : ℝ)+(1048242544714607/50000000000000000000 : ℝ) ≤ ((5561441447738754173/5562000000000000000 : ℝ)+(141862042897/278100000000000 : ℝ)*((8129/50000 : ℝ)+(1337/12500 : ℝ)))^(4935/1024 : ℝ) := by
    rw [show (5561441447738754173/5562000000000000000 : ℝ)+(141862042897/278100000000000 : ℝ)*((8129/50000 : ℝ)+(1337/12500 : ℝ))=(10000370725709463/10000000000000000 : ℝ) by norm_num, show 1+(15771297183677761/100000000000000000000 : ℝ)+(1048242544714607/50000000000000000000 : ℝ)=(4000714711290924279/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15771297183677761/100000000000000000000 : ℝ) ≤ ((5561441447738754173/5562000000000000000 : ℝ)+2*(141862042897/278100000000000 : ℝ)*(8129/50000 : ℝ))^(4935/1024 : ℝ) := by
    rw [show (5561441447738754173/5562000000000000000 : ℝ)+2*(141862042897/278100000000000 : ℝ)*(8129/50000 : ℝ)=(10000654449795257/10000000000000000 : ℝ) by norm_num, show 1+2*(15771297183677761/100000000000000000000 : ℝ)=(50015771297183677761/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5561441447738754173/5562000000000000000 : ℝ)*(X 1 0+X 2 0)+(141862042897/278100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4935/1024 : ℝ)) (lo := (1337/12500 : ℝ)) (hi := (8129/50000 : ℝ)) (c := (5561441447738754173/5562000000000000000 : ℝ)) (alpha := (141862042897/278100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5561441447738754173/5562000000000000000 : ℝ)*(X 0 1+X 2 1)+(141862042897/278100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4935/1024 : ℝ)) (lo := (1337/12500 : ℝ)) (hi := (8129/50000 : ℝ)) (c := (5561441447738754173/5562000000000000000 : ℝ)) (alpha := (141862042897/278100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5561441447738754173/5562000000000000000 : ℝ)*(X 0 2+X 1 2)+(141862042897/278100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4935/1024 : ℝ)) (lo := (1337/12500 : ℝ)) (hi := (8129/50000 : ℝ)) (c := (5561441447738754173/5562000000000000000 : ℝ)) (alpha := (141862042897/278100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-670526849/5000000000 : ℝ)*X 0 0+(1081367469/2000000000 : ℝ)*X 0 1+(5406838147/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1312750761/2500000000 : ℝ)*X 1 0+(-1560105747/10000000000 : ℝ)*X 1 1+(2703418793/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5251003133/10000000000 : ℝ)*X 2 0+(5406838233/10000000000 : ℝ)*X 2 1+(-1560104729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((222670161/500000000 : ℝ)*X 0 0+(1012658373/2500000000 : ℝ)*X 0 1+(2025316131/5000000000 : ℝ)*X 0 2+(222670161/500000000 : ℝ)*X 1 0+(1012658373/2500000000 : ℝ)*X 1 1+(2025316131/5000000000 : ℝ)*X 1 2+(222670161/500000000 : ℝ)*X 2 0+(1012658373/2500000000 : ℝ)*X 2 1+(2025316131/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-372808121/2000000000 : ℝ)*X 0 0+(5215862541/10000000000 : ℝ)*X 0 1+(5215862303/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5381996739/10000000000 : ℝ)*X 1 0+(-1642138747/10000000000 : ℝ)*X 1 1+(1043172533/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5381997141/10000000000 : ℝ)*X 2 0+(651982777/1250000000 : ℝ)*X 2 1+(-821069403/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3893865639/10000000000 : ℝ)*X 0 0+(4330078807/10000000000 : ℝ)*X 0 1+(4330078729/10000000000 : ℝ)*X 0 2+(3893865639/10000000000 : ℝ)*X 1 0+(4330078807/10000000000 : ℝ)*X 1 1+(4330078729/10000000000 : ℝ)*X 1 2+(3893865639/10000000000 : ℝ)*X 2 0+(4330078807/10000000000 : ℝ)*X 2 1+(4330078729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1752443323/10000000000 : ℝ)*X 0 0+(634799793/1250000000 : ℝ)*X 0 1+(5436231743/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5230843031/10000000000 : ℝ)*X 1 0+(-386763547/2500000000 : ℝ)*X 1 1+(5436231941/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1307710761/2500000000 : ℝ)*X 2 0+(1359058007/2500000000 : ℝ)*X 2 1+(-1547054049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((907429939/2000000000 : ℝ)*X 0 0+(801508679/2000000000 : ℝ)*X 0 1+(4007543107/10000000000 : ℝ)*X 0 2+(907429939/2000000000 : ℝ)*X 1 0+(801508679/2000000000 : ℝ)*X 1 1+(4007543107/10000000000 : ℝ)*X 1 2+(907429939/2000000000 : ℝ)*X 2 0+(801508679/2000000000 : ℝ)*X 2 1+(4007543107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1450826679/10000000000 : ℝ)*X 0 0+(5539086047/10000000000 : ℝ)*X 0 1+(2598027093/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5395593419/10000000000 : ℝ)*X 1 0+(-165036569/1000000000 : ℝ)*X 1 1+(5196054901/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2697797011/5000000000 : ℝ)*X 2 0+(1039210911/2000000000 : ℝ)*X 2 1+(-206295667/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3834201891/10000000000 : ℝ)*X 0 0+(4359010213/10000000000 : ℝ)*X 0 1+(4359009621/10000000000 : ℝ)*X 0 2+(3834201891/10000000000 : ℝ)*X 1 0+(4359010213/10000000000 : ℝ)*X 1 1+(4359009621/10000000000 : ℝ)*X 1 2+(3834201891/10000000000 : ℝ)*X 2 0+(4359010213/10000000000 : ℝ)*X 2 1+(4359009621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65089/100000 : ℝ) ≤ (-6703874620898412337739691867109/10300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2001669/25000000000000 : ℝ)*(upper1) + (7694583/25000000000000 : ℝ)*(upper4) + (30254179/100000000000000 : ℝ)*(upper5) + (1768441255039503/100000000000000 : ℝ)*(major0) + (1768441255039503/100000000000000 : ℝ)*(major1) + (1768441255039503/100000000000000 : ℝ)*(major2) + (1886938073/50000000000000 : ℝ)*(sp2) + (432076527/50000000000000 : ℝ)*(sp3) + (322134580818897/12500000000000 : ℝ)*(sp4) + (161066406153621/6250000000000 : ℝ)*(sp5) + (257707592345383/10000000000000 : ℝ)*(sp6) + (981497335718621/100000000000000 : ℝ)*(sp7) + (7626947/250000000000 : ℝ)*(sp8) + (17198872039/100000000000000 : ℝ)*(sp13) + (39259927994867/4000000000000 : ℝ)*(f.failure) + (103083187893199/4000000000000 : ℝ)*(f.sum) + (828040145639/386250000000000000000000000 : ℝ)*base66 + (129124457948587109/61800000000000000000000000000000 : ℝ)*base68 + (391394539605787109/61800000000000000000000000000000 : ℝ)*base70 + (6209840968012891/61800000000000000000000000000000 : ℝ)*base71 + (138964212857/772500000000000000000000000 : ℝ)*base73 + (159675698802412891/61800000000000000000000000000000 : ℝ)*base75 + (128099073337387109/61800000000000000000000000000000 : ℝ)*base78 + (212478560256187109/61800000000000000000000000000000 : ℝ)*base80 + (1073864269591/386250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (164577/200000000000000000000 : ℝ)*base90 + (164577/200000000000000000000 : ℝ)*base92 + (164577/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (1467/2500 : ℝ) ≤ (2719914406728340247116286441/4635000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1493419/5000000000000 : ℝ)*(lower0) + (2417477/6250000000000 : ℝ)*(lower3) + (59521611/25000000000000 : ℝ)*(upper4) + (1859548959093247/100000000000000 : ℝ)*(major0) + (1859548959093247/100000000000000 : ℝ)*(major1) + (1859548959093247/100000000000000 : ℝ)*(major2) + (1333736702309373/50000000000000 : ℝ)*(sp0) + (66685923879871/2500000000000 : ℝ)*(sp1) + (106698513396939/4000000000000 : ℝ)*(sp2) + (41282463763257/4000000000000 : ℝ)*(sp3) + (5364474003/50000000000000 : ℝ)*(sp6) + (413381879/20000000000000 : ℝ)*(sp7) + (36608676641/100000000000000 : ℝ)*(sp9) + (79626367/50000000000000 : ℝ)*(sp12) + (51603183049541/5000000000000 : ℝ)*(f.failure) + (66686839096787/2500000000000 : ℝ)*(f.sum) + (3765787693651/3476250000000000000000000000 : ℝ)*base65 + (1546100270353949731/556200000000000000000000000000000 : ℝ)*base67 + (6101717130754349731/556200000000000000000000000000000 : ℝ)*base69 + (650312914885349731/556200000000000000000000000000000 : ℝ)*base71 + (6467673161563/6952500000000000000000000000 : ℝ)*base74 + (2471159347552650269/556200000000000000000000000000000 : ℝ)*base76 + (2191572179992650269/556200000000000000000000000000000 : ℝ)*base78 + (1778467928734650269/556200000000000000000000000000000 : ℝ)*base80 + (40780387328989/13905000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2159129/250000000000000000000 : ℝ)*base89 + (2159129/250000000000000000000 : ℝ)*base91 + (2159129/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (81287/100000 : ℝ) ≤ (3767770740576481125448695733/4635000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8382611/50000000000000 : ℝ)*(lower3) + (45354693/100000000000000 : ℝ)*(upper4) + (36141041/100000000000000 : ℝ)*(lower5) + (1952742085289959/100000000000000 : ℝ)*(major0) + (1952742085289959/100000000000000 : ℝ)*(major1) + (1952742085289959/100000000000000 : ℝ)*(major2) + (2013859931/50000000000000 : ℝ)*(sp0) + (28555565029/100000000000000 : ℝ)*(sp1) + (24625329611/50000000000000 : ℝ)*(sp2) + (9161200619/50000000000000 : ℝ)*(sp3) + (1397298539200443/50000000000000 : ℝ)*(sp8) + (69864313763893/2500000000000 : ℝ)*(sp9) + (1397275927730763/50000000000000 : ℝ)*(sp10) + (1083768224685927/100000000000000 : ℝ)*(sp11) + (216757309417433/20000000000000 : ℝ)*(f.failure) + (698650276530187/25000000000000 : ℝ)*(f.sum) + (16381535104883/3476250000000000000000000000 : ℝ)*base66 + (2974900084803708907/556200000000000000000000000000000 : ℝ)*base67 + (2371990189252691093/556200000000000000000000000000000 : ℝ)*base70 + (5264212760169491093/556200000000000000000000000000000 : ℝ)*base72 + (55364020421833/13905000000000000000000000000 : ℝ)*base73 + (1918649646865091093/556200000000000000000000000000000 : ℝ)*base76 + (205495820271708907/556200000000000000000000000000000 : ℝ)*base77 + (952439927067708907/556200000000000000000000000000000 : ℝ)*base79 + (31370631588571/6952500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2146723/1000000000000000000000 : ℝ)*base90 + (2146723/1000000000000000000000 : ℝ)*base92 + (2146723/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-5517/6250 : ℝ) ≤ (-20456416337504161183010184661517/23175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8461289/50000000000000 : ℝ)*(lower0) + (47962689/100000000000000 : ℝ)*(lower1) + (186596147/100000000000000 : ℝ)*(lower2) + (499269862397843/25000000000000 : ℝ)*(major0) + (499269862397843/25000000000000 : ℝ)*(major1) + (499269862397843/25000000000000 : ℝ)*(major2) + (9278554573/100000000000000 : ℝ)*(sp0) + (17722244509/100000000000000 : ℝ)*(sp5) + (9771396333/100000000000000 : ℝ)*(sp6) + (17750561809/100000000000000 : ℝ)*(sp7) + (91099331610629/3125000000000 : ℝ)*(sp12) + (2915170167850193/100000000000000 : ℝ)*(sp13) + (22774829052331/781250000000 : ℝ)*(sp14) + (554188183623057/50000000000000 : ℝ)*(sp15) + (277098529451981/25000000000000 : ℝ)*(f.failure) + (1457593945047351/50000000000000 : ℝ)*(f.sum) + (34411666291289/13905000000000000000000000000 : ℝ)*base65 + (1727404568789568839/139050000000000000000000000000000 : ℝ)*base67 + (1389230971380168839/139050000000000000000000000000000 : ℝ)*base69 + (859183085321718839/139050000000000000000000000000000 : ℝ)*base71 + (8455143311719/3476250000000000000000000000 : ℝ)*base74 + (256428117742218839/139050000000000000000000000000000 : ℝ)*base75 + (1323818099811168839/139050000000000000000000000000000 : ℝ)*base77 + (688590181003218839/139050000000000000000000000000000 : ℝ)*base79 + (40190144457961/13905000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (8099489/1250000000000000000000 : ℝ)*base89 + (8099489/1250000000000000000000 : ℝ)*base91 + (8099489/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1655_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90088869/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8129/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1337/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65089/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1467/2500 : ℝ) else (81287/100000 : ℝ) ≤ X j i ∧ X j i ≤ (5517/6250 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1655_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1655_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90088869/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16329/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1329/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65089/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1467/2500 : ℝ) else (81287/100000 : ℝ) ≤ X j i ∧ X j i ≤ (5517/6250 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1655_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1655_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1655_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90088869/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16329/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1329/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65089/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1467/2500 : ℝ) else (81287/100000 : ℝ) ≤ X j i ∧ X j i ≤ (5517/6250 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1655_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

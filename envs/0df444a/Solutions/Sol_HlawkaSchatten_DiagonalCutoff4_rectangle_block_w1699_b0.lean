-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1699_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:44:20.006889+00:00
-- url     : https://prove2.me/submissions/c5822cf0-7bdf-416f-853d-ab2e0c3c4479

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
theorem support_rectangle_w1699_s0_0 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-34240339/250000000 : ℝ)*x 0 + (2860203209/5000000000 : ℝ)*x 1 + (4948215263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34240339/250000000 : ℝ)^5215 ≤ (4213183554637/50000000000000 : ℝ)^4191 := by
    have hnat : (34240339 : ℕ)^5215*50000000000000^4191 ≤ 4213183554637^4191*250000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34240339 250000000 4213183554637 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2860203209/5000000000 : ℝ)^5215 ≤ (24953315043521/50000000000000 : ℝ)^4191 := by
    have hnat : (2860203209 : ℕ)^5215*50000000000000^4191 ≤ 24953315043521^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2860203209 5000000000 24953315043521 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4948215263/10000000000 : ℝ)^5215 ≤ (20833501390439/50000000000000 : ℝ)^4191 := by
    have hnat : (4948215263 : ℕ)^5215*50000000000000^4191 ≤ 20833501390439^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4948215263 10000000000 20833501390439 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-34240339/250000000 : ℝ), (2860203209/5000000000 : ℝ), (4948215263/10000000000 : ℝ)] ![(4213183554637/50000000000000 : ℝ), (24953315043521/50000000000000 : ℝ), (20833501390439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-34240339/250000000 : ℝ)|^5215 ≤ (4213183554637/50000000000000 : ℝ)^4191
        have hw : |(-34240339/250000000 : ℝ)|=(34240339/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2860203209/5000000000 : ℝ)|^5215 ≤ (24953315043521/50000000000000 : ℝ)^4191
        have hw : |(2860203209/5000000000 : ℝ)|=(2860203209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4948215263/10000000000 : ℝ)|^5215 ≤ (20833501390439/50000000000000 : ℝ)^4191
        have hw : |(4948215263/10000000000 : ℝ)|=(4948215263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s0_1 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5412067593/10000000000 : ℝ)*x 0 + (-447323629/2500000000 : ℝ)*x 1 + (309263419/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412067593/10000000000 : ℝ)^5215 ≤ (23290833178967/50000000000000 : ℝ)^4191 := by
    have hnat : (5412067593 : ℕ)^5215*50000000000000^4191 ≤ 23290833178967^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412067593 10000000000 23290833178967 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447323629/2500000000 : ℝ)^5215 ≤ (5875668349733/50000000000000 : ℝ)^4191 := by
    have hnat : (447323629 : ℕ)^5215*50000000000000^4191 ≤ 5875668349733^4191*2500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447323629 2500000000 5875668349733 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (309263419/625000000 : ℝ)^5215 ≤ (833339938473/2000000000000 : ℝ)^4191 := by
    have hnat : (309263419 : ℕ)^5215*2000000000000^4191 ≤ 833339938473^4191*625000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309263419 625000000 833339938473 2000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412067593/10000000000 : ℝ), (-447323629/2500000000 : ℝ), (309263419/625000000 : ℝ)] ![(23290833178967/50000000000000 : ℝ), (5875668349733/50000000000000 : ℝ), (833339938473/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412067593/10000000000 : ℝ)|^5215 ≤ (23290833178967/50000000000000 : ℝ)^4191
        have hw : |(5412067593/10000000000 : ℝ)|=(5412067593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-447323629/2500000000 : ℝ)|^5215 ≤ (5875668349733/50000000000000 : ℝ)^4191
        have hw : |(-447323629/2500000000 : ℝ)|=(447323629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(309263419/625000000 : ℝ)|^5215 ≤ (833339938473/2000000000000 : ℝ)^4191
        have hw : |(309263419/625000000 : ℝ)|=(309263419/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s0_2 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5412067/10000000 : ℝ)*x 0 + (2474107629/5000000000 : ℝ)*x 1 + (-223661823/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412067/10000000 : ℝ)^5215 ≤ (46581660006919/100000000000000 : ℝ)^4191 := by
    have hnat : (5412067 : ℕ)^5215*100000000000000^4191 ≤ 46581660006919^4191*10000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412067 10000000 46581660006919 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2474107629/5000000000 : ℝ)^5215 ≤ (5208375341061/12500000000000 : ℝ)^4191 := by
    have hnat : (2474107629 : ℕ)^5215*12500000000000^4191 ≤ 5208375341061^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2474107629 5000000000 5208375341061 12500000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223661823/1250000000 : ℝ)^5215 ≤ (11751337255179/100000000000000 : ℝ)^4191 := by
    have hnat : (223661823 : ℕ)^5215*100000000000000^4191 ≤ 11751337255179^4191*1250000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223661823 1250000000 11751337255179 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412067/10000000 : ℝ), (2474107629/5000000000 : ℝ), (-223661823/1250000000 : ℝ)] ![(46581660006919/100000000000000 : ℝ), (5208375341061/12500000000000 : ℝ), (11751337255179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412067/10000000 : ℝ)|^5215 ≤ (46581660006919/100000000000000 : ℝ)^4191
        have hw : |(5412067/10000000 : ℝ)|=(5412067/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2474107629/5000000000 : ℝ)|^5215 ≤ (5208375341061/12500000000000 : ℝ)^4191
        have hw : |(2474107629/5000000000 : ℝ)|=(2474107629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-223661823/1250000000 : ℝ)|^5215 ≤ (11751337255179/100000000000000 : ℝ)^4191
        have hw : |(-223661823/1250000000 : ℝ)|=(223661823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s0_3 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2024441071/5000000000 : ℝ)*x 0 + (3052479261/10000000000 : ℝ)*x 1 + (2617573237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2024441071/5000000000 : ℝ)^5215 ≤ (324634082657/1000000000000 : ℝ)^4191 := by
    have hnat : (2024441071 : ℕ)^5215*1000000000000^4191 ≤ 324634082657^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024441071 5000000000 324634082657 1000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3052479261/10000000000 : ℝ)^5215 ≤ (22842115682641/100000000000000 : ℝ)^4191 := by
    have hnat : (3052479261 : ℕ)^5215*100000000000000^4191 ≤ 22842115682641^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3052479261 10000000000 22842115682641 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2617573237/5000000000 : ℝ)^5215 ≤ (44694476032819/100000000000000 : ℝ)^4191 := by
    have hnat : (2617573237 : ℕ)^5215*100000000000000^4191 ≤ 44694476032819^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617573237 5000000000 44694476032819 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2024441071/5000000000 : ℝ), (3052479261/10000000000 : ℝ), (2617573237/5000000000 : ℝ)] ![(324634082657/1000000000000 : ℝ), (22842115682641/100000000000000 : ℝ), (44694476032819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2024441071/5000000000 : ℝ)|^5215 ≤ (324634082657/1000000000000 : ℝ)^4191
        have hw : |(2024441071/5000000000 : ℝ)|=(2024441071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3052479261/10000000000 : ℝ)|^5215 ≤ (22842115682641/100000000000000 : ℝ)^4191
        have hw : |(3052479261/10000000000 : ℝ)|=(3052479261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2617573237/5000000000 : ℝ)|^5215 ≤ (44694476032819/100000000000000 : ℝ)^4191
        have hw : |(2617573237/5000000000 : ℝ)|=(2617573237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s0_4 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1371462579/10000000000 : ℝ)*x 0 + (1241854253/2500000000 : ℝ)*x 1 + (5700551761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1371462579/10000000000 : ℝ)^5215 ≤ (844052478471/10000000000000 : ℝ)^4191 := by
    have hnat : (1371462579 : ℕ)^5215*10000000000000^4191 ≤ 844052478471^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371462579 10000000000 844052478471 10000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1241854253/2500000000 : ℝ)^5215 ≤ (20934147446013/50000000000000 : ℝ)^4191 := by
    have hnat : (1241854253 : ℕ)^5215*50000000000000^4191 ≤ 20934147446013^4191*2500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1241854253 2500000000 20934147446013 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5700551761/10000000000 : ℝ)^5215 ≤ (24845590154661/50000000000000 : ℝ)^4191 := by
    have hnat : (5700551761 : ℕ)^5215*50000000000000^4191 ≤ 24845590154661^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5700551761 10000000000 24845590154661 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1371462579/10000000000 : ℝ), (1241854253/2500000000 : ℝ), (5700551761/10000000000 : ℝ)] ![(844052478471/10000000000000 : ℝ), (20934147446013/50000000000000 : ℝ), (24845590154661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1371462579/10000000000 : ℝ)|^5215 ≤ (844052478471/10000000000000 : ℝ)^4191
        have hw : |(-1371462579/10000000000 : ℝ)|=(1371462579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1241854253/2500000000 : ℝ)|^5215 ≤ (20934147446013/50000000000000 : ℝ)^4191
        have hw : |(1241854253/2500000000 : ℝ)|=(1241854253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5700551761/10000000000 : ℝ)|^5215 ≤ (24845590154661/50000000000000 : ℝ)^4191
        have hw : |(5700551761/10000000000 : ℝ)|=(5700551761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s0_5 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5202542013/10000000000 : ℝ)*x 0 + (-1036957853/10000000000 : ℝ)*x 1 + (2850275859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5202542013/10000000000 : ℝ)^5215 ≤ (22174185621367/50000000000000 : ℝ)^4191 := by
    have hnat : (5202542013 : ℕ)^5215*50000000000000^4191 ≤ 22174185621367^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202542013 10000000000 22174185621367 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036957853/10000000000 : ℝ)^5215 ≤ (5960448909343/100000000000000 : ℝ)^4191 := by
    have hnat : (1036957853 : ℕ)^5215*100000000000000^4191 ≤ 5960448909343^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036957853 10000000000 5960448909343 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2850275859/5000000000 : ℝ)^5215 ≤ (49691179842913/100000000000000 : ℝ)^4191 := by
    have hnat : (2850275859 : ℕ)^5215*100000000000000^4191 ≤ 49691179842913^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850275859 5000000000 49691179842913 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5202542013/10000000000 : ℝ), (-1036957853/10000000000 : ℝ), (2850275859/5000000000 : ℝ)] ![(22174185621367/50000000000000 : ℝ), (5960448909343/100000000000000 : ℝ), (49691179842913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5202542013/10000000000 : ℝ)|^5215 ≤ (22174185621367/50000000000000 : ℝ)^4191
        have hw : |(5202542013/10000000000 : ℝ)|=(5202542013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1036957853/10000000000 : ℝ)|^5215 ≤ (5960448909343/100000000000000 : ℝ)^4191
        have hw : |(-1036957853/10000000000 : ℝ)|=(1036957853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2850275859/5000000000 : ℝ)|^5215 ≤ (49691179842913/100000000000000 : ℝ)^4191
        have hw : |(2850275859/5000000000 : ℝ)|=(2850275859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s0_6 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5202542269/10000000000 : ℝ)*x 0 + (5700551859/10000000000 : ℝ)*x 1 + (-1036957259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5202542269/10000000000 : ℝ)^5215 ≤ (8869674791633/20000000000000 : ℝ)^4191 := by
    have hnat : (5202542269 : ℕ)^5215*20000000000000^4191 ≤ 8869674791633^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202542269 10000000000 8869674791633 20000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5700551859/10000000000 : ℝ)^5215 ≤ (24845590686151/50000000000000 : ℝ)^4191 := by
    have hnat : (5700551859 : ℕ)^5215*50000000000000^4191 ≤ 24845590686151^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5700551859 10000000000 24845590686151 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036957259/10000000000 : ℝ)^5215 ≤ (5960444660791/100000000000000 : ℝ)^4191 := by
    have hnat : (1036957259 : ℕ)^5215*100000000000000^4191 ≤ 5960444660791^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036957259 10000000000 5960444660791 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5202542269/10000000000 : ℝ), (5700551859/10000000000 : ℝ), (-1036957259/10000000000 : ℝ)] ![(8869674791633/20000000000000 : ℝ), (24845590686151/50000000000000 : ℝ), (5960444660791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5202542269/10000000000 : ℝ)|^5215 ≤ (8869674791633/20000000000000 : ℝ)^4191
        have hw : |(5202542269/10000000000 : ℝ)|=(5202542269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5700551859/10000000000 : ℝ)|^5215 ≤ (24845590686151/50000000000000 : ℝ)^4191
        have hw : |(5700551859/10000000000 : ℝ)|=(5700551859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1036957259/10000000000 : ℝ)|^5215 ≤ (5960444660791/100000000000000 : ℝ)^4191
        have hw : |(-1036957259/10000000000 : ℝ)|=(1036957259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s0_7 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (25338169/62500000 : ℝ)*x 0 + (5180870303/10000000000 : ℝ)*x 1 + (1554299409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25338169/62500000 : ℝ)^5215 ≤ (32515544767259/100000000000000 : ℝ)^4191 := by
    have hnat : (25338169 : ℕ)^5215*100000000000000^4191 ≤ 32515544767259^4191*62500000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25338169 62500000 32515544767259 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180870303/10000000000 : ℝ)^5215 ≤ (44118613259217/100000000000000 : ℝ)^4191 := by
    have hnat : (5180870303 : ℕ)^5215*100000000000000^4191 ≤ 44118613259217^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180870303 10000000000 44118613259217 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1554299409/5000000000 : ℝ)^5215 ≤ (5841460488709/25000000000000 : ℝ)^4191 := by
    have hnat : (1554299409 : ℕ)^5215*25000000000000^4191 ≤ 5841460488709^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1554299409 5000000000 5841460488709 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(25338169/62500000 : ℝ), (5180870303/10000000000 : ℝ), (1554299409/5000000000 : ℝ)] ![(32515544767259/100000000000000 : ℝ), (44118613259217/100000000000000 : ℝ), (5841460488709/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(25338169/62500000 : ℝ)|^5215 ≤ (32515544767259/100000000000000 : ℝ)^4191
        have hw : |(25338169/62500000 : ℝ)|=(25338169/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180870303/10000000000 : ℝ)|^5215 ≤ (44118613259217/100000000000000 : ℝ)^4191
        have hw : |(5180870303/10000000000 : ℝ)|=(5180870303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1554299409/5000000000 : ℝ)|^5215 ≤ (5841460488709/25000000000000 : ℝ)^4191
        have hw : |(1554299409/5000000000 : ℝ)|=(1554299409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1699_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95664749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (143/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (22303/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (5207/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5207 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5207*1^1024 ≤ 0^1024*1^5207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5207/1024 : ℝ) ≤ (947306681439757151/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5207 ≤ (947306681439757151/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5207*100000000000000000000^1024 ≤ 947306681439757151^1024*5^5207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 947306681439757151 100000000000000000000 5207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (947306681439757151/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5207/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5207 := by
      have hnat : (1 : ℕ)^1024*1^5207 ≤ 1^5207*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100947306681439757151/100000000000000000000 : ℝ) ≤ (10018559090814041/10000000000000000 : ℝ) ^ (5207/1024 : ℝ) := by
    have hpowers : (100947306681439757151/100000000000000000000 : ℝ)^1024 ≤ (10018559090814041/10000000000000000 : ℝ)^5207 := by
      have hnat : (100947306681439757151 : ℕ)^1024*10000000000000000^5207 ≤ 10018559090814041^5207*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100947306681439757151 100000000000000000000 10018559090814041 10000000000000000 1024 5207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10018559090814041/10000000000000000 : ℝ)) (X := (100947306681439757151/100000000000000000000 : ℝ)) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50947306681439757151/50000000000000000000 : ℝ) ≤ (5018559090814041/5000000000000000 : ℝ) ^ (5207/1024 : ℝ) := by
    have hpowers : (50947306681439757151/50000000000000000000 : ℝ)^1024 ≤ (5018559090814041/5000000000000000 : ℝ)^5207 := by
      have hnat : (50947306681439757151 : ℕ)^1024*5000000000000000^5207 ≤ 5018559090814041^5207*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50947306681439757151 50000000000000000000 5018559090814041 5000000000000000 1024 5207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5018559090814041/5000000000000000 : ℝ)) (X := (50947306681439757151/50000000000000000000 : ℝ)) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(18559090814041/4000000000000000 : ℝ)*(0 : ℝ))^(5207/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(18559090814041/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(947306681439757151/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(18559090814041/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5207/1024 : ℝ) := by
    rw [show (1 : ℝ)+(18559090814041/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10018559090814041/10000000000000000 : ℝ) by norm_num, show 1+(947306681439757151/100000000000000000000 : ℝ)+(0 : ℝ)=(100947306681439757151/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(947306681439757151/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(18559090814041/4000000000000000 : ℝ)*(2/5 : ℝ))^(5207/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(18559090814041/4000000000000000 : ℝ)*(2/5 : ℝ)=(5018559090814041/5000000000000000 : ℝ) by norm_num, show 1+2*(947306681439757151/100000000000000000000 : ℝ)=(50947306681439757151/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(18559090814041/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5207/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (18559090814041/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(18559090814041/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5207/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (18559090814041/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(18559090814041/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5207/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (18559090814041/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-34240339/250000000 : ℝ)*X 0 0+(2860203209/5000000000 : ℝ)*X 0 1+(4948215263/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5412067593/10000000000 : ℝ)*X 1 0+(-447323629/2500000000 : ℝ)*X 1 1+(309263419/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5412067/10000000 : ℝ)*X 2 0+(2474107629/5000000000 : ℝ)*X 2 1+(-223661823/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2024441071/5000000000 : ℝ)*X 0 0+(3052479261/10000000000 : ℝ)*X 0 1+(2617573237/5000000000 : ℝ)*X 0 2+(2024441071/5000000000 : ℝ)*X 1 0+(3052479261/10000000000 : ℝ)*X 1 1+(2617573237/5000000000 : ℝ)*X 1 2+(2024441071/5000000000 : ℝ)*X 2 0+(3052479261/10000000000 : ℝ)*X 2 1+(2617573237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1371462579/10000000000 : ℝ)*X 0 0+(1241854253/2500000000 : ℝ)*X 0 1+(5700551761/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5202542013/10000000000 : ℝ)*X 1 0+(-1036957853/10000000000 : ℝ)*X 1 1+(2850275859/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5202542269/10000000000 : ℝ)*X 2 0+(5700551859/10000000000 : ℝ)*X 2 1+(-1036957259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((25338169/62500000 : ℝ)*X 0 0+(5180870303/10000000000 : ℝ)*X 0 1+(1554299409/5000000000 : ℝ)*X 0 2+(25338169/62500000 : ℝ)*X 1 0+(5180870303/10000000000 : ℝ)*X 1 1+(1554299409/5000000000 : ℝ)*X 1 2+(25338169/62500000 : ℝ)*X 2 0+(5180870303/10000000000 : ℝ)*X 2 1+(1554299409/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (427519783880207187935319/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11342871/10000000000000 : ℝ)*(base1) + (92109421/20000000000000 : ℝ)*(base19) + (79663029/25000000000000 : ℝ)*(base23) + (34846327/50000000000000 : ℝ)*(upper3) + (12803233/100000000000000 : ℝ)*(upper5) + (876586604674551/100000000000000 : ℝ)*(major0) + (876586604674551/100000000000000 : ℝ)*(major1) + (876586604674551/100000000000000 : ℝ)*(major2) + (1295017300726343/100000000000000 : ℝ)*(sp0) + (647508592311397/50000000000000 : ℝ)*(sp1) + (1295017326517783/100000000000000 : ℝ)*(sp2) + (11453878892583/2500000000000 : ℝ)*(sp3) + (91574453/20000000000000 : ℝ)*(sp4) + (223793871/100000000000000 : ℝ)*(sp7) + (458155492925901/100000000000000 : ℝ)*(f.failure) + (647508822584949/50000000000000 : ℝ)*(f.sum) + (170341686829409/200000000000000000000000000000 : ℝ)*base66 + (1738625928629409/400000000000000000000000000000 : ℝ)*base68 + (636206453370591/400000000000000000000000000000 : ℝ)*base69 + (1576856782629409/400000000000000000000000000000 : ℝ)*base72 + (269697879629409/200000000000000000000000000000 : ℝ)*base74 + (958505987429409/400000000000000000000000000000 : ℝ)*base76 + (357235245829409/400000000000000000000000000000 : ℝ)*base78 + (3661062512629409/400000000000000000000000000000 : ℝ)*base80 + (678424288970591/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (44763849/5000000000000000000000 : ℝ)*base89 + (44763849/5000000000000000000000 : ℝ)*base91 + (44763849/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1105519119777600210318471/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (765477519/50000000000000 : ℝ)*(base19) + (1645082097/100000000000000 : ℝ)*(base23) + (7790481/50000000000000 : ℝ)*(base32) + (259222271/100000000000000 : ℝ)*(upper3) + (235092527/100000000000000 : ℝ)*(upper5) + (923284094574923/100000000000000 : ℝ)*(major0) + (923284094574923/100000000000000 : ℝ)*(major1) + (923284094574923/100000000000000 : ℝ)*(major2) + (5225566447/100000000000000 : ℝ)*(sp1) + (3196414143/50000000000000 : ℝ)*(sp2) + (682002834560947/50000000000000 : ℝ)*(sp4) + (170499864075051/12500000000000 : ℝ)*(sp5) + (136399763121151/10000000000000 : ℝ)*(sp6) + (241281160096899/50000000000000 : ℝ)*(sp7) + (12064058394369/2500000000000 : ℝ)*(f.failure) + (682002834560947/50000000000000 : ℝ)*(f.sum) + (170225276093843/200000000000000000000000000000 : ℝ)*base65 + (632764673906157/400000000000000000000000000000 : ℝ)*base68 + (2848302504306157/400000000000000000000000000000 : ℝ)*base70 + (870240583106157/400000000000000000000000000000 : ℝ)*base72 + (630197511293843/200000000000000000000000000000 : ℝ)*base73 + (639304576493843/400000000000000000000000000000 : ℝ)*base75 + (248285490893843/400000000000000000000000000000 : ℝ)*base77 + (585385666093843/400000000000000000000000000000 : ℝ)*base79 + (215283395106157/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (351619/125000000000000000000 : ℝ)*base90 + (351619/125000000000000000000 : ℝ)*base92 + (351619/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1699_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95664749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (143/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (22303/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1699_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1699_s1_0 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-181027397/1250000000 : ℝ)*x 0 + (5495828213/10000000000 : ℝ)*x 1 + (2560602431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (181027397/1250000000 : ℝ)^5215 ≤ (4516149852743/50000000000000 : ℝ)^4191 := by
    have hnat : (181027397 : ℕ)^5215*50000000000000^4191 ≤ 4516149852743^4191*1250000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181027397 1250000000 4516149852743 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5495828213/10000000000 : ℝ)^5215 ≤ (47480430066157/100000000000000 : ℝ)^4191 := by
    have hnat : (5495828213 : ℕ)^5215*100000000000000^4191 ≤ 47480430066157^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495828213 10000000000 47480430066157 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2560602431/5000000000 : ℝ)^5215 ≤ (8697454041969/20000000000000 : ℝ)^4191 := by
    have hnat : (2560602431 : ℕ)^5215*20000000000000^4191 ≤ 8697454041969^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2560602431 5000000000 8697454041969 20000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-181027397/1250000000 : ℝ), (5495828213/10000000000 : ℝ), (2560602431/5000000000 : ℝ)] ![(4516149852743/50000000000000 : ℝ), (47480430066157/100000000000000 : ℝ), (8697454041969/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-181027397/1250000000 : ℝ)|^5215 ≤ (4516149852743/50000000000000 : ℝ)^4191
        have hw : |(-181027397/1250000000 : ℝ)|=(181027397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5495828213/10000000000 : ℝ)|^5215 ≤ (47480430066157/100000000000000 : ℝ)^4191
        have hw : |(5495828213/10000000000 : ℝ)|=(5495828213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2560602431/5000000000 : ℝ)|^5215 ≤ (8697454041969/20000000000000 : ℝ)^4191
        have hw : |(2560602431/5000000000 : ℝ)|=(2560602431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s1_1 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070447997/2000000000 : ℝ)*x 0 + (-821685997/5000000000 : ℝ)*x 1 + (1280301059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070447997/2000000000 : ℝ)^5215 ≤ (45941781916521/100000000000000 : ℝ)^4191 := by
    have hnat : (1070447997 : ℕ)^5215*100000000000000^4191 ≤ 45941781916521^4191*2000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070447997 2000000000 45941781916521 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (821685997/5000000000 : ℝ)^5215 ≤ (1321369309093/12500000000000 : ℝ)^4191 := by
    have hnat : (821685997 : ℕ)^5215*12500000000000^4191 ≤ 1321369309093^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821685997 5000000000 1321369309093 12500000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1280301059/2500000000 : ℝ)^5215 ≤ (8697452719057/20000000000000 : ℝ)^4191 := by
    have hnat : (1280301059 : ℕ)^5215*20000000000000^4191 ≤ 8697452719057^4191*2500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280301059 2500000000 8697452719057 20000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070447997/2000000000 : ℝ), (-821685997/5000000000 : ℝ), (1280301059/2500000000 : ℝ)] ![(45941781916521/100000000000000 : ℝ), (1321369309093/12500000000000 : ℝ), (8697452719057/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070447997/2000000000 : ℝ)|^5215 ≤ (45941781916521/100000000000000 : ℝ)^4191
        have hw : |(1070447997/2000000000 : ℝ)|=(1070447997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-821685997/5000000000 : ℝ)|^5215 ≤ (1321369309093/12500000000000 : ℝ)^4191
        have hw : |(-821685997/5000000000 : ℝ)|=(821685997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1280301059/2500000000 : ℝ)|^5215 ≤ (8697452719057/20000000000000 : ℝ)^4191
        have hw : |(1280301059/2500000000 : ℝ)|=(1280301059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s1_2 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352238817/10000000000 : ℝ)*x 0 + (5121205253/10000000000 : ℝ)*x 1 + (-164337221/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352238817/10000000000 : ℝ)^5215 ≤ (114854423603/250000000000 : ℝ)^4191 := by
    have hnat : (5352238817 : ℕ)^5215*250000000000^4191 ≤ 114854423603^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352238817 10000000000 114854423603 250000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5121205253/10000000000 : ℝ)^5215 ≤ (5435909292663/12500000000000 : ℝ)^4191 := by
    have hnat : (5121205253 : ℕ)^5215*12500000000000^4191 ≤ 5435909292663^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5121205253 10000000000 5435909292663 12500000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164337221/1000000000 : ℝ)^5215 ≤ (10570956201639/100000000000000 : ℝ)^4191 := by
    have hnat : (164337221 : ℕ)^5215*100000000000000^4191 ≤ 10570956201639^4191*1000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164337221 1000000000 10570956201639 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352238817/10000000000 : ℝ), (5121205253/10000000000 : ℝ), (-164337221/1000000000 : ℝ)] ![(114854423603/250000000000 : ℝ), (5435909292663/12500000000000 : ℝ), (10570956201639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352238817/10000000000 : ℝ)|^5215 ≤ (114854423603/250000000000 : ℝ)^4191
        have hw : |(5352238817/10000000000 : ℝ)|=(5352238817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5121205253/10000000000 : ℝ)|^5215 ≤ (5435909292663/12500000000000 : ℝ)^4191
        have hw : |(5121205253/10000000000 : ℝ)|=(5121205253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-164337221/1000000000 : ℝ)|^5215 ≤ (10570956201639/100000000000000 : ℝ)^4191
        have hw : |(-164337221/1000000000 : ℝ)|=(164337221/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s1_3 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2057770329/5000000000 : ℝ)*x 0 + (3608251389/10000000000 : ℝ)*x 1 + (4667157797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2057770329/5000000000 : ℝ)^5215 ≤ (6625957143399/20000000000000 : ℝ)^4191 := by
    have hnat : (2057770329 : ℕ)^5215*20000000000000^4191 ≤ 6625957143399^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057770329 5000000000 6625957143399 20000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3608251389/10000000000 : ℝ)^5215 ≤ (28127409856111/100000000000000 : ℝ)^4191 := by
    have hnat : (3608251389 : ℕ)^5215*100000000000000^4191 ≤ 28127409856111^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3608251389 10000000000 28127409856111 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4667157797/10000000000 : ℝ)^5215 ≤ (38742804409139/100000000000000 : ℝ)^4191 := by
    have hnat : (4667157797 : ℕ)^5215*100000000000000^4191 ≤ 38742804409139^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4667157797 10000000000 38742804409139 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2057770329/5000000000 : ℝ), (3608251389/10000000000 : ℝ), (4667157797/10000000000 : ℝ)] ![(6625957143399/20000000000000 : ℝ), (28127409856111/100000000000000 : ℝ), (38742804409139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2057770329/5000000000 : ℝ)|^5215 ≤ (6625957143399/20000000000000 : ℝ)^4191
        have hw : |(2057770329/5000000000 : ℝ)|=(2057770329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3608251389/10000000000 : ℝ)|^5215 ≤ (28127409856111/100000000000000 : ℝ)^4191
        have hw : |(3608251389/10000000000 : ℝ)|=(3608251389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4667157797/10000000000 : ℝ)|^5215 ≤ (38742804409139/100000000000000 : ℝ)^4191
        have hw : |(4667157797/10000000000 : ℝ)|=(4667157797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s1_4 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-181053503/1250000000 : ℝ)*x 0 + (2562861593/5000000000 : ℝ)*x 1 + (2745617721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (181053503/1250000000 : ℝ)^5215 ≤ (1129240067497/12500000000000 : ℝ)^4191 := by
    have hnat : (181053503 : ℕ)^5215*12500000000000^4191 ≤ 1129240067497^4191*1250000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181053503 1250000000 1129240067497 12500000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2562861593/5000000000 : ℝ)^5215 ≤ (43535017729617/100000000000000 : ℝ)^4191 := by
    have hnat : (2562861593 : ℕ)^5215*100000000000000^4191 ≤ 43535017729617^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2562861593 5000000000 43535017729617 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2745617721/5000000000 : ℝ)^5215 ≤ (47431061718867/100000000000000 : ℝ)^4191 := by
    have hnat : (2745617721 : ℕ)^5215*100000000000000^4191 ≤ 47431061718867^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745617721 5000000000 47431061718867 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-181053503/1250000000 : ℝ), (2562861593/5000000000 : ℝ), (2745617721/5000000000 : ℝ)] ![(1129240067497/12500000000000 : ℝ), (43535017729617/100000000000000 : ℝ), (47431061718867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-181053503/1250000000 : ℝ)|^5215 ≤ (1129240067497/12500000000000 : ℝ)^4191
        have hw : |(-181053503/1250000000 : ℝ)|=(181053503/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2562861593/5000000000 : ℝ)|^5215 ≤ (43535017729617/100000000000000 : ℝ)^4191
        have hw : |(2562861593/5000000000 : ℝ)|=(2562861593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2745617721/5000000000 : ℝ)|^5215 ≤ (47431061718867/100000000000000 : ℝ)^4191
        have hw : |(2745617721/5000000000 : ℝ)|=(2745617721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s1_5 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656494859/1250000000 : ℝ)*x 0 + (-1273341033/10000000000 : ℝ)*x 1 + (5491235431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656494859/1250000000 : ℝ)^5215 ≤ (22436575054193/50000000000000 : ℝ)^4191 := by
    have hnat : (656494859 : ℕ)^5215*50000000000000^4191 ≤ 22436575054193^4191*1250000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656494859 1250000000 22436575054193 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1273341033/10000000000 : ℝ)^5215 ≤ (7695788280517/100000000000000 : ℝ)^4191 := by
    have hnat : (1273341033 : ℕ)^5215*100000000000000^4191 ≤ 7695788280517^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1273341033 10000000000 7695788280517 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5491235431/10000000000 : ℝ)^5215 ≤ (23715530800319/50000000000000 : ℝ)^4191 := by
    have hnat : (5491235431 : ℕ)^5215*50000000000000^4191 ≤ 23715530800319^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491235431 10000000000 23715530800319 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656494859/1250000000 : ℝ), (-1273341033/10000000000 : ℝ), (5491235431/10000000000 : ℝ)] ![(22436575054193/50000000000000 : ℝ), (7695788280517/100000000000000 : ℝ), (23715530800319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656494859/1250000000 : ℝ)|^5215 ≤ (22436575054193/50000000000000 : ℝ)^4191
        have hw : |(656494859/1250000000 : ℝ)|=(656494859/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1273341033/10000000000 : ℝ)|^5215 ≤ (7695788280517/100000000000000 : ℝ)^4191
        have hw : |(-1273341033/10000000000 : ℝ)|=(1273341033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5491235431/10000000000 : ℝ)|^5215 ≤ (23715530800319/50000000000000 : ℝ)^4191
        have hw : |(5491235431/10000000000 : ℝ)|=(5491235431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s1_6 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251958821/10000000000 : ℝ)*x 0 + (2745617599/5000000000 : ℝ)*x 1 + (-636670719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251958821/10000000000 : ℝ)^5215 ≤ (4487314956617/10000000000000 : ℝ)^4191 := by
    have hnat : (5251958821 : ℕ)^5215*10000000000000^4191 ≤ 4487314956617^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251958821 10000000000 4487314956617 10000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2745617599/5000000000 : ℝ)^5215 ≤ (5928882387043/12500000000000 : ℝ)^4191 := by
    have hnat : (2745617599 : ℕ)^5215*12500000000000^4191 ≤ 5928882387043^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745617599 5000000000 5928882387043 12500000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (636670719/5000000000 : ℝ)^5215 ≤ (1923947831577/25000000000000 : ℝ)^4191 := by
    have hnat : (636670719 : ℕ)^5215*25000000000000^4191 ≤ 1923947831577^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      636670719 5000000000 1923947831577 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251958821/10000000000 : ℝ), (2745617599/5000000000 : ℝ), (-636670719/5000000000 : ℝ)] ![(4487314956617/10000000000000 : ℝ), (5928882387043/12500000000000 : ℝ), (1923947831577/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251958821/10000000000 : ℝ)|^5215 ≤ (4487314956617/10000000000000 : ℝ)^4191
        have hw : |(5251958821/10000000000 : ℝ)|=(5251958821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2745617599/5000000000 : ℝ)|^5215 ≤ (5928882387043/12500000000000 : ℝ)^4191
        have hw : |(2745617599/5000000000 : ℝ)|=(2745617599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-636670719/5000000000 : ℝ)|^5215 ≤ (1923947831577/25000000000000 : ℝ)^4191
        have hw : |(-636670719/5000000000 : ℝ)|=(636670719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s1_7 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (205806549/500000000 : ℝ)*x 0 + (465438581/1000000000 : ℝ)*x 1 + (3621232313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205806549/500000000 : ℝ)^5215 ≤ (33135698949573/100000000000000 : ℝ)^4191 := by
    have hnat : (205806549 : ℕ)^5215*100000000000000^4191 ≤ 33135698949573^4191*500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205806549 500000000 33135698949573 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (465438581/1000000000 : ℝ)^5215 ≤ (38610921544277/100000000000000 : ℝ)^4191 := by
    have hnat : (465438581 : ℕ)^5215*100000000000000^4191 ≤ 38610921544277^4191*1000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465438581 1000000000 38610921544277 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3621232313/10000000000 : ℝ)^5215 ≤ (28253379491427/100000000000000 : ℝ)^4191 := by
    have hnat : (3621232313 : ℕ)^5215*100000000000000^4191 ≤ 28253379491427^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3621232313 10000000000 28253379491427 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(205806549/500000000 : ℝ), (465438581/1000000000 : ℝ), (3621232313/10000000000 : ℝ)] ![(33135698949573/100000000000000 : ℝ), (38610921544277/100000000000000 : ℝ), (28253379491427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(205806549/500000000 : ℝ)|^5215 ≤ (33135698949573/100000000000000 : ℝ)^4191
        have hw : |(205806549/500000000 : ℝ)|=(205806549/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(465438581/1000000000 : ℝ)|^5215 ≤ (38610921544277/100000000000000 : ℝ)^4191
        have hw : |(465438581/1000000000 : ℝ)|=(465438581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3621232313/10000000000 : ℝ)|^5215 ≤ (28253379491427/100000000000000 : ℝ)^4191
        have hw : |(3621232313/10000000000 : ℝ)|=(3621232313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1699_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95664749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22303/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (143/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (4789/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8781/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (22303/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (143/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (22303/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (143/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (22303/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (143/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (22303/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (143/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (22303/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (143/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (22303/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (143/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (143/2500 : ℝ) ^ (5207/1024 : ℝ) ≤ (48018362474159/100000000000000000000 : ℝ) := by
    have hpowers : (143/2500 : ℝ)^5207 ≤ (48018362474159/100000000000000000000 : ℝ)^1024 := by
      have hnat : (143 : ℕ)^5207*100000000000000000000^1024 ≤ 48018362474159^1024*2500^5207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        143 2500 48018362474159 100000000000000000000 5207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (143/2500 : ℝ)) (X := (48018362474159/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (22303/100000 : ℝ) ^ (5207/1024 : ℝ) ≤ (24289734065852763/50000000000000000000 : ℝ) := by
    have hpowers : (22303/100000 : ℝ)^5207 ≤ (24289734065852763/50000000000000000000 : ℝ)^1024 := by
      have hnat : (22303 : ℕ)^5207*50000000000000000000^1024 ≤ 24289734065852763^1024*100000^5207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22303 100000 24289734065852763 50000000000000000000 5207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22303/100000 : ℝ)) (X := (24289734065852763/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000048018362474159/50000000000000000000 : ℝ) ≤ (5000000944320803/5000000000000000 : ℝ) ^ (5207/1024 : ℝ) := by
    have hpowers : (50000048018362474159/50000000000000000000 : ℝ)^1024 ≤ (5000000944320803/5000000000000000 : ℝ)^5207 := by
      have hnat : (50000048018362474159 : ℕ)^1024*5000000000000000^5207 ≤ 5000000944320803^5207*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000048018362474159 50000000000000000000 5000000944320803 5000000000000000 1024 5207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000944320803/5000000000000000 : ℝ)) (X := (50000048018362474159/50000000000000000000 : ℝ)) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009725497298835937/20000000000000000000 : ℝ) ≤ (5000478056683507/5000000000000000 : ℝ) ^ (5207/1024 : ℝ) := by
    have hpowers : (20009725497298835937/20000000000000000000 : ℝ)^1024 ≤ (5000478056683507/5000000000000000 : ℝ)^5207 := by
      have hnat : (20009725497298835937 : ℕ)^1024*5000000000000000^5207 ≤ 5000478056683507^5207*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009725497298835937 20000000000000000000 5000478056683507 5000000000000000 1024 5207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000478056683507/5000000000000000 : ℝ)) (X := (20009725497298835937/20000000000000000000 : ℝ)) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25024289734065852763/25000000000000000000 : ℝ) ≤ (5000955169046211/5000000000000000 : ℝ) ^ (5207/1024 : ℝ) := by
    have hpowers : (25024289734065852763/25000000000000000000 : ℝ)^1024 ≤ (5000955169046211/5000000000000000 : ℝ)^5207 := by
      have hnat : (25024289734065852763 : ℕ)^1024*5000000000000000^5207 ≤ 5000955169046211^5207*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25024289734065852763 25000000000000000000 5000955169046211 5000000000000000 1024 5207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000955169046211/5000000000000000 : ℝ)) (X := (25024289734065852763/25000000000000000000 : ℝ)) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(48018362474159/100000000000000000000 : ℝ) ≤ ((82909557494242542389/82915000000000000000 : ℝ)+2*(29819522669/51821875000000 : ℝ)*(143/2500 : ℝ))^(5207/1024 : ℝ) := by
    rw [show (82909557494242542389/82915000000000000000 : ℝ)+2*(29819522669/51821875000000 : ℝ)*(143/2500 : ℝ)=(5000000944320803/5000000000000000 : ℝ) by norm_num, show 1+2*(48018362474159/100000000000000000000 : ℝ)=(50000048018362474159/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24289734065852763/50000000000000000000 : ℝ)+(48018362474159/100000000000000000000 : ℝ) ≤ ((82909557494242542389/82915000000000000000 : ℝ)+(29819522669/51821875000000 : ℝ)*((22303/100000 : ℝ)+(143/2500 : ℝ)))^(5207/1024 : ℝ) := by
    rw [show (82909557494242542389/82915000000000000000 : ℝ)+(29819522669/51821875000000 : ℝ)*((22303/100000 : ℝ)+(143/2500 : ℝ))=(5000478056683507/5000000000000000 : ℝ) by norm_num, show 1+(24289734065852763/50000000000000000000 : ℝ)+(48018362474159/100000000000000000000 : ℝ)=(20009725497298835937/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24289734065852763/50000000000000000000 : ℝ) ≤ ((82909557494242542389/82915000000000000000 : ℝ)+2*(29819522669/51821875000000 : ℝ)*(22303/100000 : ℝ))^(5207/1024 : ℝ) := by
    rw [show (82909557494242542389/82915000000000000000 : ℝ)+2*(29819522669/51821875000000 : ℝ)*(22303/100000 : ℝ)=(5000955169046211/5000000000000000 : ℝ) by norm_num, show 1+2*(24289734065852763/50000000000000000000 : ℝ)=(25024289734065852763/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (82909557494242542389/82915000000000000000 : ℝ)*(X 1 0+X 2 0)+(29819522669/51821875000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5207/1024 : ℝ)) (lo := (143/2500 : ℝ)) (hi := (22303/100000 : ℝ)) (c := (82909557494242542389/82915000000000000000 : ℝ)) (alpha := (29819522669/51821875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (82909557494242542389/82915000000000000000 : ℝ)*(X 0 1+X 2 1)+(29819522669/51821875000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5207/1024 : ℝ)) (lo := (143/2500 : ℝ)) (hi := (22303/100000 : ℝ)) (c := (82909557494242542389/82915000000000000000 : ℝ)) (alpha := (29819522669/51821875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (82909557494242542389/82915000000000000000 : ℝ)*(X 0 2+X 1 2)+(29819522669/51821875000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5207/1024 : ℝ)) (lo := (143/2500 : ℝ)) (hi := (22303/100000 : ℝ)) (c := (82909557494242542389/82915000000000000000 : ℝ)) (alpha := (29819522669/51821875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-181027397/1250000000 : ℝ)*X 0 0+(5495828213/10000000000 : ℝ)*X 0 1+(2560602431/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070447997/2000000000 : ℝ)*X 1 0+(-821685997/5000000000 : ℝ)*X 1 1+(1280301059/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352238817/10000000000 : ℝ)*X 2 0+(5121205253/10000000000 : ℝ)*X 2 1+(-164337221/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2057770329/5000000000 : ℝ)*X 0 0+(3608251389/10000000000 : ℝ)*X 0 1+(4667157797/10000000000 : ℝ)*X 0 2+(2057770329/5000000000 : ℝ)*X 1 0+(3608251389/10000000000 : ℝ)*X 1 1+(4667157797/10000000000 : ℝ)*X 1 2+(2057770329/5000000000 : ℝ)*X 2 0+(3608251389/10000000000 : ℝ)*X 2 1+(4667157797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-181053503/1250000000 : ℝ)*X 0 0+(2562861593/5000000000 : ℝ)*X 0 1+(2745617721/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((656494859/1250000000 : ℝ)*X 1 0+(-1273341033/10000000000 : ℝ)*X 1 1+(5491235431/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5251958821/10000000000 : ℝ)*X 2 0+(2745617599/5000000000 : ℝ)*X 2 1+(-636670719/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((205806549/500000000 : ℝ)*X 0 0+(465438581/1000000000 : ℝ)*X 0 1+(3621232313/10000000000 : ℝ)*X 0 2+(205806549/500000000 : ℝ)*X 1 0+(465438581/1000000000 : ℝ)*X 1 1+(3621232313/10000000000 : ℝ)*X 1 2+(205806549/500000000 : ℝ)*X 2 0+(465438581/1000000000 : ℝ)*X 2 1+(3621232313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14306950826765601934399022967/4145750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8903101/4000000000000 : ℝ)*(base19) + (12017439/12500000000000 : ℝ)*(upper2) + (229521/10000000000000 : ℝ)*(upper3) + (1122/1220703125 : ℝ)*(lower4) + (12614063/100000000000000 : ℝ)*(upper5) + (1806861579612599/100000000000000 : ℝ)*(major0) + (1806861579612599/100000000000000 : ℝ)*(major1) + (1806861579612599/100000000000000 : ℝ)*(major2) + (1334675686012227/50000000000000 : ℝ)*(sp0) + (667337376547869/25000000000000 : ℝ)*(sp1) + (667337546808129/25000000000000 : ℝ)*(sp2) + (188874334433533/20000000000000 : ℝ)*(sp3) + (328651091/20000000000000 : ℝ)*(sp5) + (592395969/50000000000000 : ℝ)*(sp6) + (188874334433533/20000000000000 : ℝ)*(f.failure) + (1334675686012227/50000000000000 : ℝ)*(f.sum) + (211583631550499/41457500000000000000000000000 : ℝ)*base66 + (42486078845915059011/8291500000000000000000000000000000 : ℝ)*base67 + (57782470489826059011/8291500000000000000000000000000000 : ℝ)*base69 + (27525529682159440989/8291500000000000000000000000000000 : ℝ)*base72 + (120576558991051/41457500000000000000000000000 : ℝ)*base73 + (84753580885783440989/8291500000000000000000000000000000 : ℝ)*base76 + (47052001827265559011/8291500000000000000000000000000000 : ℝ)*base77 + (13426696531260059011/8291500000000000000000000000000000 : ℝ)*base79 + (86525077510477/82915000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base85 + (1628217/1000000000000000000000 : ℝ)*base89 + (1628217/1000000000000000000000 : ℝ)*base91 + (1628217/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (253835737142405566541704743/64777343750000000000000000000000 : ℝ) := by norm_num
    linear_combination (374518341/50000000000000 : ℝ)*(base19) + (676428133/100000000000000 : ℝ)*(base23) + (151683/5000000000000 : ℝ)*(upper2) + (109693471/100000000000000 : ℝ)*(upper3) + (88620839/100000000000000 : ℝ)*(upper5) + (57871815911771/3125000000000 : ℝ)*(major0) + (57871815911771/3125000000000 : ℝ)*(major1) + (57871815911771/3125000000000 : ℝ)*(major2) + (3040555271/50000000000000 : ℝ)*(sp1) + (336734113/10000000000000 : ℝ)*(sp2) + (109435427514223/4000000000000 : ℝ)*(sp4) + (2735878857708351/100000000000000 : ℝ)*(sp5) + (341985205510789/12500000000000 : ℝ)*(sp6) + (483955199939079/50000000000000 : ℝ)*(sp7) + (483955199939079/50000000000000 : ℝ)*(f.failure) + (109435427514223/4000000000000 : ℝ)*(f.sum) + (4513869096911/5182187500000000000000000000 : ℝ)*base65 + (370831320480117169/259109375000000000000000000000000 : ℝ)*base67 + (693057491715398419/259109375000000000000000000000000 : ℝ)*base69 + (1242009676781429669/259109375000000000000000000000000 : ℝ)*base71 + (129560835179659/82915000000000000000000000000 : ℝ)*base74 + (432922154091535147/129554687500000000000000000000000 : ℝ)*base75 + (1464833525189867169/259109375000000000000000000000000 : ℝ)*base77 + (2014660103307820331/259109375000000000000000000000000 : ℝ)*base80 + (11741220307753/41457500000000000000000000000 : ℝ)*base81 + (7826171/2500000000000000000000 : ℝ)*base89 + (7826171/2500000000000000000000 : ℝ)*base91 + (7826171/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1699_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95664749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22303/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (143/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4789/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8781/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1699_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1699_s2_0 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1452628201/10000000000 : ℝ)*x 0 + (5477961671/10000000000 : ℝ)*x 1 + (1284032559/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1452628201/10000000000 : ℝ)^5215 ≤ (2266632381709/25000000000000 : ℝ)^4191 := by
    have hnat : (1452628201 : ℕ)^5215*25000000000000^4191 ≤ 2266632381709^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1452628201 10000000000 2266632381709 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5477961671/10000000000 : ℝ)^5215 ≤ (47288436801449/100000000000000 : ℝ)^4191 := by
    have hnat : (5477961671 : ℕ)^5215*100000000000000^4191 ≤ 47288436801449^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477961671 10000000000 47288436801449 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1284032559/2500000000 : ℝ)^5215 ≤ (545562920589/1250000000000 : ℝ)^4191 := by
    have hnat : (1284032559 : ℕ)^5215*1250000000000^4191 ≤ 545562920589^4191*2500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284032559 2500000000 545562920589 1250000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1452628201/10000000000 : ℝ), (5477961671/10000000000 : ℝ), (1284032559/2500000000 : ℝ)] ![(2266632381709/25000000000000 : ℝ), (47288436801449/100000000000000 : ℝ), (545562920589/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1452628201/10000000000 : ℝ)|^5215 ≤ (2266632381709/25000000000000 : ℝ)^4191
        have hw : |(-1452628201/10000000000 : ℝ)|=(1452628201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5477961671/10000000000 : ℝ)|^5215 ≤ (47288436801449/100000000000000 : ℝ)^4191
        have hw : |(5477961671/10000000000 : ℝ)|=(5477961671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1284032559/2500000000 : ℝ)|^5215 ≤ (545562920589/1250000000000 : ℝ)^4191
        have hw : |(1284032559/2500000000 : ℝ)|=(1284032559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s2_1 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336856389/2500000000 : ℝ)*x 0 + (-1630070889/10000000000 : ℝ)*x 1 + (2568065371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336856389/2500000000 : ℝ)^5215 ≤ (2294518250419/5000000000000 : ℝ)^4191 := by
    have hnat : (1336856389 : ℕ)^5215*5000000000000^4191 ≤ 2294518250419^4191*2500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336856389 2500000000 2294518250419 5000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1630070889/10000000000 : ℝ)^5215 ≤ (5232297989699/50000000000000 : ℝ)^4191 := by
    have hnat : (1630070889 : ℕ)^5215*50000000000000^4191 ≤ 5232297989699^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1630070889 10000000000 5232297989699 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2568065371/5000000000 : ℝ)^5215 ≤ (43645038997517/100000000000000 : ℝ)^4191 := by
    have hnat : (2568065371 : ℕ)^5215*100000000000000^4191 ≤ 43645038997517^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568065371 5000000000 43645038997517 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336856389/2500000000 : ℝ), (-1630070889/10000000000 : ℝ), (2568065371/5000000000 : ℝ)] ![(2294518250419/5000000000000 : ℝ), (5232297989699/50000000000000 : ℝ), (43645038997517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336856389/2500000000 : ℝ)|^5215 ≤ (2294518250419/5000000000000 : ℝ)^4191
        have hw : |(1336856389/2500000000 : ℝ)|=(1336856389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1630070889/10000000000 : ℝ)|^5215 ≤ (5232297989699/50000000000000 : ℝ)^4191
        have hw : |(-1630070889/10000000000 : ℝ)|=(1630070889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2568065371/5000000000 : ℝ)|^5215 ≤ (43645038997517/100000000000000 : ℝ)^4191
        have hw : |(2568065371/5000000000 : ℝ)|=(2568065371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s2_2 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336856269/2500000000 : ℝ)*x 0 + (1027226163/2000000000 : ℝ)*x 1 + (-815035717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336856269/2500000000 : ℝ)^5215 ≤ (22945179941331/50000000000000 : ℝ)^4191 := by
    have hnat : (1336856269 : ℕ)^5215*50000000000000^4191 ≤ 22945179941331^4191*2500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336856269 2500000000 22945179941331 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027226163/2000000000 : ℝ)^5215 ≤ (10911259942353/25000000000000 : ℝ)^4191 := by
    have hnat : (1027226163 : ℕ)^5215*25000000000000^4191 ≤ 10911259942353^4191*2000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027226163 2000000000 10911259942353 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (815035717/5000000000 : ℝ)^5215 ≤ (2616150083251/25000000000000 : ℝ)^4191 := by
    have hnat : (815035717 : ℕ)^5215*25000000000000^4191 ≤ 2616150083251^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      815035717 5000000000 2616150083251 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336856269/2500000000 : ℝ), (1027226163/2000000000 : ℝ), (-815035717/5000000000 : ℝ)] ![(22945179941331/50000000000000 : ℝ), (10911259942353/25000000000000 : ℝ), (2616150083251/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336856269/2500000000 : ℝ)|^5215 ≤ (22945179941331/50000000000000 : ℝ)^4191
        have hw : |(1336856269/2500000000 : ℝ)|=(1336856269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027226163/2000000000 : ℝ)|^5215 ≤ (10911259942353/25000000000000 : ℝ)^4191
        have hw : |(1027226163/2000000000 : ℝ)|=(1027226163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-815035717/5000000000 : ℝ)|^5215 ≤ (2616150083251/25000000000000 : ℝ)^4191
        have hw : |(-815035717/5000000000 : ℝ)|=(815035717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s2_3 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2059471923/5000000000 : ℝ)*x 0 + (182714331/500000000 : ℝ)*x 1 + (4620503041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2059471923/5000000000 : ℝ)^5215 ≤ (6632775632971/20000000000000 : ℝ)^4191 := by
    have hnat : (2059471923 : ℕ)^5215*20000000000000^4191 ≤ 6632775632971^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059471923 5000000000 6632775632971 20000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182714331/500000000 : ℝ)^5215 ≤ (7143660794669/25000000000000 : ℝ)^4191 := by
    have hnat : (182714331 : ℕ)^5215*25000000000000^4191 ≤ 7143660794669^4191*500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182714331 500000000 7143660794669 25000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4620503041/10000000000 : ℝ)^5215 ≤ (19130739324531/50000000000000 : ℝ)^4191 := by
    have hnat : (4620503041 : ℕ)^5215*50000000000000^4191 ≤ 19130739324531^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4620503041 10000000000 19130739324531 50000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2059471923/5000000000 : ℝ), (182714331/500000000 : ℝ), (4620503041/10000000000 : ℝ)] ![(6632775632971/20000000000000 : ℝ), (7143660794669/25000000000000 : ℝ), (19130739324531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2059471923/5000000000 : ℝ)|^5215 ≤ (6632775632971/20000000000000 : ℝ)^4191
        have hw : |(2059471923/5000000000 : ℝ)|=(2059471923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(182714331/500000000 : ℝ)|^5215 ≤ (7143660794669/25000000000000 : ℝ)^4191
        have hw : |(182714331/500000000 : ℝ)|=(182714331/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4620503041/10000000000 : ℝ)|^5215 ≤ (19130739324531/50000000000000 : ℝ)^4191
        have hw : |(4620503041/10000000000 : ℝ)|=(4620503041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s2_4 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-45399579/312500000 : ℝ)*x 0 + (5139895639/10000000000 : ℝ)*x 1 + (5474139951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (45399579/312500000 : ℝ)^5215 ≤ (9067759183949/100000000000000 : ℝ)^4191 := by
    have hnat : (45399579 : ℕ)^5215*100000000000000^4191 ≤ 9067759183949^4191*312500000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45399579 312500000 9067759183949 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5139895639/10000000000 : ℝ)^5215 ≤ (43684852230857/100000000000000 : ℝ)^4191 := by
    have hnat : (5139895639 : ℕ)^5215*100000000000000^4191 ≤ 43684852230857^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139895639 10000000000 43684852230857 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5474139951/10000000000 : ℝ)^5215 ≤ (4724738856883/10000000000000 : ℝ)^4191 := by
    have hnat : (5474139951 : ℕ)^5215*10000000000000^4191 ≤ 4724738856883^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474139951 10000000000 4724738856883 10000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-45399579/312500000 : ℝ), (5139895639/10000000000 : ℝ), (5474139951/10000000000 : ℝ)] ![(9067759183949/100000000000000 : ℝ), (43684852230857/100000000000000 : ℝ), (4724738856883/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-45399579/312500000 : ℝ)|^5215 ≤ (9067759183949/100000000000000 : ℝ)^4191
        have hw : |(-45399579/312500000 : ℝ)|=(45399579/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5139895639/10000000000 : ℝ)|^5215 ≤ (43684852230857/100000000000000 : ℝ)^4191
        have hw : |(5139895639/10000000000 : ℝ)|=(5139895639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5474139951/10000000000 : ℝ)|^5215 ≤ (4724738856883/10000000000000 : ℝ)^4191
        have hw : |(5474139951/10000000000 : ℝ)|=(5474139951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s2_5 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627984127/5000000000 : ℝ)*x 0 + (-646031001/5000000000 : ℝ)*x 1 + (1368534991/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627984127/5000000000 : ℝ)^5215 ≤ (8983156109847/20000000000000 : ℝ)^4191 := by
    have hnat : (2627984127 : ℕ)^5215*20000000000000^4191 ≤ 8983156109847^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627984127 5000000000 8983156109847 20000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (646031001/5000000000 : ℝ)^5215 ≤ (7836830727543/100000000000000 : ℝ)^4191 := by
    have hnat : (646031001 : ℕ)^5215*100000000000000^4191 ≤ 7836830727543^4191*5000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646031001 5000000000 7836830727543 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1368534991/2500000000 : ℝ)^5215 ≤ (1476480897139/3125000000000 : ℝ)^4191 := by
    have hnat : (1368534991 : ℕ)^5215*3125000000000^4191 ≤ 1476480897139^4191*2500000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368534991 2500000000 1476480897139 3125000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627984127/5000000000 : ℝ), (-646031001/5000000000 : ℝ), (1368534991/2500000000 : ℝ)] ![(8983156109847/20000000000000 : ℝ), (7836830727543/100000000000000 : ℝ), (1476480897139/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627984127/5000000000 : ℝ)|^5215 ≤ (8983156109847/20000000000000 : ℝ)^4191
        have hw : |(2627984127/5000000000 : ℝ)|=(2627984127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-646031001/5000000000 : ℝ)|^5215 ≤ (7836830727543/100000000000000 : ℝ)^4191
        have hw : |(-646031001/5000000000 : ℝ)|=(646031001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1368534991/2500000000 : ℝ)|^5215 ≤ (1476480897139/3125000000000 : ℝ)^4191
        have hw : |(1368534991/2500000000 : ℝ)|=(1368534991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s2_6 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656996031/1250000000 : ℝ)*x 0 + (5474139971/10000000000 : ℝ)*x 1 + (-646031/5000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656996031/1250000000 : ℝ)^5215 ≤ (44915780485433/100000000000000 : ℝ)^4191 := by
    have hnat : (656996031 : ℕ)^5215*100000000000000^4191 ≤ 44915780485433^4191*1250000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656996031 1250000000 44915780485433 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5474139971/10000000000 : ℝ)^5215 ≤ (47247388783627/100000000000000 : ℝ)^4191 := by
    have hnat : (5474139971 : ℕ)^5215*100000000000000^4191 ≤ 47247388783627^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474139971 10000000000 47247388783627 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (646031/5000000 : ℝ)^5215 ≤ (7836830712449/100000000000000 : ℝ)^4191 := by
    have hnat : (646031 : ℕ)^5215*100000000000000^4191 ≤ 7836830712449^4191*5000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646031 5000000 7836830712449 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656996031/1250000000 : ℝ), (5474139971/10000000000 : ℝ), (-646031/5000000 : ℝ)] ![(44915780485433/100000000000000 : ℝ), (47247388783627/100000000000000 : ℝ), (7836830712449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656996031/1250000000 : ℝ)|^5215 ≤ (44915780485433/100000000000000 : ℝ)^4191
        have hw : |(656996031/1250000000 : ℝ)|=(656996031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5474139971/10000000000 : ℝ)|^5215 ≤ (47247388783627/100000000000000 : ℝ)^4191
        have hw : |(5474139971/10000000000 : ℝ)|=(5474139971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-646031/5000000 : ℝ)|^5215 ≤ (7836830712449/100000000000000 : ℝ)^4191
        have hw : |(-646031/5000000 : ℝ)|=(646031/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1699_s2_7 (p : ℝ) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (823878287/2000000000 : ℝ)*x 0 + (4609860569/10000000000 : ℝ)*x 1 + (3665089003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (823878287/2000000000 : ℝ)^5215 ≤ (33168362533029/100000000000000 : ℝ)^4191 := by
    have hnat : (823878287 : ℕ)^5215*100000000000000^4191 ≤ 33168362533029^4191*2000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823878287 2000000000 33168362533029 100000000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4609860569/10000000000 : ℝ)^5215 ≤ (4768981082713/12500000000000 : ℝ)^4191 := by
    have hnat : (4609860569 : ℕ)^5215*12500000000000^4191 ≤ 4768981082713^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4609860569 10000000000 4768981082713 12500000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3665089003/10000000000 : ℝ)^5215 ≤ (896243399497/3125000000000 : ℝ)^4191 := by
    have hnat : (3665089003 : ℕ)^5215*3125000000000^4191 ≤ 896243399497^4191*10000000000^5215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3665089003 10000000000 896243399497 3125000000000 5215 4191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5215/1024 : ℝ)) 5215 4191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(823878287/2000000000 : ℝ), (4609860569/10000000000 : ℝ), (3665089003/10000000000 : ℝ)] ![(33168362533029/100000000000000 : ℝ), (4768981082713/12500000000000 : ℝ), (896243399497/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(823878287/2000000000 : ℝ)|^5215 ≤ (33168362533029/100000000000000 : ℝ)^4191
        have hw : |(823878287/2000000000 : ℝ)|=(823878287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4609860569/10000000000 : ℝ)|^5215 ≤ (4768981082713/12500000000000 : ℝ)^4191
        have hw : |(4609860569/10000000000 : ℝ)|=(4609860569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3665089003/10000000000 : ℝ)|^5215 ≤ (896243399497/3125000000000 : ℝ)^4191
        have hw : |(3665089003/10000000000 : ℝ)|=(3665089003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1699_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95664749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8781/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4789/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4951/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4297/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8781/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4789/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8781/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4789/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8781/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4789/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8781/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4789/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8781/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4789/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8781/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4789/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4789/50000 : ℝ) ^ (5207/1024 : ℝ) ≤ (330211597779503/50000000000000000000 : ℝ) := by
    have hpowers : (4789/50000 : ℝ)^5207 ≤ (330211597779503/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4789 : ℕ)^5207*50000000000000000000^1024 ≤ 330211597779503^1024*50000^5207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4789 50000 330211597779503 50000000000000000000 5207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4789/50000 : ℝ)) (X := (330211597779503/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8781/50000 : ℝ) ^ (5207/1024 : ℝ) ≤ (3602700578475543/25000000000000000000 : ℝ) := by
    have hpowers : (8781/50000 : ℝ)^5207 ≤ (3602700578475543/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8781 : ℕ)^5207*25000000000000000000^1024 ≤ 3602700578475543^1024*50000^5207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8781 50000 3602700578475543 25000000000000000000 5207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8781/50000 : ℝ)) (X := (3602700578475543/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000330211597779503/25000000000000000000 : ℝ) ≤ (625001623463041/625000000000000 : ℝ) ^ (5207/1024 : ℝ) := by
    have hpowers : (25000330211597779503/25000000000000000000 : ℝ)^1024 ≤ (625001623463041/625000000000000 : ℝ)^5207 := by
      have hnat : (25000330211597779503 : ℕ)^1024*625000000000000^5207 ≤ 625001623463041^5207*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000330211597779503 25000000000000000000 625001623463041 625000000000000 1024 5207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625001623463041/625000000000000 : ℝ)) (X := (25000330211597779503/25000000000000000000 : ℝ)) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50007535612754730589/50000000000000000000 : ℝ) ≤ (5000148185142569/5000000000000000 : ℝ) ^ (5207/1024 : ℝ) := by
    have hpowers : (50007535612754730589/50000000000000000000 : ℝ)^1024 ≤ (5000148185142569/5000000000000000 : ℝ)^5207 := by
      have hnat : (50007535612754730589 : ℕ)^1024*5000000000000000^5207 ≤ 5000148185142569^5207*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007535612754730589 50000000000000000000 5000148185142569 5000000000000000 1024 5207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000148185142569/5000000000000000 : ℝ)) (X := (50007535612754730589/50000000000000000000 : ℝ)) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12503602700578475543/12500000000000000000 : ℝ) ≤ (500028338258081/500000000000000 : ℝ) ^ (5207/1024 : ℝ) := by
    have hpowers : (12503602700578475543/12500000000000000000 : ℝ)^1024 ≤ (500028338258081/500000000000000 : ℝ)^5207 := by
      have hnat : (12503602700578475543 : ℕ)^1024*500000000000000^5207 ≤ 500028338258081^5207*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503602700578475543 12500000000000000000 500028338258081 500000000000000 1024 5207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500028338258081/500000000000000 : ℝ)) (X := (12503602700578475543/12500000000000000000 : ℝ)) (by norm_num) 5207 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(330211597779503/50000000000000000000 : ℝ) ≤ ((9979378462926102539/9980000000000000000 : ℝ)+2*(135197438241/399200000000000 : ℝ)*(4789/50000 : ℝ))^(5207/1024 : ℝ) := by
    rw [show (9979378462926102539/9980000000000000000 : ℝ)+2*(135197438241/399200000000000 : ℝ)*(4789/50000 : ℝ)=(625001623463041/625000000000000 : ℝ) by norm_num, show 1+2*(330211597779503/50000000000000000000 : ℝ)=(25000330211597779503/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3602700578475543/25000000000000000000 : ℝ)+(330211597779503/50000000000000000000 : ℝ) ≤ ((9979378462926102539/9980000000000000000 : ℝ)+(135197438241/399200000000000 : ℝ)*((8781/50000 : ℝ)+(4789/50000 : ℝ)))^(5207/1024 : ℝ) := by
    rw [show (9979378462926102539/9980000000000000000 : ℝ)+(135197438241/399200000000000 : ℝ)*((8781/50000 : ℝ)+(4789/50000 : ℝ))=(5000148185142569/5000000000000000 : ℝ) by norm_num, show 1+(3602700578475543/25000000000000000000 : ℝ)+(330211597779503/50000000000000000000 : ℝ)=(50007535612754730589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3602700578475543/25000000000000000000 : ℝ) ≤ ((9979378462926102539/9980000000000000000 : ℝ)+2*(135197438241/399200000000000 : ℝ)*(8781/50000 : ℝ))^(5207/1024 : ℝ) := by
    rw [show (9979378462926102539/9980000000000000000 : ℝ)+2*(135197438241/399200000000000 : ℝ)*(8781/50000 : ℝ)=(500028338258081/500000000000000 : ℝ) by norm_num, show 1+2*(3602700578475543/25000000000000000000 : ℝ)=(12503602700578475543/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9979378462926102539/9980000000000000000 : ℝ)*(X 1 0+X 2 0)+(135197438241/399200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5207/1024 : ℝ)) (lo := (4789/50000 : ℝ)) (hi := (8781/50000 : ℝ)) (c := (9979378462926102539/9980000000000000000 : ℝ)) (alpha := (135197438241/399200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9979378462926102539/9980000000000000000 : ℝ)*(X 0 1+X 2 1)+(135197438241/399200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5207/1024 : ℝ)) (lo := (4789/50000 : ℝ)) (hi := (8781/50000 : ℝ)) (c := (9979378462926102539/9980000000000000000 : ℝ)) (alpha := (135197438241/399200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9979378462926102539/9980000000000000000 : ℝ)*(X 0 2+X 1 2)+(135197438241/399200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5207/1024 : ℝ)) (lo := (4789/50000 : ℝ)) (hi := (8781/50000 : ℝ)) (c := (9979378462926102539/9980000000000000000 : ℝ)) (alpha := (135197438241/399200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1452628201/10000000000 : ℝ)*X 0 0+(5477961671/10000000000 : ℝ)*X 0 1+(1284032559/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336856389/2500000000 : ℝ)*X 1 0+(-1630070889/10000000000 : ℝ)*X 1 1+(2568065371/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336856269/2500000000 : ℝ)*X 2 0+(1027226163/2000000000 : ℝ)*X 2 1+(-815035717/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2059471923/5000000000 : ℝ)*X 0 0+(182714331/500000000 : ℝ)*X 0 1+(4620503041/10000000000 : ℝ)*X 0 2+(2059471923/5000000000 : ℝ)*X 1 0+(182714331/500000000 : ℝ)*X 1 1+(4620503041/10000000000 : ℝ)*X 1 2+(2059471923/5000000000 : ℝ)*X 2 0+(182714331/500000000 : ℝ)*X 2 1+(4620503041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-45399579/312500000 : ℝ)*X 0 0+(5139895639/10000000000 : ℝ)*X 0 1+(5474139951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2627984127/5000000000 : ℝ)*X 1 0+(-646031001/5000000000 : ℝ)*X 1 1+(1368534991/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((656996031/1250000000 : ℝ)*X 2 0+(5474139971/10000000000 : ℝ)*X 2 1+(-646031/5000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((823878287/2000000000 : ℝ)*X 0 0+(4609860569/10000000000 : ℝ)*X 0 1+(3665089003/10000000000 : ℝ)*X 0 2+(823878287/2000000000 : ℝ)*X 1 0+(4609860569/10000000000 : ℝ)*X 1 1+(3665089003/10000000000 : ℝ)*X 1 2+(823878287/2000000000 : ℝ)*X 2 0+(4609860569/10000000000 : ℝ)*X 2 1+(3665089003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1699_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1349539612178071545184307649/124750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (962107417/50000000000000 : ℝ)*(base19) + (1561657767/100000000000000 : ℝ)*(base23) + (26726313/50000000000000 : ℝ)*(lower2) + (49855903/10000000000000 : ℝ)*(upper3) + (25836203/50000000000000 : ℝ)*(upper5) + (495055097455499/25000000000000 : ℝ)*(major0) + (495055097455499/25000000000000 : ℝ)*(major1) + (495055097455499/25000000000000 : ℝ)*(major2) + (1462721981092767/50000000000000 : ℝ)*(sp0) + (146272967823717/5000000000000 : ℝ)*(sp1) + (1462729859515703/50000000000000 : ℝ)*(sp2) + (1034970701689353/100000000000000 : ℝ)*(sp3) + (432962591/2500000000000 : ℝ)*(sp4) + (1054583379/12500000000000 : ℝ)*(sp7) + (206995827671277/20000000000000 : ℝ)*(f.failure) + (1462730640344587/50000000000000 : ℝ)*(f.sum) + (17039788180299/4990000000000000000000000000 : ℝ)*base65 + (2614187153334113039/249500000000000000000000000000000 : ℝ)*base68 + (805334082138613039/249500000000000000000000000000000 : ℝ)*base70 + (1726082985206113039/249500000000000000000000000000000 : ℝ)*base72 + (18073811404661/4990000000000000000000000000 : ℝ)*base74 + (2134179219830613039/249500000000000000000000000000000 : ℝ)*base76 + (503958087298113039/249500000000000000000000000000000 : ℝ)*base78 + (1223245266026113039/249500000000000000000000000000000 : ℝ)*base80 + (2353823665909/4990000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (8714473/1000000000000000000000 : ℝ)*base89 + (8714473/1000000000000000000000 : ℝ)*base91 + (8714473/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1241108557150833633009809073/124750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1361480173/100000000000000 : ℝ)*(base19) + (1481799323/100000000000000 : ℝ)*(base23) + (42190401/20000000000000 : ℝ)*(upper3) + (11177603/20000000000000 : ℝ)*(lower4) + (52655559/25000000000000 : ℝ)*(upper5) + (1012569978413069/50000000000000 : ℝ)*(major0) + (1012569978413069/50000000000000 : ℝ)*(major1) + (1012569978413069/50000000000000 : ℝ)*(major2) + (12103937043/100000000000000 : ℝ)*(sp1) + (6552041327/50000000000000 : ℝ)*(sp2) + (1495911423721531/50000000000000 : ℝ)*(sp4) + (1495904691012923/50000000000000 : ℝ)*(sp5) + (1495904130780543/50000000000000 : ℝ)*(sp6) + (42338269383347/4000000000000 : ℝ)*(sp7) + (42338269383347/4000000000000 : ℝ)*(f.failure) + (1495911423721531/50000000000000 : ℝ)*(f.sum) + (21464931020591/9980000000000000000000000000 : ℝ)*base66 + (3230275363124592809/499000000000000000000000000000000 : ℝ)*base68 + (105849868169407191/499000000000000000000000000000000 : ℝ)*base69 + (2389644855400592809/499000000000000000000000000000000 : ℝ)*base72 + (13150705465251/9980000000000000000000000000 : ℝ)*base74 + (4266595460342592809/499000000000000000000000000000000 : ℝ)*base76 + (3471409610160592809/499000000000000000000000000000000 : ℝ)*base78 + (2517975267226592809/499000000000000000000000000000000 : ℝ)*base80 + (31418756645409/9980000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (465097/200000000000000000000 : ℝ)*base90 + (465097/200000000000000000000 : ℝ)*base92 + (465097/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1699_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95664749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8781/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4789/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4951/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4297/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1699_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1699_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95664749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4951/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4297/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1699_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1699_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1699_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5207/1024 : ℝ) ≤ p) (hpb : p ≤ (5215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95664749/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4951/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4297/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1699_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

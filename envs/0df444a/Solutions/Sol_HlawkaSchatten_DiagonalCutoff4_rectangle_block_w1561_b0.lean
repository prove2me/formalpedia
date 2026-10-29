-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1561_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:24:37.577991+00:00
-- url     : https://prove2.me/submissions/8b2b0de6-e3a5-46af-9962-2a336b902bbc

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
theorem support_rectangle_w1561_s0_0 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-163507483/1000000000 : ℝ)*x 0 + (5876084931/10000000000 : ℝ)*x 1 + (2437861649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (163507483/1000000000 : ℝ)^4619 ≤ (9761614411667/100000000000000 : ℝ)^3595 := by
    have hnat : (163507483 : ℕ)^4619*100000000000000^3595 ≤ 9761614411667^3595*1000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163507483 1000000000 9761614411667 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5876084931/10000000000 : ℝ)^4619 ≤ (50502757969339/100000000000000 : ℝ)^3595 := by
    have hnat : (5876084931 : ℕ)^4619*100000000000000^3595 ≤ 50502757969339^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5876084931 10000000000 50502757969339 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2437861649/5000000000 : ℝ)^4619 ≤ (39735627611643/100000000000000 : ℝ)^3595 := by
    have hnat : (2437861649 : ℕ)^4619*100000000000000^3595 ≤ 39735627611643^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2437861649 5000000000 39735627611643 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-163507483/1000000000 : ℝ), (5876084931/10000000000 : ℝ), (2437861649/5000000000 : ℝ)] ![(9761614411667/100000000000000 : ℝ), (50502757969339/100000000000000 : ℝ), (39735627611643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-163507483/1000000000 : ℝ)|^4619 ≤ (9761614411667/100000000000000 : ℝ)^3595
        have hw : |(-163507483/1000000000 : ℝ)|=(163507483/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5876084931/10000000000 : ℝ)|^4619 ≤ (50502757969339/100000000000000 : ℝ)^3595
        have hw : |(5876084931/10000000000 : ℝ)|=(5876084931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2437861649/5000000000 : ℝ)|^4619 ≤ (39735627611643/100000000000000 : ℝ)^3595
        have hw : |(2437861649/5000000000 : ℝ)|=(2437861649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s0_1 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5467401603/10000000000 : ℝ)*x 0 + (-2192363857/10000000000 : ℝ)*x 1 + (48757233/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5467401603/10000000000 : ℝ)^4619 ≤ (2301762438179/5000000000000 : ℝ)^3595 := by
    have hnat : (5467401603 : ℕ)^4619*5000000000000^3595 ≤ 2301762438179^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467401603 10000000000 2301762438179 5000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2192363857/10000000000 : ℝ)^4619 ≤ (569164943767/4000000000000 : ℝ)^3595 := by
    have hnat : (2192363857 : ℕ)^4619*4000000000000^3595 ≤ 569164943767^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192363857 10000000000 569164943767 4000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (48757233/100000000 : ℝ)^4619 ≤ (7947125526517/20000000000000 : ℝ)^3595 := by
    have hnat : (48757233 : ℕ)^4619*20000000000000^3595 ≤ 7947125526517^3595*100000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48757233 100000000 7947125526517 20000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5467401603/10000000000 : ℝ), (-2192363857/10000000000 : ℝ), (48757233/100000000 : ℝ)] ![(2301762438179/5000000000000 : ℝ), (569164943767/4000000000000 : ℝ), (7947125526517/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5467401603/10000000000 : ℝ)|^4619 ≤ (2301762438179/5000000000000 : ℝ)^3595
        have hw : |(5467401603/10000000000 : ℝ)|=(5467401603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2192363857/10000000000 : ℝ)|^4619 ≤ (569164943767/4000000000000 : ℝ)^3595
        have hw : |(-2192363857/10000000000 : ℝ)|=(2192363857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(48757233/100000000 : ℝ)|^4619 ≤ (7947125526517/20000000000000 : ℝ)^3595
        have hw : |(48757233/100000000 : ℝ)|=(48757233/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s0_2 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (341712603/625000000 : ℝ)*x 0 + (4875723247/10000000000 : ℝ)*x 1 + (-274045483/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341712603/625000000 : ℝ)^4619 ≤ (46035249250403/100000000000000 : ℝ)^3595 := by
    have hnat : (341712603 : ℕ)^4619*100000000000000^3595 ≤ 46035249250403^3595*625000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341712603 625000000 46035249250403 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4875723247/10000000000 : ℝ)^4619 ≤ (1986781353881/5000000000000 : ℝ)^3595 := by
    have hnat : (4875723247 : ℕ)^4619*5000000000000^3595 ≤ 1986781353881^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4875723247 10000000000 1986781353881 5000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274045483/1250000000 : ℝ)^4619 ≤ (3557280913137/25000000000000 : ℝ)^3595 := by
    have hnat : (274045483 : ℕ)^4619*25000000000000^3595 ≤ 3557280913137^3595*1250000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274045483 1250000000 3557280913137 25000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(341712603/625000000 : ℝ), (4875723247/10000000000 : ℝ), (-274045483/1250000000 : ℝ)] ![(46035249250403/100000000000000 : ℝ), (1986781353881/5000000000000 : ℝ), (3557280913137/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(341712603/625000000 : ℝ)|^4619 ≤ (46035249250403/100000000000000 : ℝ)^3595
        have hw : |(341712603/625000000 : ℝ)|=(341712603/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4875723247/10000000000 : ℝ)|^4619 ≤ (1986781353881/5000000000000 : ℝ)^3595
        have hw : |(4875723247/10000000000 : ℝ)|=(4875723247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-274045483/1250000000 : ℝ)|^4619 ≤ (3557280913137/25000000000000 : ℝ)^3595
        have hw : |(-274045483/1250000000 : ℝ)|=(274045483/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s0_3 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4132180523/10000000000 : ℝ)*x 0 + (618537933/2000000000 : ℝ)*x 1 + (5439634117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4132180523/10000000000 : ℝ)^4619 ≤ (257005110857/800000000000 : ℝ)^3595 := by
    have hnat : (4132180523 : ℕ)^4619*800000000000^3595 ≤ 257005110857^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132180523 10000000000 257005110857 800000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (618537933/2000000000 : ℝ)^4619 ≤ (1383705719183/6250000000000 : ℝ)^3595 := by
    have hnat : (618537933 : ℕ)^4619*6250000000000^3595 ≤ 1383705719183^3595*2000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618537933 2000000000 1383705719183 6250000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439634117/10000000000 : ℝ)^4619 ≤ (45735069615003/100000000000000 : ℝ)^3595 := by
    have hnat : (5439634117 : ℕ)^4619*100000000000000^3595 ≤ 45735069615003^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439634117 10000000000 45735069615003 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4132180523/10000000000 : ℝ), (618537933/2000000000 : ℝ), (5439634117/10000000000 : ℝ)] ![(257005110857/800000000000 : ℝ), (1383705719183/6250000000000 : ℝ), (45735069615003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4132180523/10000000000 : ℝ)|^4619 ≤ (257005110857/800000000000 : ℝ)^3595
        have hw : |(4132180523/10000000000 : ℝ)|=(4132180523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(618537933/2000000000 : ℝ)|^4619 ≤ (1383705719183/6250000000000 : ℝ)^3595
        have hw : |(618537933/2000000000 : ℝ)|=(618537933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439634117/10000000000 : ℝ)|^4619 ≤ (45735069615003/100000000000000 : ℝ)^3595
        have hw : |(5439634117/10000000000 : ℝ)|=(5439634117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s0_4 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1638198797/10000000000 : ℝ)*x 0 + (49009851/100000000 : ℝ)*x 1 + (116998521/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1638198797/10000000000 : ℝ)^4619 ≤ (4892791918599/50000000000000 : ℝ)^3595 := by
    have hnat : (1638198797 : ℕ)^4619*50000000000000^3595 ≤ 4892791918599^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1638198797 10000000000 4892791918599 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49009851/100000000 : ℝ)^4619 ≤ (40000340064653/100000000000000 : ℝ)^3595 := by
    have hnat : (49009851 : ℕ)^4619*100000000000000^3595 ≤ 40000340064653^3595*100000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49009851 100000000 40000340064653 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (116998521/200000000 : ℝ)^4619 ≤ (25107038042993/50000000000000 : ℝ)^3595 := by
    have hnat : (116998521 : ℕ)^4619*50000000000000^3595 ≤ 25107038042993^3595*200000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116998521 200000000 25107038042993 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1638198797/10000000000 : ℝ), (49009851/100000000 : ℝ), (116998521/200000000 : ℝ)] ![(4892791918599/50000000000000 : ℝ), (40000340064653/100000000000000 : ℝ), (25107038042993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1638198797/10000000000 : ℝ)|^4619 ≤ (4892791918599/50000000000000 : ℝ)^3595
        have hw : |(-1638198797/10000000000 : ℝ)|=(1638198797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(49009851/100000000 : ℝ)|^4619 ≤ (40000340064653/100000000000000 : ℝ)^3595
        have hw : |(49009851/100000000 : ℝ)|=(49009851/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(116998521/200000000 : ℝ)|^4619 ≤ (25107038042993/50000000000000 : ℝ)^3595
        have hw : |(116998521/200000000 : ℝ)|=(116998521/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s0_5 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596969553/5000000000 : ℝ)*x 0 + (-1218161981/10000000000 : ℝ)*x 1 + (116998583/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596969553/5000000000 : ℝ)^4619 ≤ (21549091535101/50000000000000 : ℝ)^3595 := by
    have hnat : (2596969553 : ℕ)^4619*50000000000000^3595 ≤ 21549091535101^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596969553 5000000000 21549091535101 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1218161981/10000000000 : ℝ)^4619 ≤ (6687706635683/100000000000000 : ℝ)^3595 := by
    have hnat : (1218161981 : ℕ)^4619*100000000000000^3595 ≤ 6687706635683^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1218161981 10000000000 6687706635683 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (116998583/200000000 : ℝ)^4619 ≤ (25107055137473/50000000000000 : ℝ)^3595 := by
    have hnat : (116998583 : ℕ)^4619*50000000000000^3595 ≤ 25107055137473^3595*200000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116998583 200000000 25107055137473 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596969553/5000000000 : ℝ), (-1218161981/10000000000 : ℝ), (116998583/200000000 : ℝ)] ![(21549091535101/50000000000000 : ℝ), (6687706635683/100000000000000 : ℝ), (25107055137473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596969553/5000000000 : ℝ)|^4619 ≤ (21549091535101/50000000000000 : ℝ)^3595
        have hw : |(2596969553/5000000000 : ℝ)|=(2596969553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1218161981/10000000000 : ℝ)|^4619 ≤ (6687706635683/100000000000000 : ℝ)^3595
        have hw : |(-1218161981/10000000000 : ℝ)|=(1218161981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(116998583/200000000 : ℝ)|^4619 ≤ (25107055137473/50000000000000 : ℝ)^3595
        have hw : |(116998583/200000000 : ℝ)|=(116998583/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s0_6 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596971191/5000000000 : ℝ)*x 0 + (2924963223/5000000000 : ℝ)*x 1 + (-609080629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596971191/5000000000 : ℝ)^4619 ≤ (21549108998353/50000000000000 : ℝ)^3595 := by
    have hnat : (2596971191 : ℕ)^4619*50000000000000^3595 ≤ 21549108998353^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596971191 5000000000 21549108998353 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2924963223/5000000000 : ℝ)^4619 ≤ (50214080453349/100000000000000 : ℝ)^3595 := by
    have hnat : (2924963223 : ℕ)^4619*100000000000000^3595 ≤ 50214080453349^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2924963223 5000000000 50214080453349 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (609080629/5000000000 : ℝ)^4619 ≤ (104495336497/1562500000000 : ℝ)^3595 := by
    have hnat : (609080629 : ℕ)^4619*1562500000000^3595 ≤ 104495336497^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609080629 5000000000 104495336497 1562500000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596971191/5000000000 : ℝ), (2924963223/5000000000 : ℝ), (-609080629/5000000000 : ℝ)] ![(21549108998353/50000000000000 : ℝ), (50214080453349/100000000000000 : ℝ), (104495336497/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596971191/5000000000 : ℝ)|^4619 ≤ (21549108998353/50000000000000 : ℝ)^3595
        have hw : |(2596971191/5000000000 : ℝ)|=(2596971191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2924963223/5000000000 : ℝ)|^4619 ≤ (50214080453349/100000000000000 : ℝ)^3595
        have hw : |(2924963223/5000000000 : ℝ)|=(2924963223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-609080629/5000000000 : ℝ)|^4619 ≤ (104495336497/1562500000000 : ℝ)^3595
        have hw : |(-609080629/5000000000 : ℝ)|=(609080629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s0_7 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1034878117/2500000000 : ℝ)*x 0 + (538036777/1000000000 : ℝ)*x 1 + (315405221/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034878117/2500000000 : ℝ)^4619 ≤ (16099448039083/50000000000000 : ℝ)^3595 := by
    have hnat : (1034878117 : ℕ)^4619*50000000000000^3595 ≤ 16099448039083^3595*2500000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034878117 2500000000 16099448039083 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538036777/1000000000 : ℝ)^4619 ≤ (5636979298457/12500000000000 : ℝ)^3595 := by
    have hnat : (538036777 : ℕ)^4619*12500000000000^3595 ≤ 5636979298457^3595*1000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538036777 1000000000 5636979298457 12500000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315405221/1000000000 : ℝ)^4619 ≤ (22705269515109/100000000000000 : ℝ)^3595 := by
    have hnat : (315405221 : ℕ)^4619*100000000000000^3595 ≤ 22705269515109^3595*1000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315405221 1000000000 22705269515109 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034878117/2500000000 : ℝ), (538036777/1000000000 : ℝ), (315405221/1000000000 : ℝ)] ![(16099448039083/50000000000000 : ℝ), (5636979298457/12500000000000 : ℝ), (22705269515109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034878117/2500000000 : ℝ)|^4619 ≤ (16099448039083/50000000000000 : ℝ)^3595
        have hw : |(1034878117/2500000000 : ℝ)|=(1034878117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538036777/1000000000 : ℝ)|^4619 ≤ (5636979298457/12500000000000 : ℝ)^3595
        have hw : |(538036777/1000000000 : ℝ)|=(538036777/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(315405221/1000000000 : ℝ)|^4619 ≤ (22705269515109/100000000000000 : ℝ)^3595
        have hw : |(315405221/1000000000 : ℝ)|=(315405221/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1561_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83652401/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3437/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4973/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4617/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4617 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4617*1^1024 ≤ 0^1024*1^4617 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4617 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4617/1024 : ℝ) ≤ (1606099479554728621/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4617 ≤ (1606099479554728621/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4617*100000000000000000000^1024 ≤ 1606099479554728621^1024*5^4617 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1606099479554728621 100000000000000000000 4617 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1606099479554728621/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4617/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4617 := by
      have hnat : (1 : ℕ)^1024*1^4617 ≤ 1^4617*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4617 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101606099479554728621/100000000000000000000 : ℝ) ≤ (10035401008249717/10000000000000000 : ℝ) ^ (4617/1024 : ℝ) := by
    have hpowers : (101606099479554728621/100000000000000000000 : ℝ)^1024 ≤ (10035401008249717/10000000000000000 : ℝ)^4617 := by
      have hnat : (101606099479554728621 : ℕ)^1024*10000000000000000^4617 ≤ 10035401008249717^4617*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101606099479554728621 100000000000000000000 10035401008249717 10000000000000000 1024 4617 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10035401008249717/10000000000000000 : ℝ)) (X := (101606099479554728621/100000000000000000000 : ℝ)) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51606099479554728621/50000000000000000000 : ℝ) ≤ (5035401008249717/5000000000000000 : ℝ) ^ (4617/1024 : ℝ) := by
    have hpowers : (51606099479554728621/50000000000000000000 : ℝ)^1024 ≤ (5035401008249717/5000000000000000 : ℝ)^4617 := by
      have hnat : (51606099479554728621 : ℕ)^1024*5000000000000000^4617 ≤ 5035401008249717^4617*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51606099479554728621 50000000000000000000 5035401008249717 5000000000000000 1024 4617 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5035401008249717/5000000000000000 : ℝ)) (X := (51606099479554728621/50000000000000000000 : ℝ)) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(35401008249717/4000000000000000 : ℝ)*(0 : ℝ))^(4617/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(35401008249717/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1606099479554728621/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(35401008249717/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4617/1024 : ℝ) := by
    rw [show (1 : ℝ)+(35401008249717/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10035401008249717/10000000000000000 : ℝ) by norm_num, show 1+(1606099479554728621/100000000000000000000 : ℝ)+(0 : ℝ)=(101606099479554728621/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1606099479554728621/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(35401008249717/4000000000000000 : ℝ)*(2/5 : ℝ))^(4617/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(35401008249717/4000000000000000 : ℝ)*(2/5 : ℝ)=(5035401008249717/5000000000000000 : ℝ) by norm_num, show 1+2*(1606099479554728621/100000000000000000000 : ℝ)=(51606099479554728621/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(35401008249717/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4617/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35401008249717/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(35401008249717/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4617/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35401008249717/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(35401008249717/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4617/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35401008249717/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-163507483/1000000000 : ℝ)*X 0 0+(5876084931/10000000000 : ℝ)*X 0 1+(2437861649/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5467401603/10000000000 : ℝ)*X 1 0+(-2192363857/10000000000 : ℝ)*X 1 1+(48757233/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((341712603/625000000 : ℝ)*X 2 0+(4875723247/10000000000 : ℝ)*X 2 1+(-274045483/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4132180523/10000000000 : ℝ)*X 0 0+(618537933/2000000000 : ℝ)*X 0 1+(5439634117/10000000000 : ℝ)*X 0 2+(4132180523/10000000000 : ℝ)*X 1 0+(618537933/2000000000 : ℝ)*X 1 1+(5439634117/10000000000 : ℝ)*X 1 2+(4132180523/10000000000 : ℝ)*X 2 0+(618537933/2000000000 : ℝ)*X 2 1+(5439634117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1638198797/10000000000 : ℝ)*X 0 0+(49009851/100000000 : ℝ)*X 0 1+(116998521/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2596969553/5000000000 : ℝ)*X 1 0+(-1218161981/10000000000 : ℝ)*X 1 1+(116998583/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2596971191/5000000000 : ℝ)*X 2 0+(2924963223/5000000000 : ℝ)*X 2 1+(-609080629/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1034878117/2500000000 : ℝ)*X 0 0+(538036777/1000000000 : ℝ)*X 0 1+(315405221/1000000000 : ℝ)*X 0 2+(1034878117/2500000000 : ℝ)*X 1 0+(538036777/1000000000 : ℝ)*X 1 1+(315405221/1000000000 : ℝ)*X 1 2+(1034878117/2500000000 : ℝ)*X 2 0+(538036777/1000000000 : ℝ)*X 2 1+(315405221/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1051016808454003328374653/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50065587/100000000000000 : ℝ)*(base1) + (219284607/20000000000000 : ℝ)*(base19) + (276162679/25000000000000 : ℝ)*(base23) + (142093467/100000000000000 : ℝ)*(upper3) + (142130179/100000000000000 : ℝ)*(upper5) + (712867933647203/100000000000000 : ℝ)*(major0) + (712867933647203/100000000000000 : ℝ)*(major1) + (712867933647203/100000000000000 : ℝ)*(major2) + (249910584480987/25000000000000 : ℝ)*(sp0) + (999645251507701/100000000000000 : ℝ)*(sp1) + (49982262164001/5000000000000 : ℝ)*(sp2) + (13315236352743/3125000000000 : ℝ)*(sp3) + (32480579/800000000000 : ℝ)*(sp4) + (432710209/25000000000000 : ℝ)*(sp7) + (426089344194199/100000000000000 : ℝ)*(f.failure) + (62477896745671/6250000000000 : ℝ)*(f.sum) + (86413526391551/200000000000000000000000000000 : ℝ)*base65 + (2549125136608449/400000000000000000000000000000 : ℝ)*base68 + (1513842960191551/400000000000000000000000000000 : ℝ)*base69 + (1132022717008449/400000000000000000000000000000 : ℝ)*base72 + (423778398008449/200000000000000000000000000000 : ℝ)*base74 + (198766658208449/400000000000000000000000000000 : ℝ)*base76 + (995714019808449/400000000000000000000000000000 : ℝ)*base78 + (1981599077408449/400000000000000000000000000000 : ℝ)*base80 + (888066388191551/200000000000000000000000000000 : ℝ)*base81 + (6621799/5000000000000000000000 : ℝ)*base89 + (6621799/5000000000000000000000 : ℝ)*base91 + (6621799/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (171146836279164426272217/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (997890703/100000000000000 : ℝ)*(base19) + (225485257/12500000000000 : ℝ)*(base23) + (11339157/3125000000000 : ℝ)*(base32) + (642558317/100000000000000 : ℝ)*(upper3) + (18012681/12500000000000 : ℝ)*(upper5) + (751488339164167/100000000000000 : ℝ)*(major0) + (751488339164167/100000000000000 : ℝ)*(major1) + (751488339164167/100000000000000 : ℝ)*(major2) + (504269339/50000000000000 : ℝ)*(sp1) + (1846369519/50000000000000 : ℝ)*(sp2) + (526901665980023/50000000000000 : ℝ)*(sp4) + (210760265106133/20000000000000 : ℝ)*(sp5) + (1053797835338951/100000000000000 : ℝ)*(sp6) + (14036651277903/3125000000000 : ℝ)*(sp7) + (701833130853/156250000000 : ℝ)*(f.failure) + (526901665980023/50000000000000 : ℝ)*(f.sum) + (44201138909261/200000000000000000000000000000 : ℝ)*base66 + (1957799213709261/400000000000000000000000000000 : ℝ)*base68 + (1459807989709261/400000000000000000000000000000 : ℝ)*base70 + (1267134066509261/400000000000000000000000000000 : ℝ)*base72 + (971919307509261/200000000000000000000000000000 : ℝ)*base74 + (269241529709261/400000000000000000000000000000 : ℝ)*base76 + (733238100690739/400000000000000000000000000000 : ℝ)*base77 + (465199186509261/400000000000000000000000000000 : ℝ)*base80 + (697571999709261/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (40589/3906250000000000000 : ℝ)*base89 + (40589/3906250000000000000 : ℝ)*base91 + (40589/3906250000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1561_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83652401/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3437/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4973/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1561_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1561_s1_0 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1775963179/10000000000 : ℝ)*x 0 + (44320061/80000000 : ℝ)*x 1 + (51210339/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1775963179/10000000000 : ℝ)^4619 ≤ (434212853569/4000000000000 : ℝ)^3595 := by
    have hnat : (1775963179 : ℕ)^4619*4000000000000^3595 ≤ 434212853569^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1775963179 10000000000 434212853569 4000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44320061/80000000 : ℝ)^4619 ≤ (46822202602041/100000000000000 : ℝ)^3595 := by
    have hnat : (44320061 : ℕ)^4619*100000000000000^3595 ≤ 46822202602041^3595*80000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44320061 80000000 46822202602041 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51210339/100000000 : ℝ)^4619 ≤ (10580619011179/25000000000000 : ℝ)^3595 := by
    have hnat : (51210339 : ℕ)^4619*25000000000000^3595 ≤ 10580619011179^3595*100000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51210339 100000000 10580619011179 25000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1775963179/10000000000 : ℝ), (44320061/80000000 : ℝ), (51210339/100000000 : ℝ)] ![(434212853569/4000000000000 : ℝ), (46822202602041/100000000000000 : ℝ), (10580619011179/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1775963179/10000000000 : ℝ)|^4619 ≤ (434212853569/4000000000000 : ℝ)^3595
        have hw : |(-1775963179/10000000000 : ℝ)|=(1775963179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(44320061/80000000 : ℝ)|^4619 ≤ (46822202602041/100000000000000 : ℝ)^3595
        have hw : |(44320061/80000000 : ℝ)|=(44320061/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(51210339/100000000 : ℝ)|^4619 ≤ (10580619011179/25000000000000 : ℝ)^3595
        have hw : |(51210339/100000000 : ℝ)|=(51210339/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s1_1 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377968661/10000000000 : ℝ)*x 0 + (-997663069/5000000000 : ℝ)*x 1 + (1024206773/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377968661/10000000000 : ℝ)^4619 ≤ (22535000066741/50000000000000 : ℝ)^3595 := by
    have hnat : (5377968661 : ℕ)^4619*50000000000000^3595 ≤ 22535000066741^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377968661 10000000000 22535000066741 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (997663069/5000000000 : ℝ)^4619 ≤ (12607524176471/100000000000000 : ℝ)^3595 := by
    have hnat : (997663069 : ℕ)^4619*100000000000000^3595 ≤ 12607524176471^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997663069 5000000000 12607524176471 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1024206773/2000000000 : ℝ)^4619 ≤ (42322475673069/100000000000000 : ℝ)^3595 := by
    have hnat : (1024206773 : ℕ)^4619*100000000000000^3595 ≤ 42322475673069^3595*2000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024206773 2000000000 42322475673069 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377968661/10000000000 : ℝ), (-997663069/5000000000 : ℝ), (1024206773/2000000000 : ℝ)] ![(22535000066741/50000000000000 : ℝ), (12607524176471/100000000000000 : ℝ), (42322475673069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377968661/10000000000 : ℝ)|^4619 ≤ (22535000066741/50000000000000 : ℝ)^3595
        have hw : |(5377968661/10000000000 : ℝ)|=(5377968661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-997663069/5000000000 : ℝ)|^4619 ≤ (12607524176471/100000000000000 : ℝ)^3595
        have hw : |(-997663069/5000000000 : ℝ)|=(997663069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1024206773/2000000000 : ℝ)|^4619 ≤ (42322475673069/100000000000000 : ℝ)^3595
        have hw : |(1024206773/2000000000 : ℝ)|=(1024206773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s1_2 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688984299/5000000000 : ℝ)*x 0 + (1024206849/2000000000 : ℝ)*x 1 + (-79813029/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688984299/5000000000 : ℝ)^4619 ≤ (11267499863781/25000000000000 : ℝ)^3595 := by
    have hnat : (2688984299 : ℕ)^4619*25000000000000^3595 ≤ 11267499863781^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688984299 5000000000 11267499863781 25000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024206849/2000000000 : ℝ)^4619 ≤ (42322479708093/100000000000000 : ℝ)^3595 := by
    have hnat : (1024206849 : ℕ)^4619*100000000000000^3595 ≤ 42322479708093^3595*2000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024206849 2000000000 42322479708093 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79813029/400000000 : ℝ)^4619 ≤ (6303760411807/50000000000000 : ℝ)^3595 := by
    have hnat : (79813029 : ℕ)^4619*50000000000000^3595 ≤ 6303760411807^3595*400000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79813029 400000000 6303760411807 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688984299/5000000000 : ℝ), (1024206849/2000000000 : ℝ), (-79813029/400000000 : ℝ)] ![(11267499863781/25000000000000 : ℝ), (42322479708093/100000000000000 : ℝ), (6303760411807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688984299/5000000000 : ℝ)|^4619 ≤ (11267499863781/25000000000000 : ℝ)^3595
        have hw : |(2688984299/5000000000 : ℝ)|=(2688984299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1024206849/2000000000 : ℝ)|^4619 ≤ (42322479708093/100000000000000 : ℝ)^3595
        have hw : |(1024206849/2000000000 : ℝ)|=(1024206849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-79813029/400000000 : ℝ)|^4619 ≤ (6303760411807/50000000000000 : ℝ)^3595
        have hw : |(-79813029/400000000 : ℝ)|=(79813029/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s1_3 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (846347373/2000000000 : ℝ)*x 0 + (1881715093/5000000000 : ℝ)*x 1 + (474638361/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (846347373/2000000000 : ℝ)^4619 ≤ (33123499038951/100000000000000 : ℝ)^3595 := by
    have hnat : (846347373 : ℕ)^4619*100000000000000^3595 ≤ 33123499038951^3595*2000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846347373 2000000000 33123499038951 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1881715093/5000000000 : ℝ)^4619 ≤ (1139601834149/4000000000000 : ℝ)^3595 := by
    have hnat : (1881715093 : ℕ)^4619*4000000000000^3595 ≤ 1139601834149^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1881715093 5000000000 1139601834149 4000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (474638361/1000000000 : ℝ)^4619 ≤ (38386455087981/100000000000000 : ℝ)^3595 := by
    have hnat : (474638361 : ℕ)^4619*100000000000000^3595 ≤ 38386455087981^3595*1000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474638361 1000000000 38386455087981 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(846347373/2000000000 : ℝ), (1881715093/5000000000 : ℝ), (474638361/1000000000 : ℝ)] ![(33123499038951/100000000000000 : ℝ), (1139601834149/4000000000000 : ℝ), (38386455087981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(846347373/2000000000 : ℝ)|^4619 ≤ (33123499038951/100000000000000 : ℝ)^3595
        have hw : |(846347373/2000000000 : ℝ)|=(846347373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1881715093/5000000000 : ℝ)|^4619 ≤ (1139601834149/4000000000000 : ℝ)^3595
        have hw : |(1881715093/5000000000 : ℝ)|=(1881715093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(474638361/1000000000 : ℝ)|^4619 ≤ (38386455087981/100000000000000 : ℝ)^3595
        have hw : |(474638361/1000000000 : ℝ)|=(474638361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s1_4 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-222023281/1250000000 : ℝ)*x 0 + (1025082019/2000000000 : ℝ)*x 1 + (691945751/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (222023281/1250000000 : ℝ)^4619 ≤ (5428536610477/50000000000000 : ℝ)^3595 := by
    have hnat : (222023281 : ℕ)^4619*50000000000000^3595 ≤ 5428536610477^3595*1250000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222023281 1250000000 5428536610477 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025082019/2000000000 : ℝ)^4619 ≤ (8473790050433/20000000000000 : ℝ)^3595 := by
    have hnat : (1025082019 : ℕ)^4619*20000000000000^3595 ≤ 8473790050433^3595*2000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025082019 2000000000 8473790050433 20000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (691945751/1250000000 : ℝ)^4619 ≤ (11693494128069/25000000000000 : ℝ)^3595 := by
    have hnat : (691945751 : ℕ)^4619*25000000000000^3595 ≤ 11693494128069^3595*1250000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691945751 1250000000 11693494128069 25000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-222023281/1250000000 : ℝ), (1025082019/2000000000 : ℝ), (691945751/1250000000 : ℝ)] ![(5428536610477/50000000000000 : ℝ), (8473790050433/20000000000000 : ℝ), (11693494128069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-222023281/1250000000 : ℝ)|^4619 ≤ (5428536610477/50000000000000 : ℝ)^3595
        have hw : |(-222023281/1250000000 : ℝ)|=(222023281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1025082019/2000000000 : ℝ)|^4619 ≤ (8473790050433/20000000000000 : ℝ)^3595
        have hw : |(1025082019/2000000000 : ℝ)|=(1025082019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(691945751/1250000000 : ℝ)|^4619 ≤ (11693494128069/25000000000000 : ℝ)^3595
        have hw : |(691945751/1250000000 : ℝ)|=(691945751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s1_5 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526701199/1000000000 : ℝ)*x 0 + (-1580793811/10000000000 : ℝ)*x 1 + (5535566341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526701199/1000000000 : ℝ)^4619 ≤ (8775758520101/20000000000000 : ℝ)^3595 := by
    have hnat : (526701199 : ℕ)^4619*20000000000000^3595 ≤ 8775758520101^3595*1000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526701199 1000000000 8775758520101 20000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1580793811/10000000000 : ℝ)^4619 ≤ (1869445452609/20000000000000 : ℝ)^3595 := by
    have hnat : (1580793811 : ℕ)^4619*20000000000000^3595 ≤ 1869445452609^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1580793811 10000000000 1869445452609 20000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5535566341/10000000000 : ℝ)^4619 ≤ (46773980127503/100000000000000 : ℝ)^3595 := by
    have hnat : (5535566341 : ℕ)^4619*100000000000000^3595 ≤ 46773980127503^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5535566341 10000000000 46773980127503 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526701199/1000000000 : ℝ), (-1580793811/10000000000 : ℝ), (5535566341/10000000000 : ℝ)] ![(8775758520101/20000000000000 : ℝ), (1869445452609/20000000000000 : ℝ), (46773980127503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526701199/1000000000 : ℝ)|^4619 ≤ (8775758520101/20000000000000 : ℝ)^3595
        have hw : |(526701199/1000000000 : ℝ)|=(526701199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1580793811/10000000000 : ℝ)|^4619 ≤ (1869445452609/20000000000000 : ℝ)^3595
        have hw : |(-1580793811/10000000000 : ℝ)|=(1580793811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5535566341/10000000000 : ℝ)|^4619 ≤ (46773980127503/100000000000000 : ℝ)^3595
        have hw : |(5535566341/10000000000 : ℝ)|=(5535566341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s1_6 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5267011639/10000000000 : ℝ)*x 0 + (5535566463/10000000000 : ℝ)*x 1 + (-1580794131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5267011639/10000000000 : ℝ)^4619 ≤ (43878788843459/100000000000000 : ℝ)^3595 := by
    have hnat : (5267011639 : ℕ)^4619*100000000000000^3595 ≤ 43878788843459^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267011639 10000000000 43878788843459 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5535566463/10000000000 : ℝ)^4619 ≤ (46773981452001/100000000000000 : ℝ)^3595 := by
    have hnat : (5535566463 : ℕ)^4619*100000000000000^3595 ≤ 46773981452001^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5535566463 10000000000 46773981452001 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1580794131/10000000000 : ℝ)^4619 ≤ (9347229694167/100000000000000 : ℝ)^3595 := by
    have hnat : (1580794131 : ℕ)^4619*100000000000000^3595 ≤ 9347229694167^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1580794131 10000000000 9347229694167 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5267011639/10000000000 : ℝ), (5535566463/10000000000 : ℝ), (-1580794131/10000000000 : ℝ)] ![(43878788843459/100000000000000 : ℝ), (46773981452001/100000000000000 : ℝ), (9347229694167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5267011639/10000000000 : ℝ)|^4619 ≤ (43878788843459/100000000000000 : ℝ)^3595
        have hw : |(5267011639/10000000000 : ℝ)|=(5267011639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5535566463/10000000000 : ℝ)|^4619 ≤ (46773981452001/100000000000000 : ℝ)^3595
        have hw : |(5535566463/10000000000 : ℝ)|=(5535566463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1580794131/10000000000 : ℝ)|^4619 ≤ (9347229694167/100000000000000 : ℝ)^3595
        have hw : |(-1580794131/10000000000 : ℝ)|=(1580794131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s1_7 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2116129589/5000000000 : ℝ)*x 0 + (4736117033/10000000000 : ℝ)*x 1 + (1886925369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116129589/5000000000 : ℝ)^4619 ≤ (8282188002749/25000000000000 : ℝ)^3595 := by
    have hnat : (2116129589 : ℕ)^4619*25000000000000^3595 ≤ 8282188002749^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116129589 5000000000 8282188002749 25000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4736117033/10000000000 : ℝ)^4619 ≤ (1913990313697/5000000000000 : ℝ)^3595 := by
    have hnat : (4736117033 : ℕ)^4619*5000000000000^3595 ≤ 1913990313697^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4736117033 10000000000 1913990313697 5000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1886925369/5000000000 : ℝ)^4619 ≤ (7147860426659/25000000000000 : ℝ)^3595 := by
    have hnat : (1886925369 : ℕ)^4619*25000000000000^3595 ≤ 7147860426659^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886925369 5000000000 7147860426659 25000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2116129589/5000000000 : ℝ), (4736117033/10000000000 : ℝ), (1886925369/5000000000 : ℝ)] ![(8282188002749/25000000000000 : ℝ), (1913990313697/5000000000000 : ℝ), (7147860426659/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2116129589/5000000000 : ℝ)|^4619 ≤ (8282188002749/25000000000000 : ℝ)^3595
        have hw : |(2116129589/5000000000 : ℝ)|=(2116129589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4736117033/10000000000 : ℝ)|^4619 ≤ (1913990313697/5000000000000 : ℝ)^3595
        have hw : |(4736117033/10000000000 : ℝ)|=(4736117033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1886925369/5000000000 : ℝ)|^4619 ≤ (7147860426659/25000000000000 : ℝ)^3595
        have hw : |(1886925369/5000000000 : ℝ)|=(1886925369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1561_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83652401/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4973/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3437/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8967/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8919/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4973/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3437/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4973/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3437/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4973/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3437/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4973/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3437/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4973/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3437/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4973/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3437/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3437/100000 : ℝ) ^ (4617/1024 : ℝ) ≤ (3139440800029/12500000000000000000 : ℝ) := by
    have hpowers : (3437/100000 : ℝ)^4617 ≤ (3139440800029/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3437 : ℕ)^4617*12500000000000000000^1024 ≤ 3139440800029^1024*100000^4617 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3437 100000 3139440800029 12500000000000000000 4617 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3437/100000 : ℝ)) (X := (3139440800029/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4973/20000 : ℝ) ^ (4617/1024 : ℝ) ≤ (37658747441034009/20000000000000000000 : ℝ) := by
    have hpowers : (4973/20000 : ℝ)^4617 ≤ (37658747441034009/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4973 : ℕ)^4617*20000000000000000000^1024 ≤ 37658747441034009^1024*20000^4617 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4973 20000 37658747441034009 20000000000000000000 4617 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4973/20000 : ℝ)) (X := (37658747441034009/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250003139440800029/6250000000000000000 : ℝ) ≤ (10000001114069483/10000000000000000 : ℝ) ^ (4617/1024 : ℝ) := by
    have hpowers : (6250003139440800029/6250000000000000000 : ℝ)^1024 ≤ (10000001114069483/10000000000000000 : ℝ)^4617 := by
      have hnat : (6250003139440800029 : ℕ)^1024*10000000000000000^4617 ≤ 10000001114069483^4617*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250003139440800029 6250000000000000000 10000001114069483 10000000000000000 1024 4617 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001114069483/10000000000000000 : ℝ)) (X := (6250003139440800029/6250000000000000000 : ℝ)) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100188318852731570277/100000000000000000000 : ℝ) ≤ (10004173648658747/10000000000000000 : ℝ) ^ (4617/1024 : ℝ) := by
    have hpowers : (100188318852731570277/100000000000000000000 : ℝ)^1024 ≤ (10004173648658747/10000000000000000 : ℝ)^4617 := by
      have hnat : (100188318852731570277 : ℕ)^1024*10000000000000000^4617 ≤ 10004173648658747^4617*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100188318852731570277 100000000000000000000 10004173648658747 10000000000000000 1024 4617 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004173648658747/10000000000000000 : ℝ)) (X := (100188318852731570277/100000000000000000000 : ℝ)) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10037658747441034009/10000000000000000000 : ℝ) ≤ (10008346183248011/10000000000000000 : ℝ) ^ (4617/1024 : ℝ) := by
    have hpowers : (10037658747441034009/10000000000000000000 : ℝ)^1024 ≤ (10008346183248011/10000000000000000 : ℝ)^4617 := by
      have hnat : (10037658747441034009 : ℕ)^1024*10000000000000000^4617 ≤ 10008346183248011^4617*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10037658747441034009 10000000000000000000 10008346183248011 10000000000000000 1024 4617 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008346183248011/10000000000000000 : ℝ)) (X := (10037658747441034009/10000000000000000000 : ℝ)) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3139440800029/12500000000000000000 : ℝ) ≤ ((53562835467378570247/53570000000000000000 : ℝ)+2*(260783411829/133925000000000 : ℝ)*(3437/100000 : ℝ))^(4617/1024 : ℝ) := by
    rw [show (53562835467378570247/53570000000000000000 : ℝ)+2*(260783411829/133925000000000 : ℝ)*(3437/100000 : ℝ)=(10000001114069483/10000000000000000 : ℝ) by norm_num, show 1+2*(3139440800029/12500000000000000000 : ℝ)=(6250003139440800029/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37658747441034009/20000000000000000000 : ℝ)+(3139440800029/12500000000000000000 : ℝ) ≤ ((53562835467378570247/53570000000000000000 : ℝ)+(260783411829/133925000000000 : ℝ)*((4973/20000 : ℝ)+(3437/100000 : ℝ)))^(4617/1024 : ℝ) := by
    rw [show (53562835467378570247/53570000000000000000 : ℝ)+(260783411829/133925000000000 : ℝ)*((4973/20000 : ℝ)+(3437/100000 : ℝ))=(10004173648658747/10000000000000000 : ℝ) by norm_num, show 1+(37658747441034009/20000000000000000000 : ℝ)+(3139440800029/12500000000000000000 : ℝ)=(100188318852731570277/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37658747441034009/20000000000000000000 : ℝ) ≤ ((53562835467378570247/53570000000000000000 : ℝ)+2*(260783411829/133925000000000 : ℝ)*(4973/20000 : ℝ))^(4617/1024 : ℝ) := by
    rw [show (53562835467378570247/53570000000000000000 : ℝ)+2*(260783411829/133925000000000 : ℝ)*(4973/20000 : ℝ)=(10008346183248011/10000000000000000 : ℝ) by norm_num, show 1+2*(37658747441034009/20000000000000000000 : ℝ)=(10037658747441034009/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (53562835467378570247/53570000000000000000 : ℝ)*(X 1 0+X 2 0)+(260783411829/133925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4617/1024 : ℝ)) (lo := (3437/100000 : ℝ)) (hi := (4973/20000 : ℝ)) (c := (53562835467378570247/53570000000000000000 : ℝ)) (alpha := (260783411829/133925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (53562835467378570247/53570000000000000000 : ℝ)*(X 0 1+X 2 1)+(260783411829/133925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4617/1024 : ℝ)) (lo := (3437/100000 : ℝ)) (hi := (4973/20000 : ℝ)) (c := (53562835467378570247/53570000000000000000 : ℝ)) (alpha := (260783411829/133925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (53562835467378570247/53570000000000000000 : ℝ)*(X 0 2+X 1 2)+(260783411829/133925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4617/1024 : ℝ)) (lo := (3437/100000 : ℝ)) (hi := (4973/20000 : ℝ)) (c := (53562835467378570247/53570000000000000000 : ℝ)) (alpha := (260783411829/133925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1775963179/10000000000 : ℝ)*X 0 0+(44320061/80000000 : ℝ)*X 0 1+(51210339/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5377968661/10000000000 : ℝ)*X 1 0+(-997663069/5000000000 : ℝ)*X 1 1+(1024206773/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2688984299/5000000000 : ℝ)*X 2 0+(1024206849/2000000000 : ℝ)*X 2 1+(-79813029/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((846347373/2000000000 : ℝ)*X 0 0+(1881715093/5000000000 : ℝ)*X 0 1+(474638361/1000000000 : ℝ)*X 0 2+(846347373/2000000000 : ℝ)*X 1 0+(1881715093/5000000000 : ℝ)*X 1 1+(474638361/1000000000 : ℝ)*X 1 2+(846347373/2000000000 : ℝ)*X 2 0+(1881715093/5000000000 : ℝ)*X 2 1+(474638361/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-222023281/1250000000 : ℝ)*X 0 0+(1025082019/2000000000 : ℝ)*X 0 1+(691945751/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((526701199/1000000000 : ℝ)*X 1 0+(-1580793811/10000000000 : ℝ)*X 1 1+(5535566341/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5267011639/10000000000 : ℝ)*X 2 0+(5535566463/10000000000 : ℝ)*X 2 1+(-1580794131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2116129589/5000000000 : ℝ)*X 0 0+(4736117033/10000000000 : ℝ)*X 0 1+(1886925369/5000000000 : ℝ)*X 0 2+(2116129589/5000000000 : ℝ)*X 1 0+(4736117033/10000000000 : ℝ)*X 1 1+(1886925369/5000000000 : ℝ)*X 1 2+(2116129589/5000000000 : ℝ)*X 2 0+(4736117033/10000000000 : ℝ)*X 2 1+(1886925369/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1283515678168032829953657627/334812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4756313/5000000000000 : ℝ)*(base1) + (987703647/100000000000000 : ℝ)*(base19) + (60000189/6250000000000 : ℝ)*(base23) + (225179281/100000000000000 : ℝ)*(upper5) + (212759470400551/12500000000000 : ℝ)*(major0) + (212759470400551/12500000000000 : ℝ)*(major1) + (212759470400551/12500000000000 : ℝ)*(major2) + (1193395508783583/50000000000000 : ℝ)*(sp0) + (149175011445921/6250000000000 : ℝ)*(sp1) + (18646876745397/781250000000 : ℝ)*(sp2) + (1017346800451721/100000000000000 : ℝ)*(sp3) + (5130486467/50000000000000 : ℝ)*(sp4) + (12575457/100000000000000 : ℝ)*(sp5) + (207477029/6250000000000 : ℝ)*(sp7) + (254337553802611/25000000000000 : ℝ)*(f.failure) + (29835014792673/1250000000000 : ℝ)*(f.sum) + (44152505292207/26785000000000000000000000000 : ℝ)*base66 + (400931815483577827/60875000000000000000000000000000 : ℝ)*base67 + (45513906209577827/60875000000000000000000000000000 : ℝ)*base69 + (207704321134202827/60875000000000000000000000000000 : ℝ)*base71 + (39635626940873/26785000000000000000000000000 : ℝ)*base73 + (268658973880202827/60875000000000000000000000000000 : ℝ)*base75 + (259185210327452827/60875000000000000000000000000000 : ℝ)*base77 + (376314912698577827/60875000000000000000000000000000 : ℝ)*base79 + (29911571346021/13392500000000000000000000000 : ℝ)*base82 + (9780989/1250000000000000000000 : ℝ)*base90 + (9780989/1250000000000000000000 : ℝ)*base92 + (9780989/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101434090440073313854401/26785000000000000000000000000 : ℝ) := by norm_num
    linear_combination (654388193/100000000000000 : ℝ)*(base19) + (71821317/12500000000000 : ℝ)*(base23) + (49188751/100000000000000 : ℝ)*(upper2) + (36118001/25000000000000 : ℝ)*(upper3) + (55930429/100000000000000 : ℝ)*(upper5) + (1738654203017683/100000000000000 : ℝ)*(major0) + (1738654203017683/100000000000000 : ℝ)*(major1) + (1738654203017683/100000000000000 : ℝ)*(major2) + (5521010553/100000000000000 : ℝ)*(sp1) + (1252909071/25000000000000 : ℝ)*(sp2) + (1219047355686831/50000000000000 : ℝ)*(sp4) + (609522133993729/25000000000000 : ℝ)*(sp5) + (1219044562583421/50000000000000 : ℝ)*(sp6) + (207842713685849/20000000000000 : ℝ)*(sp7) + (207842713685849/20000000000000 : ℝ)*(f.failure) + (1219047355686831/50000000000000 : ℝ)*(f.sum) + (29524214882069/13392500000000000000000000000 : ℝ)*base65 + (1080035809109679791/487000000000000000000000000000000 : ℝ)*base67 + (315202696687320209/487000000000000000000000000000000 : ℝ)*base70 + (705371939786320209/487000000000000000000000000000000 : ℝ)*base72 + (56370185266253/26785000000000000000000000000 : ℝ)*base73 + (68748880077679791/487000000000000000000000000000000 : ℝ)*base75 + (1931849211174679791/487000000000000000000000000000000 : ℝ)*base77 + (1438459140922320209/487000000000000000000000000000000 : ℝ)*base80 + (12993595516613/6696250000000000000000000000 : ℝ)*base82 + (1426551/1000000000000000000000 : ℝ)*base90 + (1426551/1000000000000000000000 : ℝ)*base92 + (1426551/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1561_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83652401/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4973/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3437/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8967/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8919/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1561_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1561_s2_0 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-897693421/5000000000 : ℝ)*x 0 + (340234659/625000000 : ℝ)*x 1 + (5204641107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (897693421/5000000000 : ℝ)^4619 ≤ (5504050075111/50000000000000 : ℝ)^3595 := by
    have hnat : (897693421 : ℕ)^4619*50000000000000^3595 ≤ 5504050075111^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897693421 5000000000 5504050075111 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340234659/625000000 : ℝ)^4619 ≤ (22889792892301/50000000000000 : ℝ)^3595 := by
    have hnat : (340234659 : ℕ)^4619*50000000000000^3595 ≤ 22889792892301^3595*625000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340234659 625000000 22889792892301 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5204641107/10000000000 : ℝ)^4619 ≤ (21606157022511/50000000000000 : ℝ)^3595 := by
    have hnat : (5204641107 : ℕ)^4619*50000000000000^3595 ≤ 21606157022511^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204641107 10000000000 21606157022511 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-897693421/5000000000 : ℝ), (340234659/625000000 : ℝ), (5204641107/10000000000 : ℝ)] ![(5504050075111/50000000000000 : ℝ), (22889792892301/50000000000000 : ℝ), (21606157022511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-897693421/5000000000 : ℝ)|^4619 ≤ (5504050075111/50000000000000 : ℝ)^3595
        have hw : |(-897693421/5000000000 : ℝ)|=(897693421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340234659/625000000 : ℝ)|^4619 ≤ (22889792892301/50000000000000 : ℝ)^3595
        have hw : |(340234659/625000000 : ℝ)|=(340234659/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5204641107/10000000000 : ℝ)|^4619 ≤ (21606157022511/50000000000000 : ℝ)^3595
        have hw : |(5204641107/10000000000 : ℝ)|=(5204641107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s2_1 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669145789/1250000000 : ℝ)*x 0 + (-959081337/5000000000 : ℝ)*x 1 + (5204641191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669145789/1250000000 : ℝ)^4619 ≤ (8960622861061/20000000000000 : ℝ)^3595 := by
    have hnat : (669145789 : ℕ)^4619*20000000000000^3595 ≤ 8960622861061^3595*1250000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669145789 1250000000 8960622861061 20000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (959081337/5000000000 : ℝ)^4619 ≤ (5992285371273/50000000000000 : ℝ)^3595 := by
    have hnat : (959081337 : ℕ)^4619*50000000000000^3595 ≤ 5992285371273^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959081337 5000000000 5992285371273 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5204641191/10000000000 : ℝ)^4619 ≤ (43212314941099/100000000000000 : ℝ)^3595 := by
    have hnat : (5204641191 : ℕ)^4619*100000000000000^3595 ≤ 43212314941099^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204641191 10000000000 43212314941099 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669145789/1250000000 : ℝ), (-959081337/5000000000 : ℝ), (5204641191/10000000000 : ℝ)] ![(8960622861061/20000000000000 : ℝ), (5992285371273/50000000000000 : ℝ), (43212314941099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669145789/1250000000 : ℝ)|^4619 ≤ (8960622861061/20000000000000 : ℝ)^3595
        have hw : |(669145789/1250000000 : ℝ)|=(669145789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-959081337/5000000000 : ℝ)|^4619 ≤ (5992285371273/50000000000000 : ℝ)^3595
        have hw : |(-959081337/5000000000 : ℝ)|=(959081337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5204641191/10000000000 : ℝ)|^4619 ≤ (43212314941099/100000000000000 : ℝ)^3595
        have hw : |(5204641191/10000000000 : ℝ)|=(5204641191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s2_2 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338291511/2500000000 : ℝ)*x 0 + (2602320717/5000000000 : ℝ)*x 1 + (-1918162709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338291511/2500000000 : ℝ)^4619 ≤ (44803111423389/100000000000000 : ℝ)^3595 := by
    have hnat : (1338291511 : ℕ)^4619*100000000000000^3595 ≤ 44803111423389^3595*2500000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338291511 2500000000 44803111423389 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2602320717/5000000000 : ℝ)^4619 ≤ (1080307938333/2500000000000 : ℝ)^3595 := by
    have hnat : (2602320717 : ℕ)^4619*2500000000000^3595 ≤ 1080307938333^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602320717 5000000000 1080307938333 2500000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1918162709/10000000000 : ℝ)^4619 ≤ (1498071377939/12500000000000 : ℝ)^3595 := by
    have hnat : (1918162709 : ℕ)^4619*12500000000000^3595 ≤ 1498071377939^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918162709 10000000000 1498071377939 12500000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338291511/2500000000 : ℝ), (2602320717/5000000000 : ℝ), (-1918162709/10000000000 : ℝ)] ![(44803111423389/100000000000000 : ℝ), (1080307938333/2500000000000 : ℝ), (1498071377939/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338291511/2500000000 : ℝ)|^4619 ≤ (44803111423389/100000000000000 : ℝ)^3595
        have hw : |(1338291511/2500000000 : ℝ)|=(1338291511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2602320717/5000000000 : ℝ)|^4619 ≤ (1080307938333/2500000000000 : ℝ)^3595
        have hw : |(2602320717/5000000000 : ℝ)|=(2602320717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1918162709/10000000000 : ℝ)|^4619 ≤ (1498071377939/12500000000000 : ℝ)^3595
        have hw : |(-1918162709/10000000000 : ℝ)|=(1918162709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s2_3 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4245794119/10000000000 : ℝ)*x 0 + (9932139/25000000 : ℝ)*x 1 + (1133459461/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4245794119/10000000000 : ℝ)^4619 ≤ (4158117384697/12500000000000 : ℝ)^3595 := by
    have hnat : (4245794119 : ℕ)^4619*12500000000000^3595 ≤ 4158117384697^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245794119 10000000000 4158117384697 12500000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9932139/25000000 : ℝ)^4619 ≤ (3817870618867/12500000000000 : ℝ)^3595 := by
    have hnat : (9932139 : ℕ)^4619*12500000000000^3595 ≤ 3817870618867^3595*25000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9932139 25000000 3817870618867 12500000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133459461/2500000000 : ℝ)^4619 ≤ (1809604798077/5000000000000 : ℝ)^3595 := by
    have hnat : (1133459461 : ℕ)^4619*5000000000000^3595 ≤ 1809604798077^3595*2500000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133459461 2500000000 1809604798077 5000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4245794119/10000000000 : ℝ), (9932139/25000000 : ℝ), (1133459461/2500000000 : ℝ)] ![(4158117384697/12500000000000 : ℝ), (3817870618867/12500000000000 : ℝ), (1809604798077/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4245794119/10000000000 : ℝ)|^4619 ≤ (4158117384697/12500000000000 : ℝ)^3595
        have hw : |(4245794119/10000000000 : ℝ)|=(4245794119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9932139/25000000 : ℝ)|^4619 ≤ (3817870618867/12500000000000 : ℝ)^3595
        have hw : |(9932139/25000000 : ℝ)|=(9932139/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1133459461/2500000000 : ℝ)|^4619 ≤ (1809604798077/5000000000000 : ℝ)^3595
        have hw : |(1133459461/2500000000 : ℝ)|=(1133459461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s2_4 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-359085611/2000000000 : ℝ)*x 0 + (5206074833/10000000000 : ℝ)*x 1 + (5442308887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (359085611/2000000000 : ℝ)^4619 ≤ (1376053102237/12500000000000 : ℝ)^3595 := by
    have hnat : (359085611 : ℕ)^4619*12500000000000^3595 ≤ 1376053102237^3595*2000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359085611 2000000000 1376053102237 12500000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5206074833/10000000000 : ℝ)^4619 ≤ (10806902257033/25000000000000 : ℝ)^3595 := by
    have hnat : (5206074833 : ℕ)^4619*25000000000000^3595 ≤ 10806902257033^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206074833 10000000000 10806902257033 25000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442308887/10000000000 : ℝ)^4619 ≤ (22881983068563/50000000000000 : ℝ)^3595 := by
    have hnat : (5442308887 : ℕ)^4619*50000000000000^3595 ≤ 22881983068563^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442308887 10000000000 22881983068563 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-359085611/2000000000 : ℝ), (5206074833/10000000000 : ℝ), (5442308887/10000000000 : ℝ)] ![(1376053102237/12500000000000 : ℝ), (10806902257033/25000000000000 : ℝ), (22881983068563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-359085611/2000000000 : ℝ)|^4619 ≤ (1376053102237/12500000000000 : ℝ)^3595
        have hw : |(-359085611/2000000000 : ℝ)|=(359085611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5206074833/10000000000 : ℝ)|^4619 ≤ (10806902257033/25000000000000 : ℝ)^3595
        have hw : |(5206074833/10000000000 : ℝ)|=(5206074833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442308887/10000000000 : ℝ)|^4619 ≤ (22881983068563/50000000000000 : ℝ)^3595
        have hw : |(5442308887/10000000000 : ℝ)|=(5442308887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s2_5 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057993123/2000000000 : ℝ)*x 0 + (-1680495649/10000000000 : ℝ)*x 1 + (2721154691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057993123/2000000000 : ℝ)^4619 ≤ (44124636762881/100000000000000 : ℝ)^3595 := by
    have hnat : (1057993123 : ℕ)^4619*100000000000000^3595 ≤ 44124636762881^3595*2000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057993123 2000000000 44124636762881 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1680495649/10000000000 : ℝ)^4619 ≤ (5055695867387/50000000000000 : ℝ)^3595 := by
    have hnat : (1680495649 : ℕ)^4619*50000000000000^3595 ≤ 5055695867387^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1680495649 10000000000 5055695867387 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721154691/5000000000 : ℝ)^4619 ≤ (45763971485167/100000000000000 : ℝ)^3595 := by
    have hnat : (2721154691 : ℕ)^4619*100000000000000^3595 ≤ 45763971485167^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721154691 5000000000 45763971485167 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057993123/2000000000 : ℝ), (-1680495649/10000000000 : ℝ), (2721154691/5000000000 : ℝ)] ![(44124636762881/100000000000000 : ℝ), (5055695867387/50000000000000 : ℝ), (45763971485167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057993123/2000000000 : ℝ)|^4619 ≤ (44124636762881/100000000000000 : ℝ)^3595
        have hw : |(1057993123/2000000000 : ℝ)|=(1057993123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1680495649/10000000000 : ℝ)|^4619 ≤ (5055695867387/50000000000000 : ℝ)^3595
        have hw : |(-1680495649/10000000000 : ℝ)|=(1680495649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721154691/5000000000 : ℝ)|^4619 ≤ (45763971485167/100000000000000 : ℝ)^3595
        have hw : |(2721154691/5000000000 : ℝ)|=(2721154691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s2_6 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330622857/625000000 : ℝ)*x 0 + (2721155287/5000000000 : ℝ)*x 1 + (-1680493849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330622857/625000000 : ℝ)^4619 ≤ (44124637802439/100000000000000 : ℝ)^3595 := by
    have hnat : (330622857 : ℕ)^4619*100000000000000^3595 ≤ 44124637802439^3595*625000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330622857 625000000 44124637802439 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721155287/5000000000 : ℝ)^4619 ≤ (45763984363683/100000000000000 : ℝ)^3595 := by
    have hnat : (2721155287 : ℕ)^4619*100000000000000^3595 ≤ 45763984363683^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721155287 5000000000 45763984363683 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1680493849/10000000000 : ℝ)^4619 ≤ (2022275563879/20000000000000 : ℝ)^3595 := by
    have hnat : (1680493849 : ℕ)^4619*20000000000000^3595 ≤ 2022275563879^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1680493849 10000000000 2022275563879 20000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330622857/625000000 : ℝ), (2721155287/5000000000 : ℝ), (-1680493849/10000000000 : ℝ)] ![(44124637802439/100000000000000 : ℝ), (45763984363683/100000000000000 : ℝ), (2022275563879/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330622857/625000000 : ℝ)|^4619 ≤ (44124637802439/100000000000000 : ℝ)^3595
        have hw : |(330622857/625000000 : ℝ)|=(330622857/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721155287/5000000000 : ℝ)|^4619 ≤ (45763984363683/100000000000000 : ℝ)^3595
        have hw : |(2721155287/5000000000 : ℝ)|=(2721155287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1680493849/10000000000 : ℝ)|^4619 ≤ (2022275563879/20000000000000 : ℝ)^3595
        have hw : |(-1680493849/10000000000 : ℝ)|=(1680493849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s2_7 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (849178321/2000000000 : ℝ)*x 0 + (4530475257/10000000000 : ℝ)*x 1 + (62128859/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849178321/2000000000 : ℝ)^4619 ≤ (33265920419923/100000000000000 : ℝ)^3595 := by
    have hnat : (849178321 : ℕ)^4619*100000000000000^3595 ≤ 33265920419923^3595*2000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849178321 2000000000 33265920419923 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4530475257/10000000000 : ℝ)^4619 ≤ (18078805709683/50000000000000 : ℝ)^3595 := by
    have hnat : (4530475257 : ℕ)^4619*50000000000000^3595 ≤ 18078805709683^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530475257 10000000000 18078805709683 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62128859/156250000 : ℝ)^4619 ≤ (7644117036173/25000000000000 : ℝ)^3595 := by
    have hnat : (62128859 : ℕ)^4619*25000000000000^3595 ≤ 7644117036173^3595*156250000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62128859 156250000 7644117036173 25000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(849178321/2000000000 : ℝ), (4530475257/10000000000 : ℝ), (62128859/156250000 : ℝ)] ![(33265920419923/100000000000000 : ℝ), (18078805709683/50000000000000 : ℝ), (7644117036173/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(849178321/2000000000 : ℝ)|^4619 ≤ (33265920419923/100000000000000 : ℝ)^3595
        have hw : |(849178321/2000000000 : ℝ)|=(849178321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4530475257/10000000000 : ℝ)|^4619 ≤ (18078805709683/50000000000000 : ℝ)^3595
        have hw : |(4530475257/10000000000 : ℝ)|=(4530475257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(62128859/156250000 : ℝ)|^4619 ≤ (7644117036173/25000000000000 : ℝ)^3595
        have hw : |(62128859/156250000 : ℝ)|=(62128859/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1561_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83652401/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8919/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8967/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (673/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3959/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8919/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8967/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8919/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8967/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8919/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8967/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8919/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8967/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8919/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8967/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8919/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8967/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (8967/100000 : ℝ) ^ (4617/1024 : ℝ) ≤ (1895426789003499/100000000000000000000 : ℝ) := by
    have hpowers : (8967/100000 : ℝ)^4617 ≤ (1895426789003499/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8967 : ℕ)^4617*100000000000000000000^1024 ≤ 1895426789003499^1024*100000^4617 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8967 100000 1895426789003499 100000000000000000000 4617 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8967/100000 : ℝ)) (X := (1895426789003499/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8919/50000 : ℝ) ^ (4617/1024 : ℝ) ≤ (21059485513157319/50000000000000000000 : ℝ) := by
    have hpowers : (8919/50000 : ℝ)^4617 ≤ (21059485513157319/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8919 : ℕ)^4617*50000000000000000000^1024 ≤ 21059485513157319^1024*50000^4617 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8919 50000 21059485513157319 50000000000000000000 4617 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8919/50000 : ℝ)) (X := (21059485513157319/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001895426789003499/50000000000000000000 : ℝ) ≤ (10000084075737633/10000000000000000 : ℝ) ^ (4617/1024 : ℝ) := by
    have hpowers : (50001895426789003499/50000000000000000000 : ℝ)^1024 ≤ (10000084075737633/10000000000000000 : ℝ)^4617 := by
      have hnat : (50001895426789003499 : ℕ)^1024*10000000000000000^4617 ≤ 10000084075737633^4617*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001895426789003499 50000000000000000000 10000084075737633 10000000000000000 1024 4617 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000084075737633/10000000000000000 : ℝ)) (X := (50001895426789003499/50000000000000000000 : ℝ)) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044014397815318137/100000000000000000000 : ℝ) ≤ (2000195204792943/2000000000000000 : ℝ) ^ (4617/1024 : ℝ) := by
    have hpowers : (100044014397815318137/100000000000000000000 : ℝ)^1024 ≤ (2000195204792943/2000000000000000 : ℝ)^4617 := by
      have hnat : (100044014397815318137 : ℕ)^1024*2000000000000000^4617 ≤ 2000195204792943^4617*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044014397815318137 100000000000000000000 2000195204792943 2000000000000000 1024 4617 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000195204792943/2000000000000000 : ℝ)) (X := (100044014397815318137/100000000000000000000 : ℝ)) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25021059485513157319/25000000000000000000 : ℝ) ≤ (10001867972191797/10000000000000000 : ℝ) ^ (4617/1024 : ℝ) := by
    have hpowers : (25021059485513157319/25000000000000000000 : ℝ)^1024 ≤ (10001867972191797/10000000000000000 : ℝ)^4617 := by
      have hnat : (25021059485513157319 : ℕ)^1024*10000000000000000^4617 ≤ 10001867972191797^4617*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25021059485513157319 25000000000000000000 10001867972191797 10000000000000000 1024 4617 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001867972191797/10000000000000000 : ℝ)) (X := (25021059485513157319/25000000000000000000 : ℝ)) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1895426789003499/100000000000000000000 : ℝ) ≤ ((5912983309090936917/5914000000000000000 : ℝ)+2*(148658037847/147850000000000 : ℝ)*(8967/100000 : ℝ))^(4617/1024 : ℝ) := by
    rw [show (5912983309090936917/5914000000000000000 : ℝ)+2*(148658037847/147850000000000 : ℝ)*(8967/100000 : ℝ)=(10000084075737633/10000000000000000 : ℝ) by norm_num, show 1+2*(1895426789003499/100000000000000000000 : ℝ)=(50001895426789003499/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21059485513157319/50000000000000000000 : ℝ)+(1895426789003499/100000000000000000000 : ℝ) ≤ ((5912983309090936917/5914000000000000000 : ℝ)+(148658037847/147850000000000 : ℝ)*((8919/50000 : ℝ)+(8967/100000 : ℝ)))^(4617/1024 : ℝ) := by
    rw [show (5912983309090936917/5914000000000000000 : ℝ)+(148658037847/147850000000000 : ℝ)*((8919/50000 : ℝ)+(8967/100000 : ℝ))=(2000195204792943/2000000000000000 : ℝ) by norm_num, show 1+(21059485513157319/50000000000000000000 : ℝ)+(1895426789003499/100000000000000000000 : ℝ)=(100044014397815318137/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21059485513157319/50000000000000000000 : ℝ) ≤ ((5912983309090936917/5914000000000000000 : ℝ)+2*(148658037847/147850000000000 : ℝ)*(8919/50000 : ℝ))^(4617/1024 : ℝ) := by
    rw [show (5912983309090936917/5914000000000000000 : ℝ)+2*(148658037847/147850000000000 : ℝ)*(8919/50000 : ℝ)=(10001867972191797/10000000000000000 : ℝ) by norm_num, show 1+2*(21059485513157319/50000000000000000000 : ℝ)=(25021059485513157319/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5912983309090936917/5914000000000000000 : ℝ)*(X 1 0+X 2 0)+(148658037847/147850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4617/1024 : ℝ)) (lo := (8967/100000 : ℝ)) (hi := (8919/50000 : ℝ)) (c := (5912983309090936917/5914000000000000000 : ℝ)) (alpha := (148658037847/147850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5912983309090936917/5914000000000000000 : ℝ)*(X 0 1+X 2 1)+(148658037847/147850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4617/1024 : ℝ)) (lo := (8967/100000 : ℝ)) (hi := (8919/50000 : ℝ)) (c := (5912983309090936917/5914000000000000000 : ℝ)) (alpha := (148658037847/147850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5912983309090936917/5914000000000000000 : ℝ)*(X 0 2+X 1 2)+(148658037847/147850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4617/1024 : ℝ)) (lo := (8967/100000 : ℝ)) (hi := (8919/50000 : ℝ)) (c := (5912983309090936917/5914000000000000000 : ℝ)) (alpha := (148658037847/147850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-897693421/5000000000 : ℝ)*X 0 0+(340234659/625000000 : ℝ)*X 0 1+(5204641107/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669145789/1250000000 : ℝ)*X 1 0+(-959081337/5000000000 : ℝ)*X 1 1+(5204641191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338291511/2500000000 : ℝ)*X 2 0+(2602320717/5000000000 : ℝ)*X 2 1+(-1918162709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4245794119/10000000000 : ℝ)*X 0 0+(9932139/25000000 : ℝ)*X 0 1+(1133459461/2500000000 : ℝ)*X 0 2+(4245794119/10000000000 : ℝ)*X 1 0+(9932139/25000000 : ℝ)*X 1 1+(1133459461/2500000000 : ℝ)*X 1 2+(4245794119/10000000000 : ℝ)*X 2 0+(9932139/25000000 : ℝ)*X 2 1+(1133459461/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-359085611/2000000000 : ℝ)*X 0 0+(5206074833/10000000000 : ℝ)*X 0 1+(5442308887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057993123/2000000000 : ℝ)*X 1 0+(-1680495649/10000000000 : ℝ)*X 1 1+(2721154691/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330622857/625000000 : ℝ)*X 2 0+(2721155287/5000000000 : ℝ)*X 2 1+(-1680493849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((849178321/2000000000 : ℝ)*X 0 0+(4530475257/10000000000 : ℝ)*X 0 1+(62128859/156250000 : ℝ)*X 0 2+(849178321/2000000000 : ℝ)*X 1 0+(4530475257/10000000000 : ℝ)*X 1 1+(62128859/156250000 : ℝ)*X 1 2+(849178321/2000000000 : ℝ)*X 2 0+(4530475257/10000000000 : ℝ)*X 2 1+(62128859/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2291788705526824877239209879/295700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (595516247/50000000000000 : ℝ)*(base19) + (786550819/100000000000000 : ℝ)*(base23) + (52222047/50000000000000 : ℝ)*(lower2) + (4412681/2000000000000 : ℝ)*(upper3) + (1850603/25000000000000 : ℝ)*(upper5) + (2982376985966871/100000000000000 : ℝ)*(major0) + (2982376985966871/100000000000000 : ℝ)*(major1) + (2982376985966871/100000000000000 : ℝ)*(major2) + (1045534134986159/25000000000000 : ℝ)*(sp0) + (2091075787437329/50000000000000 : ℝ)*(sp1) + (1045537994839083/25000000000000 : ℝ)*(sp2) + (891296577775073/50000000000000 : ℝ)*(sp3) + (4056490629/25000000000000 : ℝ)*(sp4) + (3896065143/50000000000000 : ℝ)*(sp7) + (111412559230027/6250000000000 : ℝ)*(f.failure) + (261384547869197/6250000000000 : ℝ)*(f.sum) + (41686952586777/7392500000000000000000000000 : ℝ)*base65 + (1544454774242756707/591400000000000000000000000000000 : ℝ)*base67 + (1250271602876756707/591400000000000000000000000000000 : ℝ)*base69 + (2445911135802356707/591400000000000000000000000000000 : ℝ)*base71 + (5886880917453/1848125000000000000000000000 : ℝ)*base73 + (1531322666490843293/591400000000000000000000000000000 : ℝ)*base76 + (2084761304685556707/591400000000000000000000000000000 : ℝ)*base77 + (49412152583643293/591400000000000000000000000000000 : ℝ)*base80 + (26811450201227/7392500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2030173/312500000000000000000 : ℝ)*base90 + (2030173/312500000000000000000 : ℝ)*base92 + (2030173/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (637148641432032494342199477/73925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13956659/5000000000000 : ℝ)*(base15) + (87940293/50000000000000 : ℝ)*(lower2) + (57625057/100000000000000 : ℝ)*(upper3) + (78140523/100000000000000 : ℝ)*(lower4) + (954013/6250000000000 : ℝ)*(upper5) + (754675398674227/25000000000000 : ℝ)*(major0) + (754675398674227/25000000000000 : ℝ)*(major1) + (754675398674227/25000000000000 : ℝ)*(major2) + (7442673427/25000000000000 : ℝ)*(sp2) + (126169599/25000000000000 : ℝ)*(sp3) + (4233090318950699/100000000000000 : ℝ)*(sp4) + (52913625497719/1250000000000 : ℝ)*(sp5) + (132283142133031/3125000000000 : ℝ)*(sp6) + (1804312078469641/100000000000000 : ℝ)*(sp7) + (1804312583148037/100000000000000 : ℝ)*(f.failure) + (4233090318950699/100000000000000 : ℝ)*(f.sum) + (658512715447/3696250000000000000000000000 : ℝ)*base66 + (1765377534239901841/147850000000000000000000000000000 : ℝ)*base68 + (90245345995448159/147850000000000000000000000000000 : ℝ)*base69 + (2182601825271151841/147850000000000000000000000000000 : ℝ)*base72 + (18363270831593/14785000000000000000000000000 : ℝ)*base74 + (2716156215206501841/147850000000000000000000000000000 : ℝ)*base76 + (573361405839248159/147850000000000000000000000000000 : ℝ)*base77 + (1673602960501951841/147850000000000000000000000000000 : ℝ)*base80 + (41669684909013/3696250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (33486837/5000000000000000000000 : ℝ)*base89 + (33486837/5000000000000000000000 : ℝ)*base91 + (33486837/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1561_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83652401/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8919/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8967/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (673/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3959/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1561_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1561_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83652401/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (673/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3959/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1561_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1561_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1561_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83652401/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (673/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3959/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1561_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

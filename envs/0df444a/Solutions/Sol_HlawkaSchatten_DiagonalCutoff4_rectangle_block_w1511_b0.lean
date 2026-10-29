-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1511_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:55:34.871417+00:00
-- url     : https://prove2.me/submissions/d8efb4b0-b7b3-46d3-869e-ff6f1175ec35

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
theorem support_rectangle_w1511_s0_0 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-21086189/125000000 : ℝ)*x 0 + (5913598843/10000000000 : ℝ)*x 1 + (4854889157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21086189/125000000 : ℝ)^4519 ≤ (1251822182441/12500000000000 : ℝ)^3495 := by
    have hnat : (21086189 : ℕ)^4519*12500000000000^3495 ≤ 1251822182441^3495*125000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21086189 125000000 1251822182441 12500000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5913598843/10000000000 : ℝ)^4519 ≤ (50699857657179/100000000000000 : ℝ)^3495 := by
    have hnat : (5913598843 : ℕ)^4519*100000000000000^3495 ≤ 50699857657179^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5913598843 10000000000 50699857657179 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4854889157/10000000000 : ℝ)^4519 ≤ (19642782433283/50000000000000 : ℝ)^3495 := by
    have hnat : (4854889157 : ℕ)^4519*50000000000000^3495 ≤ 19642782433283^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4854889157 10000000000 19642782433283 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21086189/125000000 : ℝ), (5913598843/10000000000 : ℝ), (4854889157/10000000000 : ℝ)] ![(1251822182441/12500000000000 : ℝ), (50699857657179/100000000000000 : ℝ), (19642782433283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21086189/125000000 : ℝ)|^4519 ≤ (1251822182441/12500000000000 : ℝ)^3495
        have hw : |(-21086189/125000000 : ℝ)|=(21086189/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5913598843/10000000000 : ℝ)|^4519 ≤ (50699857657179/100000000000000 : ℝ)^3495
        have hw : |(5913598843/10000000000 : ℝ)|=(5913598843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4854889157/10000000000 : ℝ)|^4519 ≤ (19642782433283/50000000000000 : ℝ)^3495
        have hw : |(4854889157/10000000000 : ℝ)|=(4854889157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s0_1 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2739098883/5000000000 : ℝ)*x 0 + (-228039849/1000000000 : ℝ)*x 1 + (2427444543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2739098883/5000000000 : ℝ)^4519 ≤ (22963134848573/50000000000000 : ℝ)^3495 := by
    have hnat : (2739098883 : ℕ)^4519*50000000000000^3495 ≤ 22963134848573^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739098883 5000000000 22963134848573 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (228039849/1000000000 : ℝ)^4519 ≤ (14788166173021/100000000000000 : ℝ)^3495 := by
    have hnat : (228039849 : ℕ)^4519*100000000000000^3495 ≤ 14788166173021^3495*1000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228039849 1000000000 14788166173021 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2427444543/5000000000 : ℝ)^4519 ≤ (19642782061853/50000000000000 : ℝ)^3495 := by
    have hnat : (2427444543 : ℕ)^4519*50000000000000^3495 ≤ 19642782061853^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2427444543 5000000000 19642782061853 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2739098883/5000000000 : ℝ), (-228039849/1000000000 : ℝ), (2427444543/5000000000 : ℝ)] ![(22963134848573/50000000000000 : ℝ), (14788166173021/100000000000000 : ℝ), (19642782061853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2739098883/5000000000 : ℝ)|^4519 ≤ (22963134848573/50000000000000 : ℝ)^3495
        have hw : |(2739098883/5000000000 : ℝ)|=(2739098883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-228039849/1000000000 : ℝ)|^4519 ≤ (14788166173021/100000000000000 : ℝ)^3495
        have hw : |(-228039849/1000000000 : ℝ)|=(228039849/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2427444543/5000000000 : ℝ)|^4519 ≤ (19642782061853/50000000000000 : ℝ)^3495
        have hw : |(2427444543/5000000000 : ℝ)|=(2427444543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s0_2 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5478197823/10000000000 : ℝ)*x 0 + (2427444553/5000000000 : ℝ)*x 1 + (-2280398391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5478197823/10000000000 : ℝ)^4519 ≤ (4592627031501/10000000000000 : ℝ)^3495 := by
    have hnat : (5478197823 : ℕ)^4519*10000000000000^3495 ≤ 4592627031501^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478197823 10000000000 4592627031501 10000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2427444553/5000000000 : ℝ)^4519 ≤ (39285564332963/100000000000000 : ℝ)^3495 := by
    have hnat : (2427444553 : ℕ)^4519*100000000000000^3495 ≤ 39285564332963^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2427444553 5000000000 39285564332963 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2280398391/10000000000 : ℝ)^4519 ≤ (2957633068583/20000000000000 : ℝ)^3495 := by
    have hnat : (2280398391 : ℕ)^4519*20000000000000^3495 ≤ 2957633068583^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280398391 10000000000 2957633068583 20000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5478197823/10000000000 : ℝ), (2427444553/5000000000 : ℝ), (-2280398391/10000000000 : ℝ)] ![(4592627031501/10000000000000 : ℝ), (39285564332963/100000000000000 : ℝ), (2957633068583/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5478197823/10000000000 : ℝ)|^4519 ≤ (4592627031501/10000000000000 : ℝ)^3495
        have hw : |(5478197823/10000000000 : ℝ)|=(5478197823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2427444553/5000000000 : ℝ)|^4519 ≤ (39285564332963/100000000000000 : ℝ)^3495
        have hw : |(2427444553/5000000000 : ℝ)|=(2427444553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2280398391/10000000000 : ℝ)|^4519 ≤ (2957633068583/20000000000000 : ℝ)^3495
        have hw : |(-2280398391/10000000000 : ℝ)|=(2280398391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s0_3 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (207270673/500000000 : ℝ)*x 0 + (3091261577/10000000000 : ℝ)*x 1 + (2745142333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207270673/500000000 : ℝ)^4519 ≤ (8006801699101/25000000000000 : ℝ)^3495 := by
    have hnat : (207270673 : ℕ)^4519*25000000000000^3495 ≤ 8006801699101^3495*500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207270673 500000000 8006801699101 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091261577/10000000000 : ℝ)^4519 ≤ (10957731196359/50000000000000 : ℝ)^3495 := by
    have hnat : (3091261577 : ℕ)^4519*50000000000000^3495 ≤ 10957731196359^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091261577 10000000000 10957731196359 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2745142333/5000000000 : ℝ)^4519 ≤ (46057330804571/100000000000000 : ℝ)^3495 := by
    have hnat : (2745142333 : ℕ)^4519*100000000000000^3495 ≤ 46057330804571^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745142333 5000000000 46057330804571 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207270673/500000000 : ℝ), (3091261577/10000000000 : ℝ), (2745142333/5000000000 : ℝ)] ![(8006801699101/25000000000000 : ℝ), (10957731196359/50000000000000 : ℝ), (46057330804571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207270673/500000000 : ℝ)|^4519 ≤ (8006801699101/25000000000000 : ℝ)^3495
        have hw : |(207270673/500000000 : ℝ)|=(207270673/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091261577/10000000000 : ℝ)|^4519 ≤ (10957731196359/50000000000000 : ℝ)^3495
        have hw : |(3091261577/10000000000 : ℝ)|=(3091261577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2745142333/5000000000 : ℝ)|^4519 ≤ (46057330804571/100000000000000 : ℝ)^3495
        have hw : |(2745142333/5000000000 : ℝ)|=(2745142333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s0_4 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-845212033/5000000000 : ℝ)*x 0 + (2440949579/5000000000 : ℝ)*x 1 + (2942810581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (845212033/5000000000 : ℝ)^4519 ≤ (10041674242443/100000000000000 : ℝ)^3495 := by
    have hnat : (845212033 : ℕ)^4519*100000000000000^3495 ≤ 10041674242443^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845212033 5000000000 10041674242443 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2440949579/5000000000 : ℝ)^4519 ≤ (4946049466009/12500000000000 : ℝ)^3495 := by
    have hnat : (2440949579 : ℕ)^4519*12500000000000^3495 ≤ 4946049466009^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2440949579 5000000000 4946049466009 12500000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2942810581/5000000000 : ℝ)^4519 ≤ (1574685312933/3125000000000 : ℝ)^3495 := by
    have hnat : (2942810581 : ℕ)^4519*3125000000000^3495 ≤ 1574685312933^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2942810581 5000000000 1574685312933 3125000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-845212033/5000000000 : ℝ), (2440949579/5000000000 : ℝ), (2942810581/5000000000 : ℝ)] ![(10041674242443/100000000000000 : ℝ), (4946049466009/12500000000000 : ℝ), (1574685312933/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-845212033/5000000000 : ℝ)|^4519 ≤ (10041674242443/100000000000000 : ℝ)^3495
        have hw : |(-845212033/5000000000 : ℝ)|=(845212033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2440949579/5000000000 : ℝ)|^4519 ≤ (4946049466009/12500000000000 : ℝ)^3495
        have hw : |(2440949579/5000000000 : ℝ)|=(2440949579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2942810581/5000000000 : ℝ)|^4519 ≤ (1574685312933/3125000000000 : ℝ)^3495
        have hw : |(2942810581/5000000000 : ℝ)|=(2942810581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s0_5 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (648618859/1250000000 : ℝ)*x 0 + (-1249666417/10000000000 : ℝ)*x 1 + (735702651/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (648618859/1250000000 : ℝ)^4519 ≤ (42815470705059/100000000000000 : ℝ)^3495 := by
    have hnat : (648618859 : ℕ)^4519*100000000000000^3495 ≤ 42815470705059^3495*1250000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648618859 1250000000 42815470705059 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1249666417/10000000000 : ℝ)^4519 ≤ (1698649687569/25000000000000 : ℝ)^3495 := by
    have hnat : (1249666417 : ℕ)^4519*25000000000000^3495 ≤ 1698649687569^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249666417 10000000000 1698649687569 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (735702651/1250000000 : ℝ)^4519 ≤ (2015597220923/4000000000000 : ℝ)^3495 := by
    have hnat : (735702651 : ℕ)^4519*4000000000000^3495 ≤ 2015597220923^3495*1250000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735702651 1250000000 2015597220923 4000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(648618859/1250000000 : ℝ), (-1249666417/10000000000 : ℝ), (735702651/1250000000 : ℝ)] ![(42815470705059/100000000000000 : ℝ), (1698649687569/25000000000000 : ℝ), (2015597220923/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(648618859/1250000000 : ℝ)|^4519 ≤ (42815470705059/100000000000000 : ℝ)^3495
        have hw : |(648618859/1250000000 : ℝ)|=(648618859/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1249666417/10000000000 : ℝ)|^4519 ≤ (1698649687569/25000000000000 : ℝ)^3495
        have hw : |(-1249666417/10000000000 : ℝ)|=(1249666417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(735702651/1250000000 : ℝ)|^4519 ≤ (2015597220923/4000000000000 : ℝ)^3495
        have hw : |(735702651/1250000000 : ℝ)|=(735702651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s0_6 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5188950853/10000000000 : ℝ)*x 0 + (294281063/500000000 : ℝ)*x 1 + (-249933273/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5188950853/10000000000 : ℝ)^4519 ≤ (42815470502351/100000000000000 : ℝ)^3495 := by
    have hnat : (5188950853 : ℕ)^4519*100000000000000^3495 ≤ 42815470502351^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188950853 10000000000 42815470502351 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (294281063/500000000 : ℝ)^4519 ≤ (25194965549357/50000000000000 : ℝ)^3495 := by
    have hnat : (294281063 : ℕ)^4519*50000000000000^3495 ≤ 25194965549357^3495*500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294281063 500000000 25194965549357 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249933273/2000000000 : ℝ)^4519 ≤ (1698649596177/25000000000000 : ℝ)^3495 := by
    have hnat : (249933273 : ℕ)^4519*25000000000000^3495 ≤ 1698649596177^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249933273 2000000000 1698649596177 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5188950853/10000000000 : ℝ), (294281063/500000000 : ℝ), (-249933273/2000000000 : ℝ)] ![(42815470502351/100000000000000 : ℝ), (25194965549357/50000000000000 : ℝ), (1698649596177/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5188950853/10000000000 : ℝ)|^4519 ≤ (42815470502351/100000000000000 : ℝ)^3495
        have hw : |(5188950853/10000000000 : ℝ)|=(5188950853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(294281063/500000000 : ℝ)|^4519 ≤ (25194965549357/50000000000000 : ℝ)^3495
        have hw : |(294281063/500000000 : ℝ)|=(294281063/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-249933273/2000000000 : ℝ)|^4519 ≤ (1698649596177/25000000000000 : ℝ)^3495
        have hw : |(-249933273/2000000000 : ℝ)|=(249933273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s0_7 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4153409989/10000000000 : ℝ)*x 0 + (271454011/500000000 : ℝ)*x 1 + (3154658811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4153409989/10000000000 : ℝ)^4519 ≤ (16053555584217/50000000000000 : ℝ)^3495 := by
    have hnat : (4153409989 : ℕ)^4519*50000000000000^3495 ≤ 16053555584217^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153409989 10000000000 16053555584217 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271454011/500000000 : ℝ)^4519 ≤ (45394549366927/100000000000000 : ℝ)^3495 := by
    have hnat : (271454011 : ℕ)^4519*100000000000000^3495 ≤ 45394549366927^3495*500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271454011 500000000 45394549366927 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154658811/10000000000 : ℝ)^4519 ≤ (1406146215317/6250000000000 : ℝ)^3495 := by
    have hnat : (3154658811 : ℕ)^4519*6250000000000^3495 ≤ 1406146215317^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154658811 10000000000 1406146215317 6250000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4153409989/10000000000 : ℝ), (271454011/500000000 : ℝ), (3154658811/10000000000 : ℝ)] ![(16053555584217/50000000000000 : ℝ), (45394549366927/100000000000000 : ℝ), (1406146215317/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4153409989/10000000000 : ℝ)|^4519 ≤ (16053555584217/50000000000000 : ℝ)^3495
        have hw : |(4153409989/10000000000 : ℝ)|=(4153409989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271454011/500000000 : ℝ)|^4519 ≤ (45394549366927/100000000000000 : ℝ)^3495
        have hw : |(271454011/500000000 : ℝ)|=(271454011/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154658811/10000000000 : ℝ)|^4519 ≤ (1406146215317/6250000000000 : ℝ)^3495
        have hw : |(3154658811/10000000000 : ℝ)|=(3154658811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1511_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (563/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25497/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4517/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4517 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4517*1^1024 ≤ 0^1024*1^4517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4517 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4517/1024 : ℝ) ≤ (878220912933566937/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4517 ≤ (878220912933566937/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4517*50000000000000000000^1024 ≤ 878220912933566937^1024*5^4517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 878220912933566937 50000000000000000000 4517 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (878220912933566937/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4517 := by
      have hnat : (1 : ℕ)^1024*1^4517 ≤ 1^4517*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50878220912933566937/50000000000000000000 : ℝ) ≤ (5019775370087951/5000000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (50878220912933566937/50000000000000000000 : ℝ)^1024 ≤ (5019775370087951/5000000000000000 : ℝ)^4517 := by
      have hnat : (50878220912933566937 : ℕ)^1024*5000000000000000^4517 ≤ 5019775370087951^4517*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50878220912933566937 50000000000000000000 5019775370087951 5000000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5019775370087951/5000000000000000 : ℝ)) (X := (50878220912933566937/50000000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25878220912933566937/25000000000000000000 : ℝ) ≤ (2519775370087951/2500000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (25878220912933566937/25000000000000000000 : ℝ)^1024 ≤ (2519775370087951/2500000000000000 : ℝ)^4517 := by
      have hnat : (25878220912933566937 : ℕ)^1024*2500000000000000^4517 ≤ 2519775370087951^4517*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25878220912933566937 25000000000000000000 2519775370087951 2500000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2519775370087951/2500000000000000 : ℝ)) (X := (25878220912933566937/25000000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(19775370087951/2000000000000000 : ℝ)*(0 : ℝ))^(4517/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(19775370087951/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(878220912933566937/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(19775370087951/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4517/1024 : ℝ) := by
    rw [show (1 : ℝ)+(19775370087951/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5019775370087951/5000000000000000 : ℝ) by norm_num, show 1+(878220912933566937/50000000000000000000 : ℝ)+(0 : ℝ)=(50878220912933566937/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(878220912933566937/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(19775370087951/2000000000000000 : ℝ)*(2/5 : ℝ))^(4517/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(19775370087951/2000000000000000 : ℝ)*(2/5 : ℝ)=(2519775370087951/2500000000000000 : ℝ) by norm_num, show 1+2*(878220912933566937/50000000000000000000 : ℝ)=(25878220912933566937/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(19775370087951/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (19775370087951/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(19775370087951/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (19775370087951/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(19775370087951/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (19775370087951/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-21086189/125000000 : ℝ)*X 0 0+(5913598843/10000000000 : ℝ)*X 0 1+(4854889157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2739098883/5000000000 : ℝ)*X 1 0+(-228039849/1000000000 : ℝ)*X 1 1+(2427444543/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5478197823/10000000000 : ℝ)*X 2 0+(2427444553/5000000000 : ℝ)*X 2 1+(-2280398391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((207270673/500000000 : ℝ)*X 0 0+(3091261577/10000000000 : ℝ)*X 0 1+(2745142333/5000000000 : ℝ)*X 0 2+(207270673/500000000 : ℝ)*X 1 0+(3091261577/10000000000 : ℝ)*X 1 1+(2745142333/5000000000 : ℝ)*X 1 2+(207270673/500000000 : ℝ)*X 2 0+(3091261577/10000000000 : ℝ)*X 2 1+(2745142333/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-845212033/5000000000 : ℝ)*X 0 0+(2440949579/5000000000 : ℝ)*X 0 1+(2942810581/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((648618859/1250000000 : ℝ)*X 1 0+(-1249666417/10000000000 : ℝ)*X 1 1+(735702651/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5188950853/10000000000 : ℝ)*X 2 0+(294281063/500000000 : ℝ)*X 2 1+(-249933273/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4153409989/10000000000 : ℝ)*X 0 0+(271454011/500000000 : ℝ)*X 0 1+(3154658811/10000000000 : ℝ)*X 0 2+(4153409989/10000000000 : ℝ)*X 1 0+(271454011/500000000 : ℝ)*X 1 1+(3154658811/10000000000 : ℝ)*X 1 2+(4153409989/10000000000 : ℝ)*X 2 0+(271454011/500000000 : ℝ)*X 2 1+(3154658811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19681629463659060277791/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5165831/100000000000000 : ℝ)*(base1) + (401191427/100000000000000 : ℝ)*(base19) + (411019341/100000000000000 : ℝ)*(base23) + (18712051/50000000000000 : ℝ)*(upper3) + (68320523/100000000000000 : ℝ)*(upper5) + (170173310772149/25000000000000 : ℝ)*(major0) + (170173310772149/25000000000000 : ℝ)*(major1) + (170173310772149/25000000000000 : ℝ)*(major2) + (18890944885787/2000000000000 : ℝ)*(sp0) + (944548388083697/100000000000000 : ℝ)*(sp1) + (944548378255783/100000000000000 : ℝ)*(sp2) + (416837012757409/100000000000000 : ℝ)*(sp3) + (310030321/20000000000000 : ℝ)*(sp4) + (313247239/50000000000000 : ℝ)*(sp7) + (208418822208859/50000000000000 : ℝ)*(f.failure) + (236137197318781/25000000000000 : ℝ)*(f.sum) + (18433347523301/25000000000000000000000000000 : ℝ)*base66 + (427567638373301/50000000000000000000000000000 : ℝ)*base68 + (267873099323301/50000000000000000000000000000 : ℝ)*base70 + (249388487923301/50000000000000000000000000000 : ℝ)*base72 + (81983689298301/25000000000000000000000000000 : ℝ)*base74 + (109772498423301/50000000000000000000000000000 : ℝ)*base76 + (301455463273301/50000000000000000000000000000 : ℝ)*base78 + (149024106273301/50000000000000000000000000000 : ℝ)*base80 + (33386421198301/25000000000000000000000000000 : ℝ)*base82 + (60909971/5000000000000000000000 : ℝ)*base89 + (60909971/5000000000000000000000 : ℝ)*base91 + (60909971/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (258214968317845418000439/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (232864243/20000000000000 : ℝ)*(base19) + (292839361/25000000000000 : ℝ)*(base23) + (13357473/25000000000000 : ℝ)*(base32) + (43752193/25000000000000 : ℝ)*(upper3) + (66357409/50000000000000 : ℝ)*(upper5) + (717981934429037/100000000000000 : ℝ)*(major0) + (717981934429037/100000000000000 : ℝ)*(major1) + (717981934429037/100000000000000 : ℝ)*(major2) + (748545653/25000000000000 : ℝ)*(sp1) + (3185852503/100000000000000 : ℝ)*(sp2) + (498145746471083/50000000000000 : ℝ)*(sp4) + (49814366721917/5000000000000 : ℝ)*(sp5) + (996287135732219/100000000000000 : ℝ)*(sp6) + (4396721503427/1000000000000 : ℝ)*(sp7) + (27479512735787/6250000000000 : ℝ)*(f.failure) + (498145746471083/50000000000000 : ℝ)*(f.sum) + (165532676166813/100000000000000000000000000000 : ℝ)*base66 + (388635612633187/200000000000000000000000000000 : ℝ)*base67 + (1359284339833187/200000000000000000000000000000 : ℝ)*base69 + (21647856166813/200000000000000000000000000000 : ℝ)*base72 + (119822624233187/100000000000000000000000000000 : ℝ)*base73 + (902789752166813/200000000000000000000000000000 : ℝ)*base76 + (1005220843033187/200000000000000000000000000000 : ℝ)*base77 + (226073206633187/200000000000000000000000000000 : ℝ)*base79 + (205644349033187/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (431597/625000000000000000000 : ℝ)*base90 + (431597/625000000000000000000 : ℝ)*base92 + (431597/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1511_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (563/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25497/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1511_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1511_s1_0 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1840875383/10000000000 : ℝ)*x 0 + (1114234741/2000000000 : ℝ)*x 1 + (1274588207/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1840875383/10000000000 : ℝ)^4519 ≤ (5606010425913/50000000000000 : ℝ)^3495 := by
    have hnat : (1840875383 : ℕ)^4519*50000000000000^3495 ≤ 5606010425913^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840875383 10000000000 5606010425913 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1114234741/2000000000 : ℝ)^4519 ≤ (46936599988277/100000000000000 : ℝ)^3495 := by
    have hnat : (1114234741 : ℕ)^4519*100000000000000^3495 ≤ 46936599988277^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114234741 2000000000 46936599988277 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1274588207/2500000000 : ℝ)^4519 ≤ (20925689573707/50000000000000 : ℝ)^3495 := by
    have hnat : (1274588207 : ℕ)^4519*50000000000000^3495 ≤ 20925689573707^3495*2500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274588207 2500000000 20925689573707 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1840875383/10000000000 : ℝ), (1114234741/2000000000 : ℝ), (1274588207/2500000000 : ℝ)] ![(5606010425913/50000000000000 : ℝ), (46936599988277/100000000000000 : ℝ), (20925689573707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1840875383/10000000000 : ℝ)|^4519 ≤ (5606010425913/50000000000000 : ℝ)^3495
        have hw : |(-1840875383/10000000000 : ℝ)|=(1840875383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1114234741/2000000000 : ℝ)|^4519 ≤ (46936599988277/100000000000000 : ℝ)^3495
        have hw : |(1114234741/2000000000 : ℝ)|=(1114234741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1274588207/2500000000 : ℝ)|^4519 ≤ (20925689573707/50000000000000 : ℝ)^3495
        have hw : |(1274588207/2500000000 : ℝ)|=(1274588207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s1_1 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5386804259/10000000000 : ℝ)*x 0 + (-130617289/625000000 : ℝ)*x 1 + (2549176113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5386804259/10000000000 : ℝ)^4519 ≤ (1404313099907/3125000000000 : ℝ)^3495 := by
    have hnat : (5386804259 : ℕ)^4519*3125000000000^3495 ≤ 1404313099907^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386804259 10000000000 1404313099907 3125000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130617289/625000000 : ℝ)^4519 ≤ (13210608025809/100000000000000 : ℝ)^3495 := by
    have hnat : (130617289 : ℕ)^4519*100000000000000^3495 ≤ 13210608025809^3495*625000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130617289 625000000 13210608025809 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2549176113/5000000000 : ℝ)^4519 ≤ (20925686378923/50000000000000 : ℝ)^3495 := by
    have hnat : (2549176113 : ℕ)^4519*50000000000000^3495 ≤ 20925686378923^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2549176113 5000000000 20925686378923 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5386804259/10000000000 : ℝ), (-130617289/625000000 : ℝ), (2549176113/5000000000 : ℝ)] ![(1404313099907/3125000000000 : ℝ), (13210608025809/100000000000000 : ℝ), (20925686378923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5386804259/10000000000 : ℝ)|^4519 ≤ (1404313099907/3125000000000 : ℝ)^3495
        have hw : |(5386804259/10000000000 : ℝ)|=(5386804259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130617289/625000000 : ℝ)|^4519 ≤ (13210608025809/100000000000000 : ℝ)^3495
        have hw : |(-130617289/625000000 : ℝ)|=(130617289/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2549176113/5000000000 : ℝ)|^4519 ≤ (20925686378923/50000000000000 : ℝ)^3495
        have hw : |(2549176113/5000000000 : ℝ)|=(2549176113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s1_2 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5386803711/10000000000 : ℝ)*x 0 + (1274588209/2500000000 : ℝ)*x 1 + (-2089876557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5386803711/10000000000 : ℝ)^4519 ≤ (22469006643029/50000000000000 : ℝ)^3495 := by
    have hnat : (5386803711 : ℕ)^4519*50000000000000^3495 ≤ 22469006643029^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386803711 10000000000 22469006643029 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1274588209/2500000000 : ℝ)^4519 ≤ (20925689616163/50000000000000 : ℝ)^3495 := by
    have hnat : (1274588209 : ℕ)^4519*50000000000000^3495 ≤ 20925689616163^3495*2500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274588209 2500000000 20925689616163 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2089876557/10000000000 : ℝ)^4519 ≤ (6605303739099/50000000000000 : ℝ)^3495 := by
    have hnat : (2089876557 : ℕ)^4519*50000000000000^3495 ≤ 6605303739099^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089876557 10000000000 6605303739099 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5386803711/10000000000 : ℝ), (1274588209/2500000000 : ℝ), (-2089876557/10000000000 : ℝ)] ![(22469006643029/50000000000000 : ℝ), (20925689616163/50000000000000 : ℝ), (6605303739099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5386803711/10000000000 : ℝ)|^4519 ≤ (22469006643029/50000000000000 : ℝ)^3495
        have hw : |(5386803711/10000000000 : ℝ)|=(5386803711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1274588209/2500000000 : ℝ)|^4519 ≤ (20925689616163/50000000000000 : ℝ)^3495
        have hw : |(1274588209/2500000000 : ℝ)|=(1274588209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2089876557/10000000000 : ℝ)|^4519 ≤ (6605303739099/50000000000000 : ℝ)^3495
        have hw : |(-2089876557/10000000000 : ℝ)|=(2089876557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s1_3 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265623571/625000000 : ℝ)*x 0 + (3742805501/10000000000 : ℝ)*x 1 + (4814212073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265623571/625000000 : ℝ)^4519 ≤ (33075589024169/100000000000000 : ℝ)^3495 := by
    have hnat : (265623571 : ℕ)^4519*100000000000000^3495 ≤ 33075589024169^3495*625000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265623571 625000000 33075589024169 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3742805501/10000000000 : ℝ)^4519 ≤ (28063919773261/100000000000000 : ℝ)^3495 := by
    have hnat : (3742805501 : ℕ)^4519*100000000000000^3495 ≤ 28063919773261^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3742805501 10000000000 28063919773261 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4814212073/10000000000 : ℝ)^4519 ≤ (38860491191543/100000000000000 : ℝ)^3495 := by
    have hnat : (4814212073 : ℕ)^4519*100000000000000^3495 ≤ 38860491191543^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4814212073 10000000000 38860491191543 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265623571/625000000 : ℝ), (3742805501/10000000000 : ℝ), (4814212073/10000000000 : ℝ)] ![(33075589024169/100000000000000 : ℝ), (28063919773261/100000000000000 : ℝ), (38860491191543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265623571/625000000 : ℝ)|^4519 ≤ (33075589024169/100000000000000 : ℝ)^3495
        have hw : |(265623571/625000000 : ℝ)|=(265623571/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3742805501/10000000000 : ℝ)|^4519 ≤ (28063919773261/100000000000000 : ℝ)^3495
        have hw : |(3742805501/10000000000 : ℝ)|=(3742805501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4814212073/10000000000 : ℝ)|^4519 ≤ (38860491191543/100000000000000 : ℝ)^3495
        have hw : |(4814212073/10000000000 : ℝ)|=(4814212073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s1_4 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1841179089/10000000000 : ℝ)*x 0 + (5103647983/10000000000 : ℝ)*x 1 + (2782896631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1841179089/10000000000 : ℝ)^4519 ≤ (11214412616987/100000000000000 : ℝ)^3495 := by
    have hnat : (1841179089 : ℕ)^4519*100000000000000^3495 ≤ 11214412616987^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1841179089 10000000000 11214412616987 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5103647983/10000000000 : ℝ)^4519 ≤ (20953794974729/50000000000000 : ℝ)^3495 := by
    have hnat : (5103647983 : ℕ)^4519*50000000000000^3495 ≤ 20953794974729^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5103647983 10000000000 20953794974729 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2782896631/5000000000 : ℝ)^4519 ≤ (1171949935461/2500000000000 : ℝ)^3495 := by
    have hnat : (2782896631 : ℕ)^4519*2500000000000^3495 ≤ 1171949935461^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2782896631 5000000000 1171949935461 2500000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1841179089/10000000000 : ℝ), (5103647983/10000000000 : ℝ), (2782896631/5000000000 : ℝ)] ![(11214412616987/100000000000000 : ℝ), (20953794974729/50000000000000 : ℝ), (1171949935461/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1841179089/10000000000 : ℝ)|^4519 ≤ (11214412616987/100000000000000 : ℝ)^3495
        have hw : |(-1841179089/10000000000 : ℝ)|=(1841179089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5103647983/10000000000 : ℝ)|^4519 ≤ (20953794974729/50000000000000 : ℝ)^3495
        have hw : |(5103647983/10000000000 : ℝ)|=(5103647983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2782896631/5000000000 : ℝ)|^4519 ≤ (1171949935461/2500000000000 : ℝ)^3495
        have hw : |(2782896631/5000000000 : ℝ)|=(2782896631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s1_5 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657785037/1250000000 : ℝ)*x 0 + (-405608947/2500000000 : ℝ)*x 1 + (2782896719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657785037/1250000000 : ℝ)^4519 ≤ (4359942328677/10000000000000 : ℝ)^3495 := by
    have hnat : (657785037 : ℕ)^4519*10000000000000^3495 ≤ 4359942328677^3495*1250000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657785037 1250000000 4359942328677 10000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (405608947/2500000000 : ℝ)^4519 ≤ (4761288683/50000000000 : ℝ)^3495 := by
    have hnat : (405608947 : ℕ)^4519*50000000000^3495 ≤ 4761288683^3495*2500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405608947 2500000000 4761288683 50000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2782896719/5000000000 : ℝ)^4519 ≤ (46877999335121/100000000000000 : ℝ)^3495 := by
    have hnat : (2782896719 : ℕ)^4519*100000000000000^3495 ≤ 46877999335121^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2782896719 5000000000 46877999335121 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657785037/1250000000 : ℝ), (-405608947/2500000000 : ℝ), (2782896719/5000000000 : ℝ)] ![(4359942328677/10000000000000 : ℝ), (4761288683/50000000000 : ℝ), (46877999335121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657785037/1250000000 : ℝ)|^4519 ≤ (4359942328677/10000000000000 : ℝ)^3495
        have hw : |(657785037/1250000000 : ℝ)|=(657785037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-405608947/2500000000 : ℝ)|^4519 ≤ (4761288683/50000000000 : ℝ)^3495
        have hw : |(-405608947/2500000000 : ℝ)|=(405608947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2782896719/5000000000 : ℝ)|^4519 ≤ (46877999335121/100000000000000 : ℝ)^3495
        have hw : |(2782896719/5000000000 : ℝ)|=(2782896719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s1_6 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5262280083/10000000000 : ℝ)*x 0 + (222631741/400000000 : ℝ)*x 1 + (-405608991/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5262280083/10000000000 : ℝ)^4519 ≤ (43599421004949/100000000000000 : ℝ)^3495 := by
    have hnat : (5262280083 : ℕ)^4519*100000000000000^3495 ≤ 43599421004949^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262280083 10000000000 43599421004949 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222631741/400000000 : ℝ)^4519 ≤ (46878000282571/100000000000000 : ℝ)^3495 := by
    have hnat : (222631741 : ℕ)^4519*100000000000000^3495 ≤ 46878000282571^3495*400000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222631741 400000000 46878000282571 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (405608991/2500000000 : ℝ)^4519 ≤ (9522578701657/100000000000000 : ℝ)^3495 := by
    have hnat : (405608991 : ℕ)^4519*100000000000000^3495 ≤ 9522578701657^3495*2500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405608991 2500000000 9522578701657 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5262280083/10000000000 : ℝ), (222631741/400000000 : ℝ), (-405608991/2500000000 : ℝ)] ![(43599421004949/100000000000000 : ℝ), (46878000282571/100000000000000 : ℝ), (9522578701657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5262280083/10000000000 : ℝ)|^4519 ≤ (43599421004949/100000000000000 : ℝ)^3495
        have hw : |(5262280083/10000000000 : ℝ)|=(5262280083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(222631741/400000000 : ℝ)|^4519 ≤ (46878000282571/100000000000000 : ℝ)^3495
        have hw : |(222631741/400000000 : ℝ)|=(222631741/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-405608991/2500000000 : ℝ)|^4519 ≤ (9522578701657/100000000000000 : ℝ)^3495
        have hw : |(-405608991/2500000000 : ℝ)|=(405608991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s1_7 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265666623/625000000 : ℝ)*x 0 + (4802213597/10000000000 : ℝ)*x 1 + (3754996883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265666623/625000000 : ℝ)^4519 ≤ (8270630181129/25000000000000 : ℝ)^3495 := by
    have hnat : (265666623 : ℕ)^4519*25000000000000^3495 ≤ 8270630181129^3495*625000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265666623 625000000 8270630181129 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4802213597/10000000000 : ℝ)^4519 ≤ (9683827028153/25000000000000 : ℝ)^3495 := by
    have hnat : (4802213597 : ℕ)^4519*25000000000000^3495 ≤ 9683827028153^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4802213597 10000000000 9683827028153 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3754996883/10000000000 : ℝ)^4519 ≤ (14091085574009/50000000000000 : ℝ)^3495 := by
    have hnat : (3754996883 : ℕ)^4519*50000000000000^3495 ≤ 14091085574009^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3754996883 10000000000 14091085574009 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265666623/625000000 : ℝ), (4802213597/10000000000 : ℝ), (3754996883/10000000000 : ℝ)] ![(8270630181129/25000000000000 : ℝ), (9683827028153/25000000000000 : ℝ), (14091085574009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265666623/625000000 : ℝ)|^4519 ≤ (8270630181129/25000000000000 : ℝ)^3495
        have hw : |(265666623/625000000 : ℝ)|=(265666623/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4802213597/10000000000 : ℝ)|^4519 ≤ (9683827028153/25000000000000 : ℝ)^3495
        have hw : |(4802213597/10000000000 : ℝ)|=(4802213597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3754996883/10000000000 : ℝ)|^4519 ≤ (14091085574009/50000000000000 : ℝ)^3495
        have hw : |(3754996883/10000000000 : ℝ)|=(3754996883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1511_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25497/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (563/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (8343/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18343/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25497/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (563/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25497/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (563/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25497/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (563/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25497/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (563/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25497/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (563/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25497/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (563/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (563/20000 : ℝ) ^ (4517/1024 : ℝ) ≤ (14469159036089/100000000000000000000 : ℝ) := by
    have hpowers : (563/20000 : ℝ)^4517 ≤ (14469159036089/100000000000000000000 : ℝ)^1024 := by
      have hnat : (563 : ℕ)^4517*100000000000000000000^1024 ≤ 14469159036089^1024*20000^4517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        563 20000 14469159036089 100000000000000000000 4517 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (563/20000 : ℝ)) (X := (14469159036089/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25497/100000 : ℝ) ^ (4517/1024 : ℝ) ≤ (12047988047765561/5000000000000000000 : ℝ) := by
    have hpowers : (25497/100000 : ℝ)^4517 ≤ (12047988047765561/5000000000000000000 : ℝ)^1024 := by
      have hnat : (25497 : ℕ)^4517*5000000000000000000^1024 ≤ 12047988047765561^1024*100000^4517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25497 100000 12047988047765561 5000000000000000000 4517 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25497/100000 : ℝ)) (X := (12047988047765561/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000014469159036089/50000000000000000000 : ℝ) ≤ (10000000656029099/10000000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (50000014469159036089/50000000000000000000 : ℝ)^1024 ≤ (10000000656029099/10000000000000000 : ℝ)^4517 := by
      have hnat : (50000014469159036089 : ℕ)^1024*10000000000000000^4517 ≤ 10000000656029099^4517*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000014469159036089 50000000000000000000 10000000656029099 10000000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000656029099/10000000000000000 : ℝ)) (X := (50000014469159036089/50000000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100240974230114347309/100000000000000000000 : ℝ) ≤ (2501364445581273/2500000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (100240974230114347309/100000000000000000000 : ℝ)^1024 ≤ (2501364445581273/2500000000000000 : ℝ)^4517 := by
      have hnat : (100240974230114347309 : ℕ)^1024*2500000000000000^4517 ≤ 2501364445581273^4517*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100240974230114347309 100000000000000000000 2501364445581273 2500000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501364445581273/2500000000000000 : ℝ)) (X := (100240974230114347309/100000000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2512047988047765561/2500000000000000000 : ℝ) ≤ (2002182981724217/2000000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (2512047988047765561/2500000000000000000 : ℝ)^1024 ≤ (2002182981724217/2000000000000000 : ℝ)^4517 := by
      have hnat : (2512047988047765561 : ℕ)^1024*2000000000000000^4517 ≤ 2002182981724217^4517*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2512047988047765561 2500000000000000000 2002182981724217 2000000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002182981724217/2000000000000000 : ℝ)) (X := (2512047988047765561/2500000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14469159036089/100000000000000000000 : ℝ) ≤ ((14174330703687848933/14176250000000000000 : ℝ)+2*(5457126295993/2268200000000000 : ℝ)*(563/20000 : ℝ))^(4517/1024 : ℝ) := by
    rw [show (14174330703687848933/14176250000000000000 : ℝ)+2*(5457126295993/2268200000000000 : ℝ)*(563/20000 : ℝ)=(10000000656029099/10000000000000000 : ℝ) by norm_num, show 1+2*(14469159036089/100000000000000000000 : ℝ)=(50000014469159036089/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12047988047765561/5000000000000000000 : ℝ)+(14469159036089/100000000000000000000 : ℝ) ≤ ((14174330703687848933/14176250000000000000 : ℝ)+(5457126295993/2268200000000000 : ℝ)*((25497/100000 : ℝ)+(563/20000 : ℝ)))^(4517/1024 : ℝ) := by
    rw [show (14174330703687848933/14176250000000000000 : ℝ)+(5457126295993/2268200000000000 : ℝ)*((25497/100000 : ℝ)+(563/20000 : ℝ))=(2501364445581273/2500000000000000 : ℝ) by norm_num, show 1+(12047988047765561/5000000000000000000 : ℝ)+(14469159036089/100000000000000000000 : ℝ)=(100240974230114347309/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12047988047765561/5000000000000000000 : ℝ) ≤ ((14174330703687848933/14176250000000000000 : ℝ)+2*(5457126295993/2268200000000000 : ℝ)*(25497/100000 : ℝ))^(4517/1024 : ℝ) := by
    rw [show (14174330703687848933/14176250000000000000 : ℝ)+2*(5457126295993/2268200000000000 : ℝ)*(25497/100000 : ℝ)=(2002182981724217/2000000000000000 : ℝ) by norm_num, show 1+2*(12047988047765561/5000000000000000000 : ℝ)=(2512047988047765561/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14174330703687848933/14176250000000000000 : ℝ)*(X 1 0+X 2 0)+(5457126295993/2268200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (563/20000 : ℝ)) (hi := (25497/100000 : ℝ)) (c := (14174330703687848933/14176250000000000000 : ℝ)) (alpha := (5457126295993/2268200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14174330703687848933/14176250000000000000 : ℝ)*(X 0 1+X 2 1)+(5457126295993/2268200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (563/20000 : ℝ)) (hi := (25497/100000 : ℝ)) (c := (14174330703687848933/14176250000000000000 : ℝ)) (alpha := (5457126295993/2268200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14174330703687848933/14176250000000000000 : ℝ)*(X 0 2+X 1 2)+(5457126295993/2268200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (563/20000 : ℝ)) (hi := (25497/100000 : ℝ)) (c := (14174330703687848933/14176250000000000000 : ℝ)) (alpha := (5457126295993/2268200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1840875383/10000000000 : ℝ)*X 0 0+(1114234741/2000000000 : ℝ)*X 0 1+(1274588207/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5386804259/10000000000 : ℝ)*X 1 0+(-130617289/625000000 : ℝ)*X 1 1+(2549176113/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5386803711/10000000000 : ℝ)*X 2 0+(1274588209/2500000000 : ℝ)*X 2 1+(-2089876557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((265623571/625000000 : ℝ)*X 0 0+(3742805501/10000000000 : ℝ)*X 0 1+(4814212073/10000000000 : ℝ)*X 0 2+(265623571/625000000 : ℝ)*X 1 0+(3742805501/10000000000 : ℝ)*X 1 1+(4814212073/10000000000 : ℝ)*X 1 2+(265623571/625000000 : ℝ)*X 2 0+(3742805501/10000000000 : ℝ)*X 2 1+(4814212073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1841179089/10000000000 : ℝ)*X 0 0+(5103647983/10000000000 : ℝ)*X 0 1+(2782896631/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((657785037/1250000000 : ℝ)*X 1 0+(-405608947/2500000000 : ℝ)*X 1 1+(2782896719/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5262280083/10000000000 : ℝ)*X 2 0+(222631741/400000000 : ℝ)*X 2 1+(-405608991/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((265666623/625000000 : ℝ)*X 0 0+(4802213597/10000000000 : ℝ)*X 0 1+(3754996883/10000000000 : ℝ)*X 0 2+(265666623/625000000 : ℝ)*X 1 0+(4802213597/10000000000 : ℝ)*X 1 1+(3754996883/10000000000 : ℝ)*X 1 2+(265666623/625000000 : ℝ)*X 2 0+(4802213597/10000000000 : ℝ)*X 2 1+(3754996883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14923091943379246280512569/4027343750000000000000000000000 : ℝ) := by norm_num
    linear_combination (61382837/6250000000000 : ℝ)*(base19) + (71208347/10000000000000 : ℝ)*(base23) + (15069859/20000000000000 : ℝ)*(upper3) + (7391377/25000000000000 : ℝ)*(upper4) + (24239747/100000000000000 : ℝ)*(upper5) + (381042166935793/25000000000000 : ℝ)*(major0) + (381042166935793/25000000000000 : ℝ)*(major1) + (381042166935793/25000000000000 : ℝ)*(major2) + (2114972671415143/100000000000000 : ℝ)*(sp0) + (1057488826118499/50000000000000 : ℝ)*(sp1) + (2114977922278921/100000000000000 : ℝ)*(sp2) + (233338865296379/25000000000000 : ℝ)*(sp3) + (5962947247/100000000000000 : ℝ)*(sp4) + (3116423667/100000000000000 : ℝ)*(sp7) + (933358577609183/100000000000000 : ℝ)*(f.failure) + (211497863436239/10000000000000 : ℝ)*(f.sum) + (8925711322659/2577500000000000000000000000 : ℝ)*base65 + (224219714936490579/32218750000000000000000000000000 : ℝ)*base67 + (290693523189740579/32218750000000000000000000000000 : ℝ)*base69 + (154865312046709329/32218750000000000000000000000000 : ℝ)*base71 + (26172598473453/5155000000000000000000000000 : ℝ)*base73 + (144332330491928079/32218750000000000000000000000000 : ℝ)*base75 + (170455921708615579/32218750000000000000000000000000 : ℝ)*base77 + (251200235455384421/32218750000000000000000000000000 : ℝ)*base80 + (15197218462379/2577500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (87494473/10000000000000000000000 : ℝ)*base90 + (87494473/10000000000000000000000 : ℝ)*base92 + (87494473/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (268097201250152135049939/113410000000000000000000000000 : ℝ) := by norm_num
    linear_combination (495948459/100000000000000 : ℝ)*(base19) + (56355613/12500000000000 : ℝ)*(base23) + (2726983/4000000000000 : ℝ)*(upper3) + (10937549/50000000000000 : ℝ)*(lower4) + (1559366613244259/100000000000000 : ℝ)*(major0) + (1559366613244259/100000000000000 : ℝ)*(major1) + (1559366613244259/100000000000000 : ℝ)*(major2) + (2030441991/50000000000000 : ℝ)*(sp1) + (819880501/20000000000000 : ℝ)*(sp2) + (216247869/100000000000000 : ℝ)*(sp3) + (1081910162716813/50000000000000 : ℝ)*(sp4) + (67619242768787/3125000000000 : ℝ)*(sp5) + (270476971898277/12500000000000 : ℝ)*(sp6) + (238728151502051/25000000000000 : ℝ)*(sp7) + (954912822256073/100000000000000 : ℝ)*(f.failure) + (1081910162716813/50000000000000 : ℝ)*(f.sum) + (294201546551967/113410000000000000000000000000 : ℝ)*base65 + (4704658737766680603/1417625000000000000000000000000000 : ℝ)*base68 + (1622635759454930603/1417625000000000000000000000000000 : ℝ)*base70 + (9832488897912944397/1417625000000000000000000000000000 : ℝ)*base71 + (97606125539583/113410000000000000000000000000 : ℝ)*base74 + (5428457771028930603/1417625000000000000000000000000000 : ℝ)*base76 + (7987191696072819397/1417625000000000000000000000000000 : ℝ)*base77 + (2356489961395569397/1417625000000000000000000000000000 : ℝ)*base79 + (377101407919587/113410000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (22682063/10000000000000000000000 : ℝ)*base90 + (22682063/10000000000000000000000 : ℝ)*base92 + (22682063/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1511_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25497/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (563/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8343/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18343/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1511_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1511_s2_0 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1865509493/10000000000 : ℝ)*x 0 + (2729117881/5000000000 : ℝ)*x 1 + (20781343/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1865509493/10000000000 : ℝ)^4519 ≤ (11406395409787/100000000000000 : ℝ)^3495 := by
    have hnat : (1865509493 : ℕ)^4519*100000000000000^3495 ≤ 11406395409787^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865509493 10000000000 11406395409787 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2729117881/5000000000 : ℝ)^4519 ≤ (45710002490217/100000000000000 : ℝ)^3495 := by
    have hnat : (2729117881 : ℕ)^4519*100000000000000^3495 ≤ 45710002490217^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729117881 5000000000 45710002490217 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20781343/40000000 : ℝ)^4519 ≤ (5360450260603/12500000000000 : ℝ)^3495 := by
    have hnat : (20781343 : ℕ)^4519*12500000000000^3495 ≤ 5360450260603^3495*40000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20781343 40000000 5360450260603 12500000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1865509493/10000000000 : ℝ), (2729117881/5000000000 : ℝ), (20781343/40000000 : ℝ)] ![(11406395409787/100000000000000 : ℝ), (45710002490217/100000000000000 : ℝ), (5360450260603/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1865509493/10000000000 : ℝ)|^4519 ≤ (11406395409787/100000000000000 : ℝ)^3495
        have hw : |(-1865509493/10000000000 : ℝ)|=(1865509493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2729117881/5000000000 : ℝ)|^4519 ≤ (45710002490217/100000000000000 : ℝ)^3495
        have hw : |(2729117881/5000000000 : ℝ)|=(2729117881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20781343/40000000 : ℝ)|^4519 ≤ (5360450260603/12500000000000 : ℝ)^3495
        have hw : |(20781343/40000000 : ℝ)|=(20781343/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s2_1 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358116023/10000000000 : ℝ)*x 0 + (-2000853347/10000000000 : ℝ)*x 1 + (5195335703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358116023/10000000000 : ℝ)^4519 ≤ (44628817157711/100000000000000 : ℝ)^3495 := by
    have hnat : (5358116023 : ℕ)^4519*100000000000000^3495 ≤ 44628817157711^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358116023 10000000000 44628817157711 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000853347/10000000000 : ℝ)^4519 ≤ (1560947654777/12500000000000 : ℝ)^3495 := by
    have hnat : (2000853347 : ℕ)^4519*12500000000000^3495 ≤ 1560947654777^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000853347 10000000000 1560947654777 12500000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195335703/10000000000 : ℝ)^4519 ≤ (42883601583209/100000000000000 : ℝ)^3495 := by
    have hnat : (5195335703 : ℕ)^4519*100000000000000^3495 ≤ 42883601583209^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195335703 10000000000 42883601583209 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358116023/10000000000 : ℝ), (-2000853347/10000000000 : ℝ), (5195335703/10000000000 : ℝ)] ![(44628817157711/100000000000000 : ℝ), (1560947654777/12500000000000 : ℝ), (42883601583209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358116023/10000000000 : ℝ)|^4519 ≤ (44628817157711/100000000000000 : ℝ)^3495
        have hw : |(5358116023/10000000000 : ℝ)|=(5358116023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2000853347/10000000000 : ℝ)|^4519 ≤ (1560947654777/12500000000000 : ℝ)^3495
        have hw : |(-2000853347/10000000000 : ℝ)|=(2000853347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195335703/10000000000 : ℝ)|^4519 ≤ (42883601583209/100000000000000 : ℝ)^3495
        have hw : |(5195335703/10000000000 : ℝ)|=(5195335703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s2_2 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358115727/10000000000 : ℝ)*x 0 + (5195335869/10000000000 : ℝ)*x 1 + (-500213381/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358115727/10000000000 : ℝ)^4519 ≤ (22314406984959/50000000000000 : ℝ)^3495 := by
    have hnat : (5358115727 : ℕ)^4519*50000000000000^3495 ≤ 22314406984959^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358115727 10000000000 22314406984959 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195335869/10000000000 : ℝ)^4519 ≤ (42883603354871/100000000000000 : ℝ)^3495 := by
    have hnat : (5195335869 : ℕ)^4519*100000000000000^3495 ≤ 42883603354871^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195335869 10000000000 42883603354871 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (500213381/2500000000 : ℝ)^4519 ≤ (3121895666639/25000000000000 : ℝ)^3495 := by
    have hnat : (500213381 : ℕ)^4519*25000000000000^3495 ≤ 3121895666639^3495*2500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500213381 2500000000 3121895666639 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358115727/10000000000 : ℝ), (5195335869/10000000000 : ℝ), (-500213381/2500000000 : ℝ)] ![(22314406984959/50000000000000 : ℝ), (42883603354871/100000000000000 : ℝ), (3121895666639/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358115727/10000000000 : ℝ)|^4519 ≤ (22314406984959/50000000000000 : ℝ)^3495
        have hw : |(5358115727/10000000000 : ℝ)|=(5358115727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195335869/10000000000 : ℝ)|^4519 ≤ (42883603354871/100000000000000 : ℝ)^3495
        have hw : |(5195335869/10000000000 : ℝ)|=(5195335869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-500213381/2500000000 : ℝ)|^4519 ≤ (3121895666639/25000000000000 : ℝ)^3495
        have hw : |(-500213381/2500000000 : ℝ)|=(500213381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s2_3 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2133828867/5000000000 : ℝ)*x 0 + (397861833/1000000000 : ℝ)*x 1 + (228717241/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133828867/5000000000 : ℝ)^4519 ≤ (33253612568251/100000000000000 : ℝ)^3495 := by
    have hnat : (2133828867 : ℕ)^4519*100000000000000^3495 ≤ 33253612568251^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133828867 5000000000 33253612568251 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397861833/1000000000 : ℝ)^4519 ≤ (6074182566683/20000000000000 : ℝ)^3495 := by
    have hnat : (397861833 : ℕ)^4519*20000000000000^3495 ≤ 6074182566683^3495*1000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397861833 1000000000 6074182566683 20000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228717241/500000000 : ℝ)^4519 ≤ (18187737292951/50000000000000 : ℝ)^3495 := by
    have hnat : (228717241 : ℕ)^4519*50000000000000^3495 ≤ 18187737292951^3495*500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228717241 500000000 18187737292951 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133828867/5000000000 : ℝ), (397861833/1000000000 : ℝ), (228717241/500000000 : ℝ)] ![(33253612568251/100000000000000 : ℝ), (6074182566683/20000000000000 : ℝ), (18187737292951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133828867/5000000000 : ℝ)|^4519 ≤ (33253612568251/100000000000000 : ℝ)^3495
        have hw : |(2133828867/5000000000 : ℝ)|=(2133828867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(397861833/1000000000 : ℝ)|^4519 ≤ (6074182566683/20000000000000 : ℝ)^3495
        have hw : |(397861833/1000000000 : ℝ)|=(397861833/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(228717241/500000000 : ℝ)|^4519 ≤ (18187737292951/50000000000000 : ℝ)^3495
        have hw : |(228717241/500000000 : ℝ)|=(228717241/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s2_4 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-373112233/2000000000 : ℝ)*x 0 + (5196982719/10000000000 : ℝ)*x 1 + (2728287283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (373112233/2000000000 : ℝ)^4519 ≤ (5703401960111/50000000000000 : ℝ)^3495 := by
    have hnat : (373112233 : ℕ)^4519*50000000000000^3495 ≤ 5703401960111^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373112233 2000000000 5703401960111 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5196982719/10000000000 : ℝ)^4519 ≤ (42901180446309/100000000000000 : ℝ)^3495 := by
    have hnat : (5196982719 : ℕ)^4519*100000000000000^3495 ≤ 42901180446309^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196982719 10000000000 42901180446309 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728287283/5000000000 : ℝ)^4519 ≤ (4569201561891/10000000000000 : ℝ)^3495 := by
    have hnat : (2728287283 : ℕ)^4519*10000000000000^3495 ≤ 4569201561891^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728287283 5000000000 4569201561891 10000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-373112233/2000000000 : ℝ), (5196982719/10000000000 : ℝ), (2728287283/5000000000 : ℝ)] ![(5703401960111/50000000000000 : ℝ), (42901180446309/100000000000000 : ℝ), (4569201561891/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-373112233/2000000000 : ℝ)|^4519 ≤ (5703401960111/50000000000000 : ℝ)^3495
        have hw : |(-373112233/2000000000 : ℝ)|=(373112233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5196982719/10000000000 : ℝ)|^4519 ≤ (42901180446309/100000000000000 : ℝ)^3495
        have hw : |(5196982719/10000000000 : ℝ)|=(5196982719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728287283/5000000000 : ℝ)|^4519 ≤ (4569201561891/10000000000000 : ℝ)^3495
        have hw : |(2728287283/5000000000 : ℝ)|=(2728287283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s2_5 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057818599/2000000000 : ℝ)*x 0 + (-69584587/400000000 : ℝ)*x 1 + (2728287841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057818599/2000000000 : ℝ)^4519 ≤ (43886875808659/100000000000000 : ℝ)^3495 := by
    have hnat : (1057818599 : ℕ)^4519*100000000000000^3495 ≤ 43886875808659^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057818599 2000000000 43886875808659 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69584587/400000000 : ℝ)^4519 ≤ (10421096471057/100000000000000 : ℝ)^3495 := by
    have hnat : (69584587 : ℕ)^4519*100000000000000^3495 ≤ 10421096471057^3495*400000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69584587 400000000 10421096471057 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728287841/5000000000 : ℝ)^4519 ≤ (11423006925511/25000000000000 : ℝ)^3495 := by
    have hnat : (2728287841 : ℕ)^4519*25000000000000^3495 ≤ 11423006925511^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728287841 5000000000 11423006925511 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057818599/2000000000 : ℝ), (-69584587/400000000 : ℝ), (2728287841/5000000000 : ℝ)] ![(43886875808659/100000000000000 : ℝ), (10421096471057/100000000000000 : ℝ), (11423006925511/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057818599/2000000000 : ℝ)|^4519 ≤ (43886875808659/100000000000000 : ℝ)^3495
        have hw : |(1057818599/2000000000 : ℝ)|=(1057818599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-69584587/400000000 : ℝ)|^4519 ≤ (10421096471057/100000000000000 : ℝ)^3495
        have hw : |(-69584587/400000000 : ℝ)|=(69584587/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728287841/5000000000 : ℝ)|^4519 ≤ (11423006925511/25000000000000 : ℝ)^3495
        have hw : |(2728287841/5000000000 : ℝ)|=(2728287841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s2_6 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644546829/5000000000 : ℝ)*x 0 + (54565749/100000000 : ℝ)*x 1 + (-34792297/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644546829/5000000000 : ℝ)^4519 ≤ (10971720730453/25000000000000 : ℝ)^3495 := by
    have hnat : (2644546829 : ℕ)^4519*25000000000000^3495 ≤ 10971720730453^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644546829 5000000000 10971720730453 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54565749/100000000 : ℝ)^4519 ≤ (11423004808797/25000000000000 : ℝ)^3495 := by
    have hnat : (54565749 : ℕ)^4519*25000000000000^3495 ≤ 11423004808797^3495*100000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54565749 100000000 11423004808797 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34792297/200000000 : ℝ)^4519 ≤ (10421097826539/100000000000000 : ℝ)^3495 := by
    have hnat : (34792297 : ℕ)^4519*100000000000000^3495 ≤ 10421097826539^3495*200000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34792297 200000000 10421097826539 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644546829/5000000000 : ℝ), (54565749/100000000 : ℝ), (-34792297/200000000 : ℝ)] ![(10971720730453/25000000000000 : ℝ), (11423004808797/25000000000000 : ℝ), (10421097826539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644546829/5000000000 : ℝ)|^4519 ≤ (10971720730453/25000000000000 : ℝ)^3495
        have hw : |(2644546829/5000000000 : ℝ)|=(2644546829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54565749/100000000 : ℝ)|^4519 ≤ (11423004808797/25000000000000 : ℝ)^3495
        have hw : |(54565749/100000000 : ℝ)|=(54565749/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34792297/200000000 : ℝ)|^4519 ≤ (10421097826539/100000000000000 : ℝ)^3495
        have hw : |(-34792297/200000000 : ℝ)|=(34792297/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s2_7 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1066944261/2500000000 : ℝ)*x 0 + (2285308081/5000000000 : ℝ)*x 1 + (995594951/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066944261/2500000000 : ℝ)^4519 ≤ (6650962923929/20000000000000 : ℝ)^3495 := by
    have hnat : (1066944261 : ℕ)^4519*20000000000000^3495 ≤ 6650962923929^3495*2500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066944261 2500000000 6650962923929 20000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2285308081/5000000000 : ℝ)^4519 ≤ (36337141338837/100000000000000 : ℝ)^3495 := by
    have hnat : (2285308081 : ℕ)^4519*100000000000000^3495 ≤ 36337141338837^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285308081 5000000000 36337141338837 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (995594951/2500000000 : ℝ)^4519 ≤ (15204022014093/50000000000000 : ℝ)^3495 := by
    have hnat : (995594951 : ℕ)^4519*50000000000000^3495 ≤ 15204022014093^3495*2500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995594951 2500000000 15204022014093 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1066944261/2500000000 : ℝ), (2285308081/5000000000 : ℝ), (995594951/2500000000 : ℝ)] ![(6650962923929/20000000000000 : ℝ), (36337141338837/100000000000000 : ℝ), (15204022014093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1066944261/2500000000 : ℝ)|^4519 ≤ (6650962923929/20000000000000 : ℝ)^3495
        have hw : |(1066944261/2500000000 : ℝ)|=(1066944261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2285308081/5000000000 : ℝ)|^4519 ≤ (36337141338837/100000000000000 : ℝ)^3495
        have hw : |(2285308081/5000000000 : ℝ)|=(2285308081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(995594951/2500000000 : ℝ)|^4519 ≤ (15204022014093/50000000000000 : ℝ)^3495
        have hw : |(995594951/2500000000 : ℝ)|=(995594951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1511_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18343/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2087/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4/25 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18343/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8343/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18343/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8343/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18343/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8343/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18343/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8343/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18343/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8343/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18343/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8343/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8343/100000 : ℝ) ^ (4517/1024 : ℝ) ≤ (349011028218957/20000000000000000000 : ℝ) := by
    have hpowers : (8343/100000 : ℝ)^4517 ≤ (349011028218957/20000000000000000000 : ℝ)^1024 := by
      have hnat : (8343 : ℕ)^4517*20000000000000000000^1024 ≤ 349011028218957^1024*100000^4517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8343 100000 349011028218957 20000000000000000000 4517 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8343/100000 : ℝ)) (X := (349011028218957/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18343/100000 : ℝ) ^ (4517/1024 : ℝ) ≤ (7046605806680731/12500000000000000000 : ℝ) := by
    have hpowers : (18343/100000 : ℝ)^4517 ≤ (7046605806680731/12500000000000000000 : ℝ)^1024 := by
      have hnat : (18343 : ℕ)^4517*12500000000000000000^1024 ≤ 7046605806680731^1024*100000^4517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18343 100000 7046605806680731 12500000000000000000 4517 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18343/100000 : ℝ)) (X := (7046605806680731/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000349011028218957/10000000000000000000 : ℝ) ≤ (625004944964443/625000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (10000349011028218957/10000000000000000000 : ℝ)^1024 ≤ (625004944964443/625000000000000 : ℝ)^4517 := by
      have hnat : (10000349011028218957 : ℕ)^1024*625000000000000^4517 ≤ 625004944964443^4517*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000349011028218957 10000000000000000000 625004944964443 625000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625004944964443/625000000000000 : ℝ)) (X := (10000349011028218957/10000000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100058117901594540633/100000000000000000000 : ℝ) ≤ (10001317231847107/10000000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (100058117901594540633/100000000000000000000 : ℝ)^1024 ≤ (10001317231847107/10000000000000000 : ℝ)^4517 := by
      have hnat : (100058117901594540633 : ℕ)^1024*10000000000000000^4517 ≤ 10001317231847107^4517*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100058117901594540633 100000000000000000000 10001317231847107 10000000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001317231847107/10000000000000000 : ℝ)) (X := (100058117901594540633/100000000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6257046605806680731/6250000000000000000 : ℝ) ≤ (5001277672131563/5000000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (6257046605806680731/6250000000000000000 : ℝ)^1024 ≤ (5001277672131563/5000000000000000 : ℝ)^4517 := by
      have hnat : (6257046605806680731 : ℕ)^1024*5000000000000000^4517 ≤ 5001277672131563^4517*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6257046605806680731 6250000000000000000 5001277672131563 5000000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001277672131563/5000000000000000 : ℝ)) (X := (6257046605806680731/6250000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(349011028218957/20000000000000000000 : ℝ) ≤ ((49990066025268593483/50000000000000000000 : ℝ)+2*(1238112416019/1000000000000000 : ℝ)*(8343/100000 : ℝ))^(4517/1024 : ℝ) := by
    rw [show (49990066025268593483/50000000000000000000 : ℝ)+2*(1238112416019/1000000000000000 : ℝ)*(8343/100000 : ℝ)=(625004944964443/625000000000000 : ℝ) by norm_num, show 1+2*(349011028218957/20000000000000000000 : ℝ)=(10000349011028218957/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7046605806680731/12500000000000000000 : ℝ)+(349011028218957/20000000000000000000 : ℝ) ≤ ((49990066025268593483/50000000000000000000 : ℝ)+(1238112416019/1000000000000000 : ℝ)*((18343/100000 : ℝ)+(8343/100000 : ℝ)))^(4517/1024 : ℝ) := by
    rw [show (49990066025268593483/50000000000000000000 : ℝ)+(1238112416019/1000000000000000 : ℝ)*((18343/100000 : ℝ)+(8343/100000 : ℝ))=(10001317231847107/10000000000000000 : ℝ) by norm_num, show 1+(7046605806680731/12500000000000000000 : ℝ)+(349011028218957/20000000000000000000 : ℝ)=(100058117901594540633/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7046605806680731/12500000000000000000 : ℝ) ≤ ((49990066025268593483/50000000000000000000 : ℝ)+2*(1238112416019/1000000000000000 : ℝ)*(18343/100000 : ℝ))^(4517/1024 : ℝ) := by
    rw [show (49990066025268593483/50000000000000000000 : ℝ)+2*(1238112416019/1000000000000000 : ℝ)*(18343/100000 : ℝ)=(5001277672131563/5000000000000000 : ℝ) by norm_num, show 1+2*(7046605806680731/12500000000000000000 : ℝ)=(6257046605806680731/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (49990066025268593483/50000000000000000000 : ℝ)*(X 1 0+X 2 0)+(1238112416019/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (8343/100000 : ℝ)) (hi := (18343/100000 : ℝ)) (c := (49990066025268593483/50000000000000000000 : ℝ)) (alpha := (1238112416019/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (49990066025268593483/50000000000000000000 : ℝ)*(X 0 1+X 2 1)+(1238112416019/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (8343/100000 : ℝ)) (hi := (18343/100000 : ℝ)) (c := (49990066025268593483/50000000000000000000 : ℝ)) (alpha := (1238112416019/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (49990066025268593483/50000000000000000000 : ℝ)*(X 0 2+X 1 2)+(1238112416019/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (8343/100000 : ℝ)) (hi := (18343/100000 : ℝ)) (c := (49990066025268593483/50000000000000000000 : ℝ)) (alpha := (1238112416019/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1865509493/10000000000 : ℝ)*X 0 0+(2729117881/5000000000 : ℝ)*X 0 1+(20781343/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5358116023/10000000000 : ℝ)*X 1 0+(-2000853347/10000000000 : ℝ)*X 1 1+(5195335703/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5358115727/10000000000 : ℝ)*X 2 0+(5195335869/10000000000 : ℝ)*X 2 1+(-500213381/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2133828867/5000000000 : ℝ)*X 0 0+(397861833/1000000000 : ℝ)*X 0 1+(228717241/500000000 : ℝ)*X 0 2+(2133828867/5000000000 : ℝ)*X 1 0+(397861833/1000000000 : ℝ)*X 1 1+(228717241/500000000 : ℝ)*X 1 2+(2133828867/5000000000 : ℝ)*X 2 0+(397861833/1000000000 : ℝ)*X 2 1+(228717241/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-373112233/2000000000 : ℝ)*X 0 0+(5196982719/10000000000 : ℝ)*X 0 1+(2728287283/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057818599/2000000000 : ℝ)*X 1 0+(-69584587/400000000 : ℝ)*X 1 1+(2728287841/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644546829/5000000000 : ℝ)*X 2 0+(54565749/100000000 : ℝ)*X 2 1+(-34792297/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1066944261/2500000000 : ℝ)*X 0 0+(2285308081/5000000000 : ℝ)*X 0 1+(995594951/2500000000 : ℝ)*X 0 2+(1066944261/2500000000 : ℝ)*X 1 0+(2285308081/5000000000 : ℝ)*X 1 1+(995594951/2500000000 : ℝ)*X 1 2+(1066944261/2500000000 : ℝ)*X 2 0+(2285308081/5000000000 : ℝ)*X 2 1+(995594951/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5738956885028812430297205891/625000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (913141731/50000000000000 : ℝ)*(base19) + (364050081/25000000000000 : ℝ)*(base23) + (2678223/3125000000000 : ℝ)*(lower2) + (163561223/50000000000000 : ℝ)*(upper3) + (22317383/100000000000000 : ℝ)*(upper5) + (685301856396447/25000000000000 : ℝ)*(major0) + (685301856396447/25000000000000 : ℝ)*(major1) + (685301856396447/25000000000000 : ℝ)*(major2) + (380375483763647/10000000000000 : ℝ)*(sp0) + (95094334844113/2500000000000 : ℝ)*(sp1) + (3803773763847657/100000000000000 : ℝ)*(sp2) + (209828696484991/12500000000000 : ℝ)*(sp3) + (2547801439/12500000000000 : ℝ)*(sp4) + (2438291489/25000000000000 : ℝ)*(sp7) + (419659831261471/25000000000000 : ℝ)*(f.failure) + (1901887610023991/50000000000000 : ℝ)*(f.sum) + (27240057159493/12500000000000000000000000000 : ℝ)*base65 + (11696188961753204901/1250000000000000000000000000000000 : ℝ)*base67 + (3349352091753204901/1250000000000000000000000000000000 : ℝ)*base69 + (12396415466753204901/1250000000000000000000000000000000 : ℝ)*base71 + (4661599084493/12500000000000000000000000000 : ℝ)*base73 + (3210538006753204901/1250000000000000000000000000000000 : ℝ)*base75 + (22267793368003204901/1250000000000000000000000000000000 : ℝ)*base77 + (18766679380503204901/1250000000000000000000000000000000 : ℝ)*base79 + (17164896465507/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (11688201/2500000000000000000000 : ℝ)*base90 + (11688201/2500000000000000000000 : ℝ)*base92 + (11688201/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2208402611218338275290528761/250000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1440451/1562500000000 : ℝ)*(base23) + (324044651/100000000000000 : ℝ)*(lower2) + (87540527/50000000000000 : ℝ)*(upper3) + (137511099/100000000000000 : ℝ)*(lower4) + (277610596971289/10000000000000 : ℝ)*(major0) + (277610596971289/10000000000000 : ℝ)*(major1) + (277610596971289/10000000000000 : ℝ)*(major2) + (487721341/5000000000000 : ℝ)*(sp1) + (684131337/10000000000000 : ℝ)*(sp2) + (245996621/5000000000000 : ℝ)*(sp3) + (963050355092163/25000000000000 : ℝ)*(sp4) + (481523958242729/12500000000000 : ℝ)*(sp5) + (1926097243433209/50000000000000 : ℝ)*(sp6) + (850002652335507/50000000000000 : ℝ)*(sp7) + (850005112301717/50000000000000 : ℝ)*(f.failure) + (963050355092163/25000000000000 : ℝ)*(f.sum) + (27177929901509/5000000000000000000000000000 : ℝ)*base66 + (130603041311940413/500000000000000000000000000000000 : ℝ)*base68 + (5456832557311940413/500000000000000000000000000000000 : ℝ)*base70 + (1299768511311940413/500000000000000000000000000000000 : ℝ)*base72 + (770588038491/5000000000000000000000000000 : ℝ)*base73 + (784378016688059587/500000000000000000000000000000000 : ℝ)*base75 + (8168640178311940413/500000000000000000000000000000000 : ℝ)*base78 + (40225070987688059587/500000000000000000000000000000000 : ℝ)*base79 + (12893054298491/5000000000000000000000000000 : ℝ)*base81 + (23716573/5000000000000000000000 : ℝ)*base89 + (23716573/5000000000000000000000 : ℝ)*base91 + (23716573/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1511_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18343/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2087/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4/25 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1511_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1511_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2087/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4/25 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1511_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1511_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1511_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2087/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4/25 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1511_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

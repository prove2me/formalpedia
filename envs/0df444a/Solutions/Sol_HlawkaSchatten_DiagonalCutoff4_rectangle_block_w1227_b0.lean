-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1227_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:13:21.388817+00:00
-- url     : https://prove2.me/submissions/0d563ccc-4b9c-43b7-9b8d-427d3ef0c36e

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
theorem support_rectangle_w1227_s0_0 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1865197283/10000000000 : ℝ)*x 0 + (603489243/1000000000 : ℝ)*x 1 + (4791127427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1865197283/10000000000 : ℝ)^2105 ≤ (10872545408081/100000000000000 : ℝ)^1593 := by
    have hnat : (1865197283 : ℕ)^2105*100000000000000^1593 ≤ 10872545408081^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865197283 10000000000 10872545408081 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (603489243/1000000000 : ℝ)^2105 ≤ (51306852389869/100000000000000 : ℝ)^1593 := by
    have hnat : (603489243 : ℕ)^2105*100000000000000^1593 ≤ 51306852389869^1593*1000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603489243 1000000000 51306852389869 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4791127427/10000000000 : ℝ)^2105 ≤ (18910301095921/50000000000000 : ℝ)^1593 := by
    have hnat : (4791127427 : ℕ)^2105*50000000000000^1593 ≤ 18910301095921^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4791127427 10000000000 18910301095921 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1865197283/10000000000 : ℝ), (603489243/1000000000 : ℝ), (4791127427/10000000000 : ℝ)] ![(10872545408081/100000000000000 : ℝ), (51306852389869/100000000000000 : ℝ), (18910301095921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1865197283/10000000000 : ℝ)|^2105 ≤ (10872545408081/100000000000000 : ℝ)^1593
        have hw : |(-1865197283/10000000000 : ℝ)|=(1865197283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(603489243/1000000000 : ℝ)|^2105 ≤ (51306852389869/100000000000000 : ℝ)^1593
        have hw : |(603489243/1000000000 : ℝ)|=(603489243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4791127427/10000000000 : ℝ)|^2105 ≤ (18910301095921/50000000000000 : ℝ)^1593
        have hw : |(4791127427/10000000000 : ℝ)|=(4791127427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s0_1 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5512004571/10000000000 : ℝ)*x 0 + (-1288316941/5000000000 : ℝ)*x 1 + (239556369/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5512004571/10000000000 : ℝ)^2105 ≤ (45516082203793/100000000000000 : ℝ)^1593 := by
    have hnat : (5512004571 : ℕ)^2105*100000000000000^1593 ≤ 45516082203793^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512004571 10000000000 45516082203793 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1288316941/5000000000 : ℝ)^2105 ≤ (16663316075999/100000000000000 : ℝ)^1593 := by
    have hnat : (1288316941 : ℕ)^2105*100000000000000^1593 ≤ 16663316075999^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288316941 5000000000 16663316075999 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (239556369/500000000 : ℝ)^2105 ≤ (37820601701583/100000000000000 : ℝ)^1593 := by
    have hnat : (239556369 : ℕ)^2105*100000000000000^1593 ≤ 37820601701583^1593*500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239556369 500000000 37820601701583 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5512004571/10000000000 : ℝ), (-1288316941/5000000000 : ℝ), (239556369/500000000 : ℝ)] ![(45516082203793/100000000000000 : ℝ), (16663316075999/100000000000000 : ℝ), (37820601701583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5512004571/10000000000 : ℝ)|^2105 ≤ (45516082203793/100000000000000 : ℝ)^1593
        have hw : |(5512004571/10000000000 : ℝ)|=(5512004571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1288316941/5000000000 : ℝ)|^2105 ≤ (16663316075999/100000000000000 : ℝ)^1593
        have hw : |(-1288316941/5000000000 : ℝ)|=(1288316941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(239556369/500000000 : ℝ)|^2105 ≤ (37820601701583/100000000000000 : ℝ)^1593
        have hw : |(239556369/500000000 : ℝ)|=(239556369/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s0_2 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1378001131/2500000000 : ℝ)*x 0 + (4791127437/10000000000 : ℝ)*x 1 + (-1288316937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1378001131/2500000000 : ℝ)^2105 ≤ (711188776421/1562500000000 : ℝ)^1593 := by
    have hnat : (1378001131 : ℕ)^2105*1562500000000^1593 ≤ 711188776421^1593*2500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378001131 2500000000 711188776421 1562500000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4791127437/10000000000 : ℝ)^2105 ≤ (4727575287019/12500000000000 : ℝ)^1593 := by
    have hnat : (4791127437 : ℕ)^2105*12500000000000^1593 ≤ 4727575287019^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4791127437 10000000000 4727575287019 12500000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1288316937/5000000000 : ℝ)^2105 ≤ (8331658003817/50000000000000 : ℝ)^1593 := by
    have hnat : (1288316937 : ℕ)^2105*50000000000000^1593 ≤ 8331658003817^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288316937 5000000000 8331658003817 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1378001131/2500000000 : ℝ), (4791127437/10000000000 : ℝ), (-1288316937/5000000000 : ℝ)] ![(711188776421/1562500000000 : ℝ), (4727575287019/12500000000000 : ℝ), (8331658003817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1378001131/2500000000 : ℝ)|^2105 ≤ (711188776421/1562500000000 : ℝ)^1593
        have hw : |(1378001131/2500000000 : ℝ)|=(1378001131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4791127437/10000000000 : ℝ)|^2105 ≤ (4727575287019/12500000000000 : ℝ)^1593
        have hw : |(4791127437/10000000000 : ℝ)|=(4791127437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1288316937/5000000000 : ℝ)|^2105 ≤ (8331658003817/50000000000000 : ℝ)^1593
        have hw : |(-1288316937/5000000000 : ℝ)|=(1288316937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s0_3 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4194202187/10000000000 : ℝ)*x 0 + (3117463307/10000000000 : ℝ)*x 1 + (1408305657/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4194202187/10000000000 : ℝ)^2105 ≤ (31722437178663/100000000000000 : ℝ)^1593 := by
    have hnat : (4194202187 : ℕ)^2105*100000000000000^1593 ≤ 31722437178663^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4194202187 10000000000 31722437178663 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3117463307/10000000000 : ℝ)^2105 ≤ (5358534104007/25000000000000 : ℝ)^1593 := by
    have hnat : (3117463307 : ℕ)^2105*25000000000000^1593 ≤ 5358534104007^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3117463307 10000000000 5358534104007 25000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1408305657/2500000000 : ℝ)^2105 ≤ (4684342639419/10000000000000 : ℝ)^1593 := by
    have hnat : (1408305657 : ℕ)^2105*10000000000000^1593 ≤ 4684342639419^1593*2500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1408305657 2500000000 4684342639419 10000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4194202187/10000000000 : ℝ), (3117463307/10000000000 : ℝ), (1408305657/2500000000 : ℝ)] ![(31722437178663/100000000000000 : ℝ), (5358534104007/25000000000000 : ℝ), (4684342639419/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4194202187/10000000000 : ℝ)|^2105 ≤ (31722437178663/100000000000000 : ℝ)^1593
        have hw : |(4194202187/10000000000 : ℝ)|=(4194202187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3117463307/10000000000 : ℝ)|^2105 ≤ (5358534104007/25000000000000 : ℝ)^1593
        have hw : |(3117463307/10000000000 : ℝ)|=(3117463307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1408305657/2500000000 : ℝ)|^2105 ≤ (4684342639419/10000000000000 : ℝ)^1593
        have hw : |(1408305657/2500000000 : ℝ)|=(1408305657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s0_4 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1826267/9765625 : ℝ)*x 0 + (4823164807/10000000000 : ℝ)*x 1 + (6001723093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1826267/9765625 : ℝ)^2105 ≤ (10910305508961/100000000000000 : ℝ)^1593 := by
    have hnat : (1826267 : ℕ)^2105*100000000000000^1593 ≤ 10910305508961^1593*9765625^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826267 9765625 10910305508961 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4823164807/10000000000 : ℝ)^2105 ≤ (1907757175747/5000000000000 : ℝ)^1593 := by
    have hnat : (4823164807 : ℕ)^2105*5000000000000^1593 ≤ 1907757175747^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4823164807 10000000000 1907757175747 5000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6001723093/10000000000 : ℝ)^2105 ≤ (10186910191271/20000000000000 : ℝ)^1593 := by
    have hnat : (6001723093 : ℕ)^2105*20000000000000^1593 ≤ 10186910191271^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6001723093 10000000000 10186910191271 20000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1826267/9765625 : ℝ), (4823164807/10000000000 : ℝ), (6001723093/10000000000 : ℝ)] ![(10910305508961/100000000000000 : ℝ), (1907757175747/5000000000000 : ℝ), (10186910191271/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1826267/9765625 : ℝ)|^2105 ≤ (10910305508961/100000000000000 : ℝ)^1593
        have hw : |(-1826267/9765625 : ℝ)|=(1826267/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4823164807/10000000000 : ℝ)|^2105 ≤ (1907757175747/5000000000000 : ℝ)^1593
        have hw : |(4823164807/10000000000 : ℝ)|=(4823164807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6001723093/10000000000 : ℝ)|^2105 ≤ (10186910191271/20000000000000 : ℝ)^1593
        have hw : |(6001723093/10000000000 : ℝ)|=(6001723093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s0_5 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5173657851/10000000000 : ℝ)*x 0 + (-341509643/2500000000 : ℝ)*x 1 + (750215377/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173657851/10000000000 : ℝ)^2105 ≤ (4186108933297/10000000000000 : ℝ)^1593 := by
    have hnat : (5173657851 : ℕ)^2105*10000000000000^1593 ≤ 4186108933297^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173657851 10000000000 4186108933297 10000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341509643/2500000000 : ℝ)^2105 ≤ (1801090139849/25000000000000 : ℝ)^1593 := by
    have hnat : (341509643 : ℕ)^2105*25000000000000^1593 ≤ 1801090139849^1593*2500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341509643 2500000000 1801090139849 25000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (750215377/1250000000 : ℝ)^2105 ≤ (50934550092853/100000000000000 : ℝ)^1593 := by
    have hnat : (750215377 : ℕ)^2105*100000000000000^1593 ≤ 50934550092853^1593*1250000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750215377 1250000000 50934550092853 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173657851/10000000000 : ℝ), (-341509643/2500000000 : ℝ), (750215377/1250000000 : ℝ)] ![(4186108933297/10000000000000 : ℝ), (1801090139849/25000000000000 : ℝ), (50934550092853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173657851/10000000000 : ℝ)|^2105 ≤ (4186108933297/10000000000000 : ℝ)^1593
        have hw : |(5173657851/10000000000 : ℝ)|=(5173657851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-341509643/2500000000 : ℝ)|^2105 ≤ (1801090139849/25000000000000 : ℝ)^1593
        have hw : |(-341509643/2500000000 : ℝ)|=(341509643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(750215377/1250000000 : ℝ)|^2105 ≤ (50934550092853/100000000000000 : ℝ)^1593
        have hw : |(750215377/1250000000 : ℝ)|=(750215377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s0_6 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5173657827/10000000000 : ℝ)*x 0 + (1200344619/2000000000 : ℝ)*x 1 + (-683019241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173657827/10000000000 : ℝ)^2105 ≤ (2616318067273/6250000000000 : ℝ)^1593 := by
    have hnat : (5173657827 : ℕ)^2105*6250000000000^1593 ≤ 2616318067273^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173657827 10000000000 2616318067273 6250000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1200344619/2000000000 : ℝ)^2105 ≤ (1591704718087/3125000000000 : ℝ)^1593 := by
    have hnat : (1200344619 : ℕ)^2105*3125000000000^1593 ≤ 1591704718087^1593*2000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200344619 2000000000 1591704718087 3125000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683019241/5000000000 : ℝ)^2105 ≤ (7204359932189/100000000000000 : ℝ)^1593 := by
    have hnat : (683019241 : ℕ)^2105*100000000000000^1593 ≤ 7204359932189^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683019241 5000000000 7204359932189 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173657827/10000000000 : ℝ), (1200344619/2000000000 : ℝ), (-683019241/5000000000 : ℝ)] ![(2616318067273/6250000000000 : ℝ), (1591704718087/3125000000000 : ℝ), (7204359932189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173657827/10000000000 : ℝ)|^2105 ≤ (2616318067273/6250000000000 : ℝ)^1593
        have hw : |(5173657827/10000000000 : ℝ)|=(5173657827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1200344619/2000000000 : ℝ)|^2105 ≤ (1591704718087/3125000000000 : ℝ)^1593
        have hw : |(1200344619/2000000000 : ℝ)|=(1200344619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-683019241/5000000000 : ℝ)|^2105 ≤ (7204359932189/100000000000000 : ℝ)^1593
        have hw : |(-683019241/5000000000 : ℝ)|=(683019241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s0_7 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4204113347/10000000000 : ℝ)*x 0 + (222736811/400000000 : ℝ)*x 1 + (3184555263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4204113347/10000000000 : ℝ)^2105 ≤ (31821530138293/100000000000000 : ℝ)^1593 := by
    have hnat : (4204113347 : ℕ)^2105*100000000000000^1593 ≤ 31821530138293^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204113347 10000000000 31821530138293 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222736811/400000000 : ℝ)^2105 ≤ (461326825151/1000000000000 : ℝ)^1593 := by
    have hnat : (222736811 : ℕ)^2105*1000000000000^1593 ≤ 461326825151^1593*400000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222736811 400000000 461326825151 1000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3184555263/10000000000 : ℝ)^2105 ≤ (22045787332949/100000000000000 : ℝ)^1593 := by
    have hnat : (3184555263 : ℕ)^2105*100000000000000^1593 ≤ 22045787332949^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3184555263 10000000000 22045787332949 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4204113347/10000000000 : ℝ), (222736811/400000000 : ℝ), (3184555263/10000000000 : ℝ)] ![(31821530138293/100000000000000 : ℝ), (461326825151/1000000000000 : ℝ), (22045787332949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4204113347/10000000000 : ℝ)|^2105 ≤ (31821530138293/100000000000000 : ℝ)^1593
        have hw : |(4204113347/10000000000 : ℝ)|=(4204113347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(222736811/400000000 : ℝ)|^2105 ≤ (461326825151/1000000000000 : ℝ)^1593
        have hw : |(222736811/400000000 : ℝ)|=(222736811/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3184555263/10000000000 : ℝ)|^2105 ≤ (22045787332949/100000000000000 : ℝ)^1593
        have hw : |(3184555263/10000000000 : ℝ)|=(3184555263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1227_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75567419/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (379/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6873/25000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8419/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8419 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8419*1^2048 ≤ 0^2048*1^8419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8419 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8419/2048 : ℝ) ≤ (18068511949779487/781250000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8419 ≤ (18068511949779487/781250000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8419*781250000000000000^2048 ≤ 18068511949779487^2048*5^8419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 18068511949779487 781250000000000000 8419 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (18068511949779487/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8419/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8419 := by
      have hnat : (1 : ℕ)^2048*1^8419 ≤ 1^8419*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (799318511949779487/781250000000000000 : ℝ) ≤ (5027887253630727/5000000000000000 : ℝ) ^ (8419/2048 : ℝ) := by
    have hpowers : (799318511949779487/781250000000000000 : ℝ)^2048 ≤ (5027887253630727/5000000000000000 : ℝ)^8419 := by
      have hnat : (799318511949779487 : ℕ)^2048*5000000000000000^8419 ≤ 5027887253630727^8419*781250000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        799318511949779487 781250000000000000 5027887253630727 5000000000000000 2048 8419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5027887253630727/5000000000000000 : ℝ)) (X := (799318511949779487/781250000000000000 : ℝ)) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (408693511949779487/390625000000000000 : ℝ) ≤ (2527887253630727/2500000000000000 : ℝ) ^ (8419/2048 : ℝ) := by
    have hpowers : (408693511949779487/390625000000000000 : ℝ)^2048 ≤ (2527887253630727/2500000000000000 : ℝ)^8419 := by
      have hnat : (408693511949779487 : ℕ)^2048*2500000000000000^8419 ≤ 2527887253630727^8419*390625000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        408693511949779487 390625000000000000 2527887253630727 2500000000000000 2048 8419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2527887253630727/2500000000000000 : ℝ)) (X := (408693511949779487/390625000000000000 : ℝ)) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(27887253630727/2000000000000000 : ℝ)*(0 : ℝ))^(8419/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(27887253630727/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18068511949779487/781250000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(27887253630727/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8419/2048 : ℝ) := by
    rw [show (1 : ℝ)+(27887253630727/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5027887253630727/5000000000000000 : ℝ) by norm_num, show 1+(18068511949779487/781250000000000000 : ℝ)+(0 : ℝ)=(799318511949779487/781250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18068511949779487/781250000000000000 : ℝ) ≤ ((1 : ℝ)+2*(27887253630727/2000000000000000 : ℝ)*(2/5 : ℝ))^(8419/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(27887253630727/2000000000000000 : ℝ)*(2/5 : ℝ)=(2527887253630727/2500000000000000 : ℝ) by norm_num, show 1+2*(18068511949779487/781250000000000000 : ℝ)=(408693511949779487/390625000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(27887253630727/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8419/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27887253630727/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(27887253630727/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8419/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27887253630727/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(27887253630727/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8419/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27887253630727/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1865197283/10000000000 : ℝ)*X 0 0+(603489243/1000000000 : ℝ)*X 0 1+(4791127427/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5512004571/10000000000 : ℝ)*X 1 0+(-1288316941/5000000000 : ℝ)*X 1 1+(239556369/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1378001131/2500000000 : ℝ)*X 2 0+(4791127437/10000000000 : ℝ)*X 2 1+(-1288316937/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4194202187/10000000000 : ℝ)*X 0 0+(3117463307/10000000000 : ℝ)*X 0 1+(1408305657/2500000000 : ℝ)*X 0 2+(4194202187/10000000000 : ℝ)*X 1 0+(3117463307/10000000000 : ℝ)*X 1 1+(1408305657/2500000000 : ℝ)*X 1 2+(4194202187/10000000000 : ℝ)*X 2 0+(3117463307/10000000000 : ℝ)*X 2 1+(1408305657/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1826267/9765625 : ℝ)*X 0 0+(4823164807/10000000000 : ℝ)*X 0 1+(6001723093/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5173657851/10000000000 : ℝ)*X 1 0+(-341509643/2500000000 : ℝ)*X 1 1+(750215377/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5173657827/10000000000 : ℝ)*X 2 0+(1200344619/2000000000 : ℝ)*X 2 1+(-683019241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4204113347/10000000000 : ℝ)*X 0 0+(222736811/400000000 : ℝ)*X 0 1+(3184555263/10000000000 : ℝ)*X 0 2+(4204113347/10000000000 : ℝ)*X 1 0+(222736811/400000000 : ℝ)*X 1 1+(3184555263/10000000000 : ℝ)*X 1 2+(4204113347/10000000000 : ℝ)*X 2 0+(222736811/400000000 : ℝ)*X 2 1+(3184555263/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (330134317554640696604433/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38978267/50000000000000 : ℝ)*(base1) + (1611936069/100000000000000 : ℝ)*(base19) + (1495549623/100000000000000 : ℝ)*(base23) + (13691339/12500000000000 : ℝ)*(base24) + (182644037/50000000000000 : ℝ)*(upper3) + (600759199711231/100000000000000 : ℝ)*(major0) + (600759199711231/100000000000000 : ℝ)*(major1) + (600759199711231/100000000000000 : ℝ)*(major2) + (100501982170293/12500000000000 : ℝ)*(sp0) + (402008873019451/50000000000000 : ℝ)*(sp1) + (160803550578927/20000000000000 : ℝ)*(sp2) + (49686993022357/12500000000000 : ℝ)*(sp3) + (89464229/2500000000000 : ℝ)*(sp4) + (55984451/2000000000000 : ℝ)*(sp7) + (19874941067897/5000000000000 : ℝ)*(f.failure) + (80401935797497/10000000000000 : ℝ)*(f.sum) + (465673720405063/100000000000000000000000000000 : ℝ)*base66 + (522934507805063/200000000000000000000000000000 : ℝ)*base68 + (1145236288605063/200000000000000000000000000000 : ℝ)*base70 + (1606516084205063/200000000000000000000000000000 : ℝ)*base72 + (256321339205063/100000000000000000000000000000 : ℝ)*base74 + (2391699487005063/200000000000000000000000000000 : ℝ)*base76 + (1056017623805063/200000000000000000000000000000 : ℝ)*base78 + (606612998805063/200000000000000000000000000000 : ℝ)*base80 + (557932114205063/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2547843/250000000000000000000 : ℝ)*base89 + (2547843/250000000000000000000 : ℝ)*base91 + (2547843/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13944639581480018036007/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10672011/100000000000000 : ℝ)*(base1) + (236266429/50000000000000 : ℝ)*(base19) + (467369741/100000000000000 : ℝ)*(base23) + (49556259/100000000000000 : ℝ)*(upper3) + (15282153/20000000000000 : ℝ)*(upper5) + (158497664932703/25000000000000 : ℝ)*(major0) + (158497664932703/25000000000000 : ℝ)*(major1) + (158497664932703/25000000000000 : ℝ)*(major2) + (261104967/25000000000000 : ℝ)*(sp1) + (1025657101/100000000000000 : ℝ)*(sp2) + (169698895900597/20000000000000 : ℝ)*(sp4) + (106061618984781/12500000000000 : ℝ)*(sp5) + (212123243951033/25000000000000 : ℝ)*(sp6) + (20974338279361/5000000000000 : ℝ)*(sp7) + (419486776259231/100000000000000 : ℝ)*(f.failure) + (424247234415487/50000000000000 : ℝ)*(f.sum) + (10298306465081/25000000000000000000000000000 : ℝ)*base65 + (161628148215081/50000000000000000000000000000 : ℝ)*base67 + (324571294715081/50000000000000000000000000000 : ℝ)*base69 + (207486517165081/50000000000000000000000000000 : ℝ)*base71 + (41513533734919/25000000000000000000000000000 : ℝ)*base74 + (474310834565081/50000000000000000000000000000 : ℝ)*base75 + (182240296565081/50000000000000000000000000000 : ℝ)*base77 + (528010159115081/50000000000000000000000000000 : ℝ)*base79 + (23627568915081/25000000000000000000000000000 : ℝ)*base81 + (38405211/5000000000000000000000 : ℝ)*base90 + (38405211/5000000000000000000000 : ℝ)*base92 + (38405211/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1227_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75567419/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (379/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6873/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1227_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1227_s1_0 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2063703719/10000000000 : ℝ)*x 0 + (5679378633/10000000000 : ℝ)*x 1 + (2509787227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2063703719/10000000000 : ℝ)^2105 ≤ (6213564232259/50000000000000 : ℝ)^1593 := by
    have hnat : (2063703719 : ℕ)^2105*50000000000000^1593 ≤ 6213564232259^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063703719 10000000000 6213564232259 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5679378633/10000000000 : ℝ)^2105 ≤ (47351266144161/100000000000000 : ℝ)^1593 := by
    have hnat : (5679378633 : ℕ)^2105*100000000000000^1593 ≤ 47351266144161^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5679378633 10000000000 47351266144161 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2509787227/5000000000 : ℝ)^2105 ≤ (20110802687123/50000000000000 : ℝ)^1593 := by
    have hnat : (2509787227 : ℕ)^2105*50000000000000^1593 ≤ 20110802687123^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2509787227 5000000000 20110802687123 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2063703719/10000000000 : ℝ), (5679378633/10000000000 : ℝ), (2509787227/5000000000 : ℝ)] ![(6213564232259/50000000000000 : ℝ), (47351266144161/100000000000000 : ℝ), (20110802687123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2063703719/10000000000 : ℝ)|^2105 ≤ (6213564232259/50000000000000 : ℝ)^1593
        have hw : |(-2063703719/10000000000 : ℝ)|=(2063703719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5679378633/10000000000 : ℝ)|^2105 ≤ (47351266144161/100000000000000 : ℝ)^1593
        have hw : |(5679378633/10000000000 : ℝ)|=(5679378633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2509787227/5000000000 : ℝ)|^2105 ≤ (20110802687123/50000000000000 : ℝ)^1593
        have hw : |(2509787227/5000000000 : ℝ)|=(2509787227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s1_1 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (54144711/100000000 : ℝ)*x 0 + (-1209133563/5000000000 : ℝ)*x 1 + (5019574493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54144711/100000000 : ℝ)^2105 ≤ (277842916727/625000000000 : ℝ)^1593 := by
    have hnat : (54144711 : ℕ)^2105*625000000000^1593 ≤ 277842916727^1593*100000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54144711 100000000 277842916727 625000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1209133563/5000000000 : ℝ)^2105 ≤ (7661763757917/50000000000000 : ℝ)^1593 := by
    have hnat : (1209133563 : ℕ)^2105*50000000000000^1593 ≤ 7661763757917^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209133563 5000000000 7661763757917 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5019574493/10000000000 : ℝ)^2105 ≤ (40221605787193/100000000000000 : ℝ)^1593 := by
    have hnat : (5019574493 : ℕ)^2105*100000000000000^1593 ≤ 40221605787193^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5019574493 10000000000 40221605787193 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54144711/100000000 : ℝ), (-1209133563/5000000000 : ℝ), (5019574493/10000000000 : ℝ)] ![(277842916727/625000000000 : ℝ), (7661763757917/50000000000000 : ℝ), (40221605787193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54144711/100000000 : ℝ)|^2105 ≤ (277842916727/625000000000 : ℝ)^1593
        have hw : |(54144711/100000000 : ℝ)|=(54144711/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1209133563/5000000000 : ℝ)|^2105 ≤ (7661763757917/50000000000000 : ℝ)^1593
        have hw : |(-1209133563/5000000000 : ℝ)|=(1209133563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5019574493/10000000000 : ℝ)|^2105 ≤ (40221605787193/100000000000000 : ℝ)^1593
        have hw : |(5019574493/10000000000 : ℝ)|=(5019574493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s1_2 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5414471147/10000000000 : ℝ)*x 0 + (5019574473/10000000000 : ℝ)*x 1 + (-241826709/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5414471147/10000000000 : ℝ)^2105 ≤ (8890973437247/20000000000000 : ℝ)^1593 := by
    have hnat : (5414471147 : ℕ)^2105*20000000000000^1593 ≤ 8890973437247^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414471147 10000000000 8890973437247 20000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5019574473/10000000000 : ℝ)^2105 ≤ (1608864223017/4000000000000 : ℝ)^1593 := by
    have hnat : (5019574473 : ℕ)^2105*4000000000000^1593 ≤ 1608864223017^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5019574473 10000000000 1608864223017 4000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (241826709/1000000000 : ℝ)^2105 ≤ (15323527214399/100000000000000 : ℝ)^1593 := by
    have hnat : (241826709 : ℕ)^2105*100000000000000^1593 ≤ 15323527214399^1593*1000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241826709 1000000000 15323527214399 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5414471147/10000000000 : ℝ), (5019574473/10000000000 : ℝ), (-241826709/1000000000 : ℝ)] ![(8890973437247/20000000000000 : ℝ), (1608864223017/4000000000000 : ℝ), (15323527214399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5414471147/10000000000 : ℝ)|^2105 ≤ (8890973437247/20000000000000 : ℝ)^1593
        have hw : |(5414471147/10000000000 : ℝ)|=(5414471147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5019574473/10000000000 : ℝ)|^2105 ≤ (1608864223017/4000000000000 : ℝ)^1593
        have hw : |(5019574473/10000000000 : ℝ)|=(5019574473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-241826709/1000000000 : ℝ)|^2105 ≤ (15323527214399/100000000000000 : ℝ)^1593
        have hw : |(-241826709/1000000000 : ℝ)|=(241826709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s1_3 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1077539501/2500000000 : ℝ)*x 0 + (461593503/1250000000 : ℝ)*x 1 + (5027332307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077539501/2500000000 : ℝ)^2105 ≤ (6577290892587/20000000000000 : ℝ)^1593 := by
    have hnat : (1077539501 : ℕ)^2105*20000000000000^1593 ≤ 6577290892587^1593*2500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077539501 2500000000 6577290892587 20000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (461593503/1250000000 : ℝ)^2105 ≤ (26809776787319/100000000000000 : ℝ)^1593 := by
    have hnat : (461593503 : ℕ)^2105*100000000000000^1593 ≤ 26809776787319^1593*1250000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461593503 1250000000 26809776787319 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5027332307/10000000000 : ℝ)^2105 ≤ (40303768733169/100000000000000 : ℝ)^1593 := by
    have hnat : (5027332307 : ℕ)^2105*100000000000000^1593 ≤ 40303768733169^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027332307 10000000000 40303768733169 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077539501/2500000000 : ℝ), (461593503/1250000000 : ℝ), (5027332307/10000000000 : ℝ)] ![(6577290892587/20000000000000 : ℝ), (26809776787319/100000000000000 : ℝ), (40303768733169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077539501/2500000000 : ℝ)|^2105 ≤ (6577290892587/20000000000000 : ℝ)^1593
        have hw : |(1077539501/2500000000 : ℝ)|=(1077539501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(461593503/1250000000 : ℝ)|^2105 ≤ (26809776787319/100000000000000 : ℝ)^1593
        have hw : |(461593503/1250000000 : ℝ)|=(461593503/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5027332307/10000000000 : ℝ)|^2105 ≤ (40303768733169/100000000000000 : ℝ)^1593
        have hw : |(5027332307/10000000000 : ℝ)|=(5027332307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s1_4 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2064398773/10000000000 : ℝ)*x 0 + (2514146317/5000000000 : ℝ)*x 1 + (2835246557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2064398773/10000000000 : ℝ)^2105 ≤ (6216329720527/50000000000000 : ℝ)^1593 := by
    have hnat : (2064398773 : ℕ)^2105*50000000000000^1593 ≤ 6216329720527^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064398773 10000000000 6216329720527 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2514146317/5000000000 : ℝ)^2105 ≤ (40313942384743/100000000000000 : ℝ)^1593 := by
    have hnat : (2514146317 : ℕ)^2105*100000000000000^1593 ≤ 40313942384743^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2514146317 5000000000 40313942384743 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2835246557/5000000000 : ℝ)^2105 ≤ (9450679631551/20000000000000 : ℝ)^1593 := by
    have hnat : (2835246557 : ℕ)^2105*20000000000000^1593 ≤ 9450679631551^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2835246557 5000000000 9450679631551 20000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2064398773/10000000000 : ℝ), (2514146317/5000000000 : ℝ), (2835246557/5000000000 : ℝ)] ![(6216329720527/50000000000000 : ℝ), (40313942384743/100000000000000 : ℝ), (9450679631551/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2064398773/10000000000 : ℝ)|^2105 ≤ (6216329720527/50000000000000 : ℝ)^1593
        have hw : |(-2064398773/10000000000 : ℝ)|=(2064398773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2514146317/5000000000 : ℝ)|^2105 ≤ (40313942384743/100000000000000 : ℝ)^1593
        have hw : |(2514146317/5000000000 : ℝ)|=(2514146317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2835246557/5000000000 : ℝ)|^2105 ≤ (9450679631551/20000000000000 : ℝ)^1593
        have hw : |(2835246557/5000000000 : ℝ)|=(2835246557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s1_5 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5244606871/10000000000 : ℝ)*x 0 + (-883673897/5000000000 : ℝ)*x 1 + (5670493507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5244606871/10000000000 : ℝ)^2105 ≤ (2131066285627/5000000000000 : ℝ)^1593 := by
    have hnat : (5244606871 : ℕ)^2105*5000000000000^1593 ≤ 2131066285627^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244606871 10000000000 2131066285627 5000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (883673897/5000000000 : ℝ)^2105 ≤ (2531317947247/25000000000000 : ℝ)^1593 := by
    have hnat : (883673897 : ℕ)^2105*25000000000000^1593 ≤ 2531317947247^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883673897 5000000000 2531317947247 25000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5670493507/10000000000 : ℝ)^2105 ≤ (9450680497059/20000000000000 : ℝ)^1593 := by
    have hnat : (5670493507 : ℕ)^2105*20000000000000^1593 ≤ 9450680497059^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5670493507 10000000000 9450680497059 20000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5244606871/10000000000 : ℝ), (-883673897/5000000000 : ℝ), (5670493507/10000000000 : ℝ)] ![(2131066285627/5000000000000 : ℝ), (2531317947247/25000000000000 : ℝ), (9450680497059/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5244606871/10000000000 : ℝ)|^2105 ≤ (2131066285627/5000000000000 : ℝ)^1593
        have hw : |(5244606871/10000000000 : ℝ)|=(5244606871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-883673897/5000000000 : ℝ)|^2105 ≤ (2531317947247/25000000000000 : ℝ)^1593
        have hw : |(-883673897/5000000000 : ℝ)|=(883673897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5670493507/10000000000 : ℝ)|^2105 ≤ (9450680497059/20000000000000 : ℝ)^1593
        have hw : |(5670493507/10000000000 : ℝ)|=(5670493507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s1_6 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1048921431/2000000000 : ℝ)*x 0 + (5670494247/10000000000 : ℝ)*x 1 + (-353469263/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048921431/2000000000 : ℝ)^2105 ≤ (42621328762321/100000000000000 : ℝ)^1593 := by
    have hnat : (1048921431 : ℕ)^2105*100000000000000^1593 ≤ 42621328762321^1593*2000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048921431 2000000000 42621328762321 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5670494247/10000000000 : ℝ)^2105 ≤ (11813352658461/25000000000000 : ℝ)^1593 := by
    have hnat : (5670494247 : ℕ)^2105*25000000000000^1593 ≤ 11813352658461^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5670494247 10000000000 11813352658461 25000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (353469263/2000000000 : ℝ)^2105 ≤ (10125260592313/100000000000000 : ℝ)^1593 := by
    have hnat : (353469263 : ℕ)^2105*100000000000000^1593 ≤ 10125260592313^1593*2000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353469263 2000000000 10125260592313 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048921431/2000000000 : ℝ), (5670494247/10000000000 : ℝ), (-353469263/2000000000 : ℝ)] ![(42621328762321/100000000000000 : ℝ), (11813352658461/25000000000000 : ℝ), (10125260592313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048921431/2000000000 : ℝ)|^2105 ≤ (42621328762321/100000000000000 : ℝ)^1593
        have hw : |(1048921431/2000000000 : ℝ)|=(1048921431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5670494247/10000000000 : ℝ)|^2105 ≤ (11813352658461/25000000000000 : ℝ)^1593
        have hw : |(5670494247/10000000000 : ℝ)|=(5670494247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-353469263/2000000000 : ℝ)|^2105 ≤ (10125260592313/100000000000000 : ℝ)^1593
        have hw : |(-353469263/2000000000 : ℝ)|=(353469263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s1_7 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4311562069/10000000000 : ℝ)*x 0 + (1252424713/2500000000 : ℝ)*x 1 + (1855359471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311562069/10000000000 : ℝ)^2105 ≤ (4112576428393/12500000000000 : ℝ)^1593 := by
    have hnat : (4311562069 : ℕ)^2105*12500000000000^1593 ≤ 4112576428393^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311562069 10000000000 4112576428393 12500000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1252424713/2500000000 : ℝ)^2105 ≤ (40117071990243/100000000000000 : ℝ)^1593 := by
    have hnat : (1252424713 : ℕ)^2105*100000000000000^1593 ≤ 40117071990243^1593*2500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252424713 2500000000 40117071990243 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1855359471/5000000000 : ℝ)^2105 ≤ (13491158286269/50000000000000 : ℝ)^1593 := by
    have hnat : (1855359471 : ℕ)^2105*50000000000000^1593 ≤ 13491158286269^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855359471 5000000000 13491158286269 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311562069/10000000000 : ℝ), (1252424713/2500000000 : ℝ), (1855359471/5000000000 : ℝ)] ![(4112576428393/12500000000000 : ℝ), (40117071990243/100000000000000 : ℝ), (13491158286269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311562069/10000000000 : ℝ)|^2105 ≤ (4112576428393/12500000000000 : ℝ)^1593
        have hw : |(4311562069/10000000000 : ℝ)|=(4311562069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1252424713/2500000000 : ℝ)|^2105 ≤ (40117071990243/100000000000000 : ℝ)^1593
        have hw : |(1252424713/2500000000 : ℝ)|=(1252424713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1855359471/5000000000 : ℝ)|^2105 ≤ (13491158286269/50000000000000 : ℝ)^1593
        have hw : |(1855359471/5000000000 : ℝ)|=(1855359471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s1_8 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (3938281/10000000000 : ℝ)*x 0 + (1098244369/2000000000 : ℝ)*x 1 + (1583802969/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3938281/10000000000 : ℝ)^2105 ≤ (3169693931/100000000000000 : ℝ)^1593 := by
    have hnat : (3938281 : ℕ)^2105*100000000000000^1593 ≤ 3169693931^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3938281 10000000000 3169693931 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098244369/2000000000 : ℝ)^2105 ≤ (11322361317383/25000000000000 : ℝ)^1593 := by
    have hnat : (1098244369 : ℕ)^2105*25000000000000^1593 ≤ 11322361317383^1593*2000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098244369 2000000000 11322361317383 25000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1583802969/2500000000 : ℝ)^2105 ≤ (1709605781833/3125000000000 : ℝ)^1593 := by
    have hnat : (1583802969 : ℕ)^2105*3125000000000^1593 ≤ 1709605781833^1593*2500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583802969 2500000000 1709605781833 3125000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3938281/10000000000 : ℝ), (1098244369/2000000000 : ℝ), (1583802969/2500000000 : ℝ)] ![(3169693931/100000000000000 : ℝ), (11322361317383/25000000000000 : ℝ), (1709605781833/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3938281/10000000000 : ℝ)|^2105 ≤ (3169693931/100000000000000 : ℝ)^1593
        have hw : |(3938281/10000000000 : ℝ)|=(3938281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1098244369/2000000000 : ℝ)|^2105 ≤ (11322361317383/25000000000000 : ℝ)^1593
        have hw : |(1098244369/2000000000 : ℝ)|=(1098244369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1583802969/2500000000 : ℝ)|^2105 ≤ (1709605781833/3125000000000 : ℝ)^1593
        have hw : |(1583802969/2500000000 : ℝ)|=(1583802969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s1_9 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (199463781/2000000000 : ℝ)*x 0 + (-544337419/1250000000 : ℝ)*x 1 + (3478402097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (199463781/2000000000 : ℝ)^2105 ≤ (594241761741/12500000000000 : ℝ)^1593 := by
    have hnat : (199463781 : ℕ)^2105*12500000000000^1593 ≤ 594241761741^1593*2000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199463781 2000000000 594241761741 12500000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544337419/1250000000 : ℝ)^2105 ≤ (33336278343471/100000000000000 : ℝ)^1593 := by
    have hnat : (544337419 : ℕ)^2105*100000000000000^1593 ≤ 33336278343471^1593*1250000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544337419 1250000000 33336278343471 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3478402097/5000000000 : ℝ)^2105 ≤ (6190978754681/10000000000000 : ℝ)^1593 := by
    have hnat : (3478402097 : ℕ)^2105*10000000000000^1593 ≤ 6190978754681^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3478402097 5000000000 6190978754681 10000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(199463781/2000000000 : ℝ), (-544337419/1250000000 : ℝ), (3478402097/5000000000 : ℝ)] ![(594241761741/12500000000000 : ℝ), (33336278343471/100000000000000 : ℝ), (6190978754681/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(199463781/2000000000 : ℝ)|^2105 ≤ (594241761741/12500000000000 : ℝ)^1593
        have hw : |(199463781/2000000000 : ℝ)|=(199463781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-544337419/1250000000 : ℝ)|^2105 ≤ (33336278343471/100000000000000 : ℝ)^1593
        have hw : |(-544337419/1250000000 : ℝ)|=(544337419/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3478402097/5000000000 : ℝ)|^2105 ≤ (6190978754681/10000000000000 : ℝ)^1593
        have hw : |(3478402097/5000000000 : ℝ)|=(3478402097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s1_10 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (249330299/2500000000 : ℝ)*x 0 + (1391361767/2000000000 : ℝ)*x 1 + (-435469253/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (249330299/2500000000 : ℝ)^2105 ≤ (950789704881/20000000000000 : ℝ)^1593 := by
    have hnat : (249330299 : ℕ)^2105*20000000000000^1593 ≤ 950789704881^1593*2500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249330299 2500000000 950789704881 20000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1391361767/2000000000 : ℝ)^2105 ≤ (61909842122279/100000000000000 : ℝ)^1593 := by
    have hnat : (1391361767 : ℕ)^2105*100000000000000^1593 ≤ 61909842122279^1593*2000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1391361767 2000000000 61909842122279 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (435469253/1000000000 : ℝ)^2105 ≤ (33336209334291/100000000000000 : ℝ)^1593 := by
    have hnat : (435469253 : ℕ)^2105*100000000000000^1593 ≤ 33336209334291^1593*1000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435469253 1000000000 33336209334291 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(249330299/2500000000 : ℝ), (1391361767/2000000000 : ℝ), (-435469253/1000000000 : ℝ)] ![(950789704881/20000000000000 : ℝ), (61909842122279/100000000000000 : ℝ), (33336209334291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(249330299/2500000000 : ℝ)|^2105 ≤ (950789704881/20000000000000 : ℝ)^1593
        have hw : |(249330299/2500000000 : ℝ)|=(249330299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1391361767/2000000000 : ℝ)|^2105 ≤ (61909842122279/100000000000000 : ℝ)^1593
        have hw : |(1391361767/2000000000 : ℝ)|=(1391361767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-435469253/1000000000 : ℝ)|^2105 ≤ (33336209334291/100000000000000 : ℝ)^1593
        have hw : |(-435469253/1000000000 : ℝ)|=(435469253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s1_11 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1906111233/10000000000 : ℝ)*x 0 + (5791267951/10000000000 : ℝ)*x 1 + (2509869823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1906111233/10000000000 : ℝ)^2105 ≤ (11188798607/100000000000 : ℝ)^1593 := by
    have hnat : (1906111233 : ℕ)^2105*100000000000^1593 ≤ 11188798607^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906111233 10000000000 11188798607 100000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5791267951/10000000000 : ℝ)^2105 ≤ (24293923436093/50000000000000 : ℝ)^1593 := by
    have hnat : (5791267951 : ℕ)^2105*50000000000000^1593 ≤ 24293923436093^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5791267951 10000000000 24293923436093 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2509869823/5000000000 : ℝ)^2105 ≤ (40223354496369/100000000000000 : ℝ)^1593 := by
    have hnat : (2509869823 : ℕ)^2105*100000000000000^1593 ≤ 40223354496369^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2509869823 5000000000 40223354496369 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1906111233/10000000000 : ℝ), (5791267951/10000000000 : ℝ), (2509869823/5000000000 : ℝ)] ![(11188798607/100000000000 : ℝ), (24293923436093/50000000000000 : ℝ), (40223354496369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1906111233/10000000000 : ℝ)|^2105 ≤ (11188798607/100000000000 : ℝ)^1593
        have hw : |(1906111233/10000000000 : ℝ)|=(1906111233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5791267951/10000000000 : ℝ)|^2105 ≤ (24293923436093/50000000000000 : ℝ)^1593
        have hw : |(5791267951/10000000000 : ℝ)|=(5791267951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2509869823/5000000000 : ℝ)|^2105 ≤ (40223354496369/100000000000000 : ℝ)^1593
        have hw : |(2509869823/5000000000 : ℝ)|=(2509869823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1227_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75567419/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6873/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (379/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (191/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10031/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6873/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (379/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6873/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (379/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6873/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (379/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6873/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (379/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6873/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (379/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6873/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (379/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (379/50000 : ℝ) ^ (8419/2048 : ℝ) ≤ (192158539219/100000000000000000000 : ℝ) := by
    have hpowers : (379/50000 : ℝ)^8419 ≤ (192158539219/100000000000000000000 : ℝ)^2048 := by
      have hnat : (379 : ℕ)^8419*100000000000000000000^2048 ≤ 192158539219^2048*50000^8419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        379 50000 192158539219 100000000000000000000 8419 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (379/50000 : ℝ)) (X := (192158539219/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (6873/25000 : ℝ) ^ (8419/2048 : ℝ) ≤ (9901410232045881/2000000000000000000 : ℝ) := by
    have hpowers : (6873/25000 : ℝ)^8419 ≤ (9901410232045881/2000000000000000000 : ℝ)^2048 := by
      have hnat : (6873 : ℕ)^8419*2000000000000000000^2048 ≤ 9901410232045881^2048*25000^8419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6873 25000 9901410232045881 2000000000000000000 8419 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6873/25000 : ℝ)) (X := (9901410232045881/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000192158539219/50000000000000000000 : ℝ) ≤ (10000000009348871/10000000000000000 : ℝ) ^ (8419/2048 : ℝ) := by
    have hpowers : (50000000192158539219/50000000000000000000 : ℝ)^2048 ≤ (10000000009348871/10000000000000000 : ℝ)^8419 := by
      have hnat : (50000000192158539219 : ℕ)^2048*10000000000000000^8419 ≤ 10000000009348871^8419*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000192158539219 50000000000000000000 10000000009348871 10000000000000000 2048 8419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000009348871/10000000000000000 : ℝ)) (X := (50000000192158539219/50000000000000000000 : ℝ)) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100495070703760833269/100000000000000000000 : ℝ) ≤ (10012020561127443/10000000000000000 : ℝ) ^ (8419/2048 : ℝ) := by
    have hpowers : (100495070703760833269/100000000000000000000 : ℝ)^2048 ≤ (10012020561127443/10000000000000000 : ℝ)^8419 := by
      have hnat : (100495070703760833269 : ℕ)^2048*10000000000000000^8419 ≤ 10012020561127443^8419*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100495070703760833269 100000000000000000000 10012020561127443 10000000000000000 2048 8419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012020561127443/10000000000000000 : ℝ)) (X := (100495070703760833269/100000000000000000000 : ℝ)) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1009901410232045881/1000000000000000000 : ℝ) ≤ (2004808222581203/2000000000000000 : ℝ) ^ (8419/2048 : ℝ) := by
    have hpowers : (1009901410232045881/1000000000000000000 : ℝ)^2048 ≤ (2004808222581203/2000000000000000 : ℝ)^8419 := by
      have hnat : (1009901410232045881 : ℕ)^2048*2000000000000000^8419 ≤ 2004808222581203^8419*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1009901410232045881 1000000000000000000 2004808222581203 2000000000000000 2048 8419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004808222581203/2000000000000000 : ℝ)) (X := (1009901410232045881/1000000000000000000 : ℝ)) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(192158539219/100000000000000000000 : ℝ) ≤ ((133660888546718201081/133670000000000000000 : ℝ)+2*(3005137944643/668350000000000 : ℝ)*(379/50000 : ℝ))^(8419/2048 : ℝ) := by
    rw [show (133660888546718201081/133670000000000000000 : ℝ)+2*(3005137944643/668350000000000 : ℝ)*(379/50000 : ℝ)=(10000000009348871/10000000000000000 : ℝ) by norm_num, show 1+2*(192158539219/100000000000000000000 : ℝ)=(50000000192158539219/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9901410232045881/2000000000000000000 : ℝ)+(192158539219/100000000000000000000 : ℝ) ≤ ((133660888546718201081/133670000000000000000 : ℝ)+(3005137944643/668350000000000 : ℝ)*((6873/25000 : ℝ)+(379/50000 : ℝ)))^(8419/2048 : ℝ) := by
    rw [show (133660888546718201081/133670000000000000000 : ℝ)+(3005137944643/668350000000000 : ℝ)*((6873/25000 : ℝ)+(379/50000 : ℝ))=(10012020561127443/10000000000000000 : ℝ) by norm_num, show 1+(9901410232045881/2000000000000000000 : ℝ)+(192158539219/100000000000000000000 : ℝ)=(100495070703760833269/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9901410232045881/2000000000000000000 : ℝ) ≤ ((133660888546718201081/133670000000000000000 : ℝ)+2*(3005137944643/668350000000000 : ℝ)*(6873/25000 : ℝ))^(8419/2048 : ℝ) := by
    rw [show (133660888546718201081/133670000000000000000 : ℝ)+2*(3005137944643/668350000000000 : ℝ)*(6873/25000 : ℝ)=(2004808222581203/2000000000000000 : ℝ) by norm_num, show 1+2*(9901410232045881/2000000000000000000 : ℝ)=(1009901410232045881/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (133660888546718201081/133670000000000000000 : ℝ)*(X 1 0+X 2 0)+(3005137944643/668350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8419/2048 : ℝ)) (lo := (379/50000 : ℝ)) (hi := (6873/25000 : ℝ)) (c := (133660888546718201081/133670000000000000000 : ℝ)) (alpha := (3005137944643/668350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (133660888546718201081/133670000000000000000 : ℝ)*(X 0 1+X 2 1)+(3005137944643/668350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8419/2048 : ℝ)) (lo := (379/50000 : ℝ)) (hi := (6873/25000 : ℝ)) (c := (133660888546718201081/133670000000000000000 : ℝ)) (alpha := (3005137944643/668350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (133660888546718201081/133670000000000000000 : ℝ)*(X 0 2+X 1 2)+(3005137944643/668350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8419/2048 : ℝ)) (lo := (379/50000 : ℝ)) (hi := (6873/25000 : ℝ)) (c := (133660888546718201081/133670000000000000000 : ℝ)) (alpha := (3005137944643/668350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2063703719/10000000000 : ℝ)*X 0 0+(5679378633/10000000000 : ℝ)*X 0 1+(2509787227/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((54144711/100000000 : ℝ)*X 1 0+(-1209133563/5000000000 : ℝ)*X 1 1+(5019574493/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5414471147/10000000000 : ℝ)*X 2 0+(5019574473/10000000000 : ℝ)*X 2 1+(-241826709/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1077539501/2500000000 : ℝ)*X 0 0+(461593503/1250000000 : ℝ)*X 0 1+(5027332307/10000000000 : ℝ)*X 0 2+(1077539501/2500000000 : ℝ)*X 1 0+(461593503/1250000000 : ℝ)*X 1 1+(5027332307/10000000000 : ℝ)*X 1 2+(1077539501/2500000000 : ℝ)*X 2 0+(461593503/1250000000 : ℝ)*X 2 1+(5027332307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2064398773/10000000000 : ℝ)*X 0 0+(2514146317/5000000000 : ℝ)*X 0 1+(2835246557/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5244606871/10000000000 : ℝ)*X 1 0+(-883673897/5000000000 : ℝ)*X 1 1+(5670493507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1048921431/2000000000 : ℝ)*X 2 0+(5670494247/10000000000 : ℝ)*X 2 1+(-353469263/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4311562069/10000000000 : ℝ)*X 0 0+(1252424713/2500000000 : ℝ)*X 0 1+(1855359471/5000000000 : ℝ)*X 0 2+(4311562069/10000000000 : ℝ)*X 1 0+(1252424713/2500000000 : ℝ)*X 1 1+(1855359471/5000000000 : ℝ)*X 1 2+(4311562069/10000000000 : ℝ)*X 2 0+(1252424713/2500000000 : ℝ)*X 2 1+(1855359471/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((3938281/10000000000 : ℝ)*X 0 0+(1098244369/2000000000 : ℝ)*X 0 1+(1583802969/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((199463781/2000000000 : ℝ)*X 1 0+(-544337419/1250000000 : ℝ)*X 1 1+(3478402097/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((249330299/2500000000 : ℝ)*X 2 0+(1391361767/2000000000 : ℝ)*X 2 1+(-435469253/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1906111233/10000000000 : ℝ)*X 0 0+(5791267951/10000000000 : ℝ)*X 0 1+(2509869823/5000000000 : ℝ)*X 0 2+(1906111233/10000000000 : ℝ)*X 1 0+(5791267951/10000000000 : ℝ)*X 1 1+(2509869823/5000000000 : ℝ)*X 1 2+(1906111233/10000000000 : ℝ)*X 2 0+(5791267951/10000000000 : ℝ)*X 2 1+(2509869823/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41138144689384078908435673407/3341750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (566226177567183/50000000000000 : ℝ)*(major0) + (566226177567183/50000000000000 : ℝ)*(major1) + (566226177567183/50000000000000 : ℝ)*(major2) + (15156032420769/1000000000000 : ℝ)*(sp0) + (1515603517462461/100000000000000 : ℝ)*(sp1) + (37890087981601/2500000000000 : ℝ)*(sp2) + (187324463892753/25000000000000 : ℝ)*(sp3) + (200175029/50000000000000 : ℝ)*(sp4) + (664550223/100000000000000 : ℝ)*(sp5) + (80738079/12500000000000 : ℝ)*(sp6) + (654946881/50000000000000 : ℝ)*(sp8) + (192577009/25000000000000 : ℝ)*(sp9) + (49197003/6250000000000 : ℝ)*(sp10) + (373007917/25000000000000 : ℝ)*(sp11) + (18732483690067/2500000000000 : ℝ)*(f.failure) + (18945061904009/1250000000000 : ℝ)*(f.sum) + (44504963019281/16708750000000000000000000000 : ℝ)*base66 + (53646331284038475177/6683500000000000000000000000000000 : ℝ)*base68 + (65279571352841475177/6683500000000000000000000000000000 : ℝ)*base70 + (23471349267602975177/6683500000000000000000000000000000 : ℝ)*base72 + (34312706656971/16708750000000000000000000000 : ℝ)*base74 + (64554288586340475177/6683500000000000000000000000000000 : ℝ)*base76 + (67373425044075475177/6683500000000000000000000000000000 : ℝ)*base78 + (55135854470695475177/6683500000000000000000000000000000 : ℝ)*base80 + (14570658554759/4177187500000000000000000000 : ℝ)*base82 + (1627073/125000000000000000000 : ℝ)*base89 + (1627073/125000000000000000000 : ℝ)*base91 + (1627073/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3508782493559316513131549091/1670875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (581745724088737/50000000000000 : ℝ)*(major0) + (581745724088737/50000000000000 : ℝ)*(major1) + (581745724088737/50000000000000 : ℝ)*(major2) + (532190489/100000000000000 : ℝ)*(sp1) + (373037381/12500000000000 : ℝ)*(sp2) + (780681431/100000000000000 : ℝ)*(sp3) + (1557145168455653/100000000000000 : ℝ)*(sp4) + (778572652995459/50000000000000 : ℝ)*(sp5) + (97321415730829/6250000000000 : ℝ)*(sp6) + (384917801427931/50000000000000 : ℝ)*(sp7) + (2396789/250000000000 : ℝ)*(sp8) + (144494923/50000000000000 : ℝ)*(sp9) + (24558947/5000000000000 : ℝ)*(sp10) + (315647493/100000000000000 : ℝ)*(sp11) + (384918349592393/50000000000000 : ℝ)*(f.failure) + (389286531792813/25000000000000 : ℝ)*(f.sum) + (95026630029197/33417500000000000000000000000 : ℝ)*base65 + (38988213037653975303/6683500000000000000000000000000000 : ℝ)*base68 + (35021717715491975303/6683500000000000000000000000000000 : ℝ)*base70 + (51049681981014975303/6683500000000000000000000000000000 : ℝ)*base72 + (60149451674209/66835000000000000000000000000 : ℝ)*base73 + (36495039048839475303/6683500000000000000000000000000000 : ℝ)*base76 + (33575538282832975303/6683500000000000000000000000000000 : ℝ)*base78 + (2317509157711024697/6683500000000000000000000000000000 : ℝ)*base79 + (159136377080199/66835000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (8956333/2500000000000000000000 : ℝ)*base90 + (8956333/2500000000000000000000 : ℝ)*base92 + (8956333/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1227_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75567419/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6873/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (379/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (191/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10031/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1227_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1227_s2_0 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-16503909/78125000 : ℝ)*x 0 + (2747678987/5000000000 : ℝ)*x 1 + (5172488907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16503909/78125000 : ℝ)^2105 ≤ (12816880186217/100000000000000 : ℝ)^1593 := by
    have hnat : (16503909 : ℕ)^2105*100000000000000^1593 ≤ 12816880186217^1593*78125000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16503909 78125000 12816880186217 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2747678987/5000000000 : ℝ)^2105 ≤ (45334528078603/100000000000000 : ℝ)^1593 := by
    have hnat : (2747678987 : ℕ)^2105*100000000000000^1593 ≤ 45334528078603^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747678987 5000000000 45334528078603 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5172488907/10000000000 : ℝ)^2105 ≤ (41848591719693/100000000000000 : ℝ)^1593 := by
    have hnat : (5172488907 : ℕ)^2105*100000000000000^1593 ≤ 41848591719693^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172488907 10000000000 41848591719693 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16503909/78125000 : ℝ), (2747678987/5000000000 : ℝ), (5172488907/10000000000 : ℝ)] ![(12816880186217/100000000000000 : ℝ), (45334528078603/100000000000000 : ℝ), (41848591719693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16503909/78125000 : ℝ)|^2105 ≤ (12816880186217/100000000000000 : ℝ)^1593
        have hw : |(-16503909/78125000 : ℝ)|=(16503909/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2747678987/5000000000 : ℝ)|^2105 ≤ (45334528078603/100000000000000 : ℝ)^1593
        have hw : |(2747678987/5000000000 : ℝ)|=(2747678987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5172488907/10000000000 : ℝ)|^2105 ≤ (41848591719693/100000000000000 : ℝ)^1593
        have hw : |(5172488907/10000000000 : ℝ)|=(5172488907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s2_1 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (167821721/312500000 : ℝ)*x 0 + (-2279831993/10000000000 : ℝ)*x 1 + (2586244423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167821721/312500000 : ℝ)^2105 ≤ (43976219608127/100000000000000 : ℝ)^1593 := by
    have hnat : (167821721 : ℕ)^2105*100000000000000^1593 ≤ 43976219608127^1593*312500000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167821721 312500000 43976219608127 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2279831993/10000000000 : ℝ)^2105 ≤ (283503786271/2000000000000 : ℝ)^1593 := by
    have hnat : (2279831993 : ℕ)^2105*2000000000000^1593 ≤ 283503786271^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279831993 10000000000 283503786271 2000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2586244423/5000000000 : ℝ)^2105 ≤ (41848591067543/100000000000000 : ℝ)^1593 := by
    have hnat : (2586244423 : ℕ)^2105*100000000000000^1593 ≤ 41848591067543^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586244423 5000000000 41848591067543 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167821721/312500000 : ℝ), (-2279831993/10000000000 : ℝ), (2586244423/5000000000 : ℝ)] ![(43976219608127/100000000000000 : ℝ), (283503786271/2000000000000 : ℝ), (41848591067543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167821721/312500000 : ℝ)|^2105 ≤ (43976219608127/100000000000000 : ℝ)^1593
        have hw : |(167821721/312500000 : ℝ)|=(167821721/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2279831993/10000000000 : ℝ)|^2105 ≤ (283503786271/2000000000000 : ℝ)^1593
        have hw : |(-2279831993/10000000000 : ℝ)|=(2279831993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2586244423/5000000000 : ℝ)|^2105 ≤ (41848591067543/100000000000000 : ℝ)^1593
        have hw : |(2586244423/5000000000 : ℝ)|=(2586244423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s2_2 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2685147441/5000000000 : ℝ)*x 0 + (5172489013/10000000000 : ℝ)*x 1 + (-91193281/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685147441/5000000000 : ℝ)^2105 ≤ (4397621755219/10000000000000 : ℝ)^1593 := by
    have hnat : (2685147441 : ℕ)^2105*10000000000000^1593 ≤ 4397621755219^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685147441 5000000000 4397621755219 10000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5172489013/10000000000 : ℝ)^2105 ≤ (41848592852937/100000000000000 : ℝ)^1593 := by
    have hnat : (5172489013 : ℕ)^2105*100000000000000^1593 ≤ 41848592852937^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172489013 10000000000 41848592852937 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91193281/400000000 : ℝ)^2105 ≤ (14175189576463/100000000000000 : ℝ)^1593 := by
    have hnat : (91193281 : ℕ)^2105*100000000000000^1593 ≤ 14175189576463^1593*400000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91193281 400000000 14175189576463 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685147441/5000000000 : ℝ), (5172489013/10000000000 : ℝ), (-91193281/400000000 : ℝ)] ![(4397621755219/10000000000000 : ℝ), (41848592852937/100000000000000 : ℝ), (14175189576463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685147441/5000000000 : ℝ)|^2105 ≤ (4397621755219/10000000000000 : ℝ)^1593
        have hw : |(2685147441/5000000000 : ℝ)|=(2685147441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5172489013/10000000000 : ℝ)|^2105 ≤ (41848592852937/100000000000000 : ℝ)^1593
        have hw : |(5172489013/10000000000 : ℝ)|=(5172489013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-91193281/400000000 : ℝ)|^2105 ≤ (14175189576463/100000000000000 : ℝ)^1593
        have hw : |(-91193281/400000000 : ℝ)|=(91193281/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s2_3 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (434383069/1000000000 : ℝ)*x 0 + (251826581/625000000 : ℝ)*x 1 + (4682291753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434383069/1000000000 : ℝ)^2105 ≤ (16613189256867/50000000000000 : ℝ)^1593 := by
    have hnat : (434383069 : ℕ)^2105*50000000000000^1593 ≤ 16613189256867^1593*1000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434383069 1000000000 16613189256867 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (251826581/625000000 : ℝ)^2105 ≤ (1880257576347/6250000000000 : ℝ)^1593 := by
    have hnat : (251826581 : ℕ)^2105*6250000000000^1593 ≤ 1880257576347^1593*625000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251826581 625000000 1880257576347 6250000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4682291753/10000000000 : ℝ)^2105 ≤ (18344750128113/50000000000000 : ℝ)^1593 := by
    have hnat : (4682291753 : ℕ)^2105*50000000000000^1593 ≤ 18344750128113^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4682291753 10000000000 18344750128113 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434383069/1000000000 : ℝ), (251826581/625000000 : ℝ), (4682291753/10000000000 : ℝ)] ![(16613189256867/50000000000000 : ℝ), (1880257576347/6250000000000 : ℝ), (18344750128113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434383069/1000000000 : ℝ)|^2105 ≤ (16613189256867/50000000000000 : ℝ)^1593
        have hw : |(434383069/1000000000 : ℝ)|=(434383069/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(251826581/625000000 : ℝ)|^2105 ≤ (1880257576347/6250000000000 : ℝ)^1593
        have hw : |(251826581/625000000 : ℝ)|=(251826581/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4682291753/10000000000 : ℝ)|^2105 ≤ (18344750128113/50000000000000 : ℝ)^1593
        have hw : |(4682291753/10000000000 : ℝ)|=(4682291753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s2_4 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-105629097/500000000 : ℝ)*x 0 + (1293646521/2500000000 : ℝ)*x 1 + (5493240947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105629097/500000000 : ℝ)^2105 ≤ (12817534296297/100000000000000 : ℝ)^1593 := by
    have hnat : (105629097 : ℕ)^2105*100000000000000^1593 ≤ 12817534296297^1593*500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105629097 500000000 12817534296297 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293646521/2500000000 : ℝ)^2105 ≤ (41871014062293/100000000000000 : ℝ)^1593 := by
    have hnat : (1293646521 : ℕ)^2105*100000000000000^1593 ≤ 41871014062293^1593*2500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293646521 2500000000 41871014062293 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5493240947/10000000000 : ℝ)^2105 ≤ (362491613053/800000000000 : ℝ)^1593 := by
    have hnat : (5493240947 : ℕ)^2105*800000000000^1593 ≤ 362491613053^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493240947 10000000000 362491613053 800000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-105629097/500000000 : ℝ), (1293646521/2500000000 : ℝ), (5493240947/10000000000 : ℝ)] ![(12817534296297/100000000000000 : ℝ), (41871014062293/100000000000000 : ℝ), (362491613053/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-105629097/500000000 : ℝ)|^2105 ≤ (12817534296297/100000000000000 : ℝ)^1593
        have hw : |(-105629097/500000000 : ℝ)|=(105629097/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1293646521/2500000000 : ℝ)|^2105 ≤ (41871014062293/100000000000000 : ℝ)^1593
        have hw : |(1293646521/2500000000 : ℝ)|=(1293646521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5493240947/10000000000 : ℝ)|^2105 ≤ (362491613053/800000000000 : ℝ)^1593
        have hw : |(5493240947/10000000000 : ℝ)|=(5493240947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s2_5 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2643960157/5000000000 : ℝ)*x 0 + (-489769929/2500000000 : ℝ)*x 1 + (1098648197/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643960157/5000000000 : ℝ)^2105 ≤ (8617414096093/20000000000000 : ℝ)^1593 := by
    have hnat : (2643960157 : ℕ)^2105*20000000000000^1593 ≤ 8617414096093^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643960157 5000000000 8617414096093 20000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (489769929/2500000000 : ℝ)^2105 ≤ (11601477452507/100000000000000 : ℝ)^1593 := by
    have hnat : (489769929 : ℕ)^2105*100000000000000^1593 ≤ 11601477452507^1593*2500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489769929 2500000000 11601477452507 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098648197/2000000000 : ℝ)^2105 ≤ (9062290409163/20000000000000 : ℝ)^1593 := by
    have hnat : (1098648197 : ℕ)^2105*20000000000000^1593 ≤ 9062290409163^1593*2000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098648197 2000000000 9062290409163 20000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643960157/5000000000 : ℝ), (-489769929/2500000000 : ℝ), (1098648197/2000000000 : ℝ)] ![(8617414096093/20000000000000 : ℝ), (11601477452507/100000000000000 : ℝ), (9062290409163/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643960157/5000000000 : ℝ)|^2105 ≤ (8617414096093/20000000000000 : ℝ)^1593
        have hw : |(2643960157/5000000000 : ℝ)|=(2643960157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-489769929/2500000000 : ℝ)|^2105 ≤ (11601477452507/100000000000000 : ℝ)^1593
        have hw : |(-489769929/2500000000 : ℝ)|=(489769929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1098648197/2000000000 : ℝ)|^2105 ≤ (9062290409163/20000000000000 : ℝ)^1593
        have hw : |(1098648197/2000000000 : ℝ)|=(1098648197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s2_6 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2643960247/5000000000 : ℝ)*x 0 + (2746620521/5000000000 : ℝ)*x 1 + (-195907939/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643960247/5000000000 : ℝ)^2105 ≤ (21543536209271/50000000000000 : ℝ)^1593 := by
    have hnat : (2643960247 : ℕ)^2105*50000000000000^1593 ≤ 21543536209271^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643960247 5000000000 21543536209271 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2746620521/5000000000 : ℝ)^2105 ≤ (453114526671/1000000000000 : ℝ)^1593 := by
    have hnat : (2746620521 : ℕ)^2105*1000000000000^1593 ≤ 453114526671^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746620521 5000000000 453114526671 1000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (195907939/1000000000 : ℝ)^2105 ≤ (11601474901479/100000000000000 : ℝ)^1593 := by
    have hnat : (195907939 : ℕ)^2105*100000000000000^1593 ≤ 11601474901479^1593*1000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195907939 1000000000 11601474901479 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643960247/5000000000 : ℝ), (2746620521/5000000000 : ℝ), (-195907939/1000000000 : ℝ)] ![(21543536209271/50000000000000 : ℝ), (453114526671/1000000000000 : ℝ), (11601474901479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643960247/5000000000 : ℝ)|^2105 ≤ (21543536209271/50000000000000 : ℝ)^1593
        have hw : |(2643960247/5000000000 : ℝ)|=(2643960247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2746620521/5000000000 : ℝ)|^2105 ≤ (453114526671/1000000000000 : ℝ)^1593
        have hw : |(2746620521/5000000000 : ℝ)|=(2746620521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-195907939/1000000000 : ℝ)|^2105 ≤ (11601474901479/100000000000000 : ℝ)^1593
        have hw : |(-195907939/1000000000 : ℝ)|=(195907939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s2_7 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4343995179/10000000000 : ℝ)*x 0 + (2339024973/5000000000 : ℝ)*x 1 + (4033507027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343995179/10000000000 : ℝ)^2105 ≤ (33228041106729/100000000000000 : ℝ)^1593 := by
    have hnat : (4343995179 : ℕ)^2105*100000000000000^1593 ≤ 33228041106729^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343995179 10000000000 33228041106729 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2339024973/5000000000 : ℝ)^2105 ≤ (9161396455047/25000000000000 : ℝ)^1593 := by
    have hnat : (2339024973 : ℕ)^2105*25000000000000^1593 ≤ 9161396455047^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2339024973 5000000000 9161396455047 25000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4033507027/10000000000 : ℝ)^2105 ≤ (30126373061289/100000000000000 : ℝ)^1593 := by
    have hnat : (4033507027 : ℕ)^2105*100000000000000^1593 ≤ 30126373061289^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033507027 10000000000 30126373061289 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343995179/10000000000 : ℝ), (2339024973/5000000000 : ℝ), (4033507027/10000000000 : ℝ)] ![(33228041106729/100000000000000 : ℝ), (9161396455047/25000000000000 : ℝ), (30126373061289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343995179/10000000000 : ℝ)|^2105 ≤ (33228041106729/100000000000000 : ℝ)^1593
        have hw : |(4343995179/10000000000 : ℝ)|=(4343995179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2339024973/5000000000 : ℝ)|^2105 ≤ (9161396455047/25000000000000 : ℝ)^1593
        have hw : |(2339024973/5000000000 : ℝ)|=(2339024973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4033507027/10000000000 : ℝ)|^2105 ≤ (30126373061289/100000000000000 : ℝ)^1593
        have hw : |(4033507027/10000000000 : ℝ)|=(4033507027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1227_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75567419/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (191/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (4719/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8131/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (191/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (191/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (191/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (191/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (191/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (191/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (191/3125 : ℝ) ^ (8419/2048 : ℝ) ≤ (127968814584431/12500000000000000000 : ℝ) := by
    have hpowers : (191/3125 : ℝ)^8419 ≤ (127968814584431/12500000000000000000 : ℝ)^2048 := by
      have hnat : (191 : ℕ)^8419*12500000000000000000^2048 ≤ 127968814584431^2048*3125^8419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        191 3125 127968814584431 12500000000000000000 8419 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (191/3125 : ℝ)) (X := (127968814584431/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10031/50000 : ℝ) ^ (8419/2048 : ℝ) ≤ (135572677270999571/100000000000000000000 : ℝ) := by
    have hpowers : (10031/50000 : ℝ)^8419 ≤ (135572677270999571/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10031 : ℕ)^8419*100000000000000000000^2048 ≤ 135572677270999571^2048*50000^8419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10031 50000 135572677270999571 100000000000000000000 8419 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10031/50000 : ℝ)) (X := (135572677270999571/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250127968814584431/6250000000000000000 : ℝ) ≤ (10000049806979817/10000000000000000 : ℝ) ^ (8419/2048 : ℝ) := by
    have hpowers : (6250127968814584431/6250000000000000000 : ℝ)^2048 ≤ (10000049806979817/10000000000000000 : ℝ)^8419 := by
      have hnat : (6250127968814584431 : ℕ)^2048*10000000000000000^8419 ≤ 10000049806979817^8419*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250127968814584431 6250000000000000000 10000049806979817 10000000000000000 2048 8419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000049806979817/10000000000000000 : ℝ)) (X := (6250127968814584431/6250000000000000000 : ℝ)) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100136596427787675019/100000000000000000000 : ℝ) ≤ (10003321119061893/10000000000000000 : ℝ) ^ (8419/2048 : ℝ) := by
    have hpowers : (100136596427787675019/100000000000000000000 : ℝ)^2048 ≤ (10003321119061893/10000000000000000 : ℝ)^8419 := by
      have hnat : (100136596427787675019 : ℕ)^2048*10000000000000000^8419 ≤ 10003321119061893^8419*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100136596427787675019 100000000000000000000 10003321119061893 10000000000000000 2048 8419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003321119061893/10000000000000000 : ℝ)) (X := (100136596427787675019/100000000000000000000 : ℝ)) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50135572677270999571/50000000000000000000 : ℝ) ≤ (10006592431143969/10000000000000000 : ℝ) ^ (8419/2048 : ℝ) := by
    have hpowers : (50135572677270999571/50000000000000000000 : ℝ)^2048 ≤ (10006592431143969/10000000000000000 : ℝ)^8419 := by
      have hnat : (50135572677270999571 : ℕ)^2048*10000000000000000^8419 ≤ 10006592431143969^8419*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50135572677270999571 50000000000000000000 10006592431143969 10000000000000000 2048 8419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006592431143969/10000000000000000 : ℝ)) (X := (50135572677270999571/50000000000000000000 : ℝ)) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(127968814584431/12500000000000000000 : ℝ) ≤ ((749788743486436291/750000000000000000 : ℝ)+2*(8793849683/3750000000000 : ℝ)*(191/3125 : ℝ))^(8419/2048 : ℝ) := by
    rw [show (749788743486436291/750000000000000000 : ℝ)+2*(8793849683/3750000000000 : ℝ)*(191/3125 : ℝ)=(10000049806979817/10000000000000000 : ℝ) by norm_num, show 1+2*(127968814584431/12500000000000000000 : ℝ)=(6250127968814584431/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(135572677270999571/100000000000000000000 : ℝ)+(127968814584431/12500000000000000000 : ℝ) ≤ ((749788743486436291/750000000000000000 : ℝ)+(8793849683/3750000000000 : ℝ)*((10031/50000 : ℝ)+(191/3125 : ℝ)))^(8419/2048 : ℝ) := by
    rw [show (749788743486436291/750000000000000000 : ℝ)+(8793849683/3750000000000 : ℝ)*((10031/50000 : ℝ)+(191/3125 : ℝ))=(10003321119061893/10000000000000000 : ℝ) by norm_num, show 1+(135572677270999571/100000000000000000000 : ℝ)+(127968814584431/12500000000000000000 : ℝ)=(100136596427787675019/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(135572677270999571/100000000000000000000 : ℝ) ≤ ((749788743486436291/750000000000000000 : ℝ)+2*(8793849683/3750000000000 : ℝ)*(10031/50000 : ℝ))^(8419/2048 : ℝ) := by
    rw [show (749788743486436291/750000000000000000 : ℝ)+2*(8793849683/3750000000000 : ℝ)*(10031/50000 : ℝ)=(10006592431143969/10000000000000000 : ℝ) by norm_num, show 1+2*(135572677270999571/100000000000000000000 : ℝ)=(50135572677270999571/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (749788743486436291/750000000000000000 : ℝ)*(X 1 0+X 2 0)+(8793849683/3750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8419/2048 : ℝ)) (lo := (191/3125 : ℝ)) (hi := (10031/50000 : ℝ)) (c := (749788743486436291/750000000000000000 : ℝ)) (alpha := (8793849683/3750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (749788743486436291/750000000000000000 : ℝ)*(X 0 1+X 2 1)+(8793849683/3750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8419/2048 : ℝ)) (lo := (191/3125 : ℝ)) (hi := (10031/50000 : ℝ)) (c := (749788743486436291/750000000000000000 : ℝ)) (alpha := (8793849683/3750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (749788743486436291/750000000000000000 : ℝ)*(X 0 2+X 1 2)+(8793849683/3750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8419/2048 : ℝ)) (lo := (191/3125 : ℝ)) (hi := (10031/50000 : ℝ)) (c := (749788743486436291/750000000000000000 : ℝ)) (alpha := (8793849683/3750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-16503909/78125000 : ℝ)*X 0 0+(2747678987/5000000000 : ℝ)*X 0 1+(5172488907/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167821721/312500000 : ℝ)*X 1 0+(-2279831993/10000000000 : ℝ)*X 1 1+(2586244423/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2685147441/5000000000 : ℝ)*X 2 0+(5172489013/10000000000 : ℝ)*X 2 1+(-91193281/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((434383069/1000000000 : ℝ)*X 0 0+(251826581/625000000 : ℝ)*X 0 1+(4682291753/10000000000 : ℝ)*X 0 2+(434383069/1000000000 : ℝ)*X 1 0+(251826581/625000000 : ℝ)*X 1 1+(4682291753/10000000000 : ℝ)*X 1 2+(434383069/1000000000 : ℝ)*X 2 0+(251826581/625000000 : ℝ)*X 2 1+(4682291753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-105629097/500000000 : ℝ)*X 0 0+(1293646521/2500000000 : ℝ)*X 0 1+(5493240947/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643960157/5000000000 : ℝ)*X 1 0+(-489769929/2500000000 : ℝ)*X 1 1+(1098648197/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643960247/5000000000 : ℝ)*X 2 0+(2746620521/5000000000 : ℝ)*X 2 1+(-195907939/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4343995179/10000000000 : ℝ)*X 0 0+(2339024973/5000000000 : ℝ)*X 0 1+(4033507027/10000000000 : ℝ)*X 0 2+(4343995179/10000000000 : ℝ)*X 1 0+(2339024973/5000000000 : ℝ)*X 1 1+(4033507027/10000000000 : ℝ)*X 1 2+(4343995179/10000000000 : ℝ)*X 2 0+(2339024973/5000000000 : ℝ)*X 2 1+(4033507027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19265443523544925821575537/3125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (122764267/10000000000000 : ℝ)*(base19) + (514315611/50000000000000 : ℝ)*(base23) + (24013587/50000000000000 : ℝ)*(lower2) + (40673873/20000000000000 : ℝ)*(upper3) + (41202871/50000000000000 : ℝ)*(upper5) + (1157126794886507/50000000000000 : ℝ)*(major0) + (1157126794886507/50000000000000 : ℝ)*(major1) + (1157126794886507/50000000000000 : ℝ)*(major2) + (3097244511699953/100000000000000 : ℝ)*(sp0) + (1548627415697931/50000000000000 : ℝ)*(sp1) + (309725503040731/10000000000000 : ℝ)*(sp2) + (765621886840539/50000000000000 : ℝ)*(sp3) + (11547338579/100000000000000 : ℝ)*(sp4) + (7141328349/100000000000000 : ℝ)*(sp7) + (765625457504713/50000000000000 : ℝ)*(f.failure) + (774314014759633/25000000000000 : ℝ)*(f.sum) + (203525756501/375000000000000000000000000 : ℝ)*base66 + (260044082062774463/37500000000000000000000000000000 : ℝ)*base68 + (37477327649725537/37500000000000000000000000000000 : ℝ)*base69 + (13636354125274463/37500000000000000000000000000000 : ℝ)*base72 + (110625563711/23437500000000000000000000 : ℝ)*base74 + (231211656150274463/37500000000000000000000000000000 : ℝ)*base76 + (114458679975274463/37500000000000000000000000000000 : ℝ)*base78 + (288025651012774463/37500000000000000000000000000000 : ℝ)*base80 + (195440931499/375000000000000000000000000 : ℝ)*base81 + (8254253/2500000000000000000000 : ℝ)*base90 + (8254253/2500000000000000000000 : ℝ)*base92 + (8254253/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6171966055363528576746331/6250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (557048899/100000000000000 : ℝ)*(base19) + (111970523/12500000000000 : ℝ)*(base23) + (2249513/3125000000000 : ℝ)*(upper2) + (13027369/12500000000000 : ℝ)*(upper3) + (4289211/25000000000000 : ℝ)*(upper5) + (1172419415595853/50000000000000 : ℝ)*(major0) + (1172419415595853/50000000000000 : ℝ)*(major1) + (1172419415595853/50000000000000 : ℝ)*(major2) + (123736263/2500000000000 : ℝ)*(sp1) + (1387098451/12500000000000 : ℝ)*(sp2) + (39227370733877/1250000000000 : ℝ)*(sp4) + (3138184152210741/100000000000000 : ℝ)*(sp5) + (98068052067449/3125000000000 : ℝ)*(sp6) + (1551487970756091/100000000000000 : ℝ)*(sp7) + (1551487970756091/100000000000000 : ℝ)*(f.failure) + (39227370733877/1250000000000 : ℝ)*(f.sum) + (1668249924979/375000000000000000000000000 : ℝ)*base66 + (414126101483101223/37500000000000000000000000000000 : ℝ)*base67 + (349995909570601223/37500000000000000000000000000000 : ℝ)*base69 + (160248068595601223/37500000000000000000000000000000 : ℝ)*base71 + (293419359823/187500000000000000000000000 : ℝ)*base73 + (603855973883101223/37500000000000000000000000000000 : ℝ)*base75 + (149992346070601223/37500000000000000000000000000000 : ℝ)*base77 + (405933216983101223/37500000000000000000000000000000 : ℝ)*base79 + (320797992979/375000000000000000000000000 : ℝ)*base82 + (24600871/5000000000000000000000 : ℝ)*base90 + (24600871/5000000000000000000000 : ℝ)*base92 + (24600871/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1227_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75567419/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (191/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4719/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8131/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1227_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1227_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75567419/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4719/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8131/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1227_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1227_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1227_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75567419/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4719/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8131/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1227_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

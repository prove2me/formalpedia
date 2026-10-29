-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1388_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:25:00.056979+00:00
-- url     : https://prove2.me/submissions/4c1a12dc-9c8d-4261-9469-6c51bfea3f23

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
theorem support_rectangle_w1388_s0_0 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1782262857/10000000000 : ℝ)*x 0 + (5977284697/10000000000 : ℝ)*x 1 + (4821764953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1782262857/10000000000 : ℝ)^1087 ≤ (5238346123477/50000000000000 : ℝ)^831 := by
    have hnat : (1782262857 : ℕ)^1087*50000000000000^831 ≤ 5238346123477^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1782262857 10000000000 5238346123477 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5977284697/10000000000 : ℝ)^1087 ≤ (51009747107689/100000000000000 : ℝ)^831 := by
    have hnat : (5977284697 : ℕ)^1087*100000000000000^831 ≤ 51009747107689^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5977284697 10000000000 51009747107689 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4821764953/10000000000 : ℝ)^1087 ≤ (3851356063109/10000000000000 : ℝ)^831 := by
    have hnat : (4821764953 : ℕ)^1087*10000000000000^831 ≤ 3851356063109^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4821764953 10000000000 3851356063109 10000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1782262857/10000000000 : ℝ), (5977284697/10000000000 : ℝ), (4821764953/10000000000 : ℝ)] ![(5238346123477/50000000000000 : ℝ), (51009747107689/100000000000000 : ℝ), (3851356063109/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1782262857/10000000000 : ℝ)|^1087 ≤ (5238346123477/50000000000000 : ℝ)^831
        have hw : |(-1782262857/10000000000 : ℝ)|=(1782262857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5977284697/10000000000 : ℝ)|^1087 ≤ (51009747107689/100000000000000 : ℝ)^831
        have hw : |(5977284697/10000000000 : ℝ)|=(5977284697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4821764953/10000000000 : ℝ)|^1087 ≤ (3851356063109/10000000000000 : ℝ)^831
        have hw : |(4821764953/10000000000 : ℝ)|=(4821764953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s0_1 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (21471361/39062500 : ℝ)*x 0 + (-2436890543/10000000000 : ℝ)*x 1 + (4821765059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21471361/39062500 : ℝ)^1087 ≤ (5714048823507/12500000000000 : ℝ)^831 := by
    have hnat : (21471361 : ℕ)^1087*12500000000000^831 ≤ 5714048823507^831*39062500^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21471361 39062500 5714048823507 12500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2436890543/10000000000 : ℝ)^1087 ≤ (15774047658881/100000000000000 : ℝ)^831 := by
    have hnat : (2436890543 : ℕ)^1087*100000000000000^831 ≤ 15774047658881^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2436890543 10000000000 15774047658881 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4821765059/10000000000 : ℝ)^1087 ≤ (7702712347717/20000000000000 : ℝ)^831 := by
    have hnat : (4821765059 : ℕ)^1087*20000000000000^831 ≤ 7702712347717^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4821765059 10000000000 7702712347717 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21471361/39062500 : ℝ), (-2436890543/10000000000 : ℝ), (4821765059/10000000000 : ℝ)] ![(5714048823507/12500000000000 : ℝ), (15774047658881/100000000000000 : ℝ), (7702712347717/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21471361/39062500 : ℝ)|^1087 ≤ (5714048823507/12500000000000 : ℝ)^831
        have hw : |(21471361/39062500 : ℝ)|=(21471361/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2436890543/10000000000 : ℝ)|^1087 ≤ (15774047658881/100000000000000 : ℝ)^831
        have hw : |(-2436890543/10000000000 : ℝ)|=(2436890543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4821765059/10000000000 : ℝ)|^1087 ≤ (7702712347717/20000000000000 : ℝ)^831
        have hw : |(4821765059/10000000000 : ℝ)|=(4821765059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s0_2 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2748334213/5000000000 : ℝ)*x 0 + (2410882517/5000000000 : ℝ)*x 1 + (-2436890561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2748334213/5000000000 : ℝ)^1087 ≤ (45712390696839/100000000000000 : ℝ)^831 := by
    have hnat : (2748334213 : ℕ)^1087*100000000000000^831 ≤ 45712390696839^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748334213 5000000000 45712390696839 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2410882517/5000000000 : ℝ)^1087 ≤ (4814195184673/12500000000000 : ℝ)^831 := by
    have hnat : (2410882517 : ℕ)^1087*12500000000000^831 ≤ 4814195184673^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2410882517 5000000000 4814195184673 12500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2436890561/10000000000 : ℝ)^1087 ≤ (15774047811289/100000000000000 : ℝ)^831 := by
    have hnat : (2436890561 : ℕ)^1087*100000000000000^831 ≤ 15774047811289^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2436890561 10000000000 15774047811289 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2748334213/5000000000 : ℝ), (2410882517/5000000000 : ℝ), (-2436890561/10000000000 : ℝ)] ![(45712390696839/100000000000000 : ℝ), (4814195184673/12500000000000 : ℝ), (15774047811289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2748334213/5000000000 : ℝ)|^1087 ≤ (45712390696839/100000000000000 : ℝ)^831
        have hw : |(2748334213/5000000000 : ℝ)|=(2748334213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2410882517/5000000000 : ℝ)|^1087 ≤ (4814195184673/12500000000000 : ℝ)^831
        have hw : |(2410882517/5000000000 : ℝ)|=(2410882517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2436890561/10000000000 : ℝ)|^1087 ≤ (15774047811289/100000000000000 : ℝ)^831
        have hw : |(-2436890561/10000000000 : ℝ)|=(2436890561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s0_3 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2085969869/5000000000 : ℝ)*x 0 + (3104599199/10000000000 : ℝ)*x 1 + (5566873143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2085969869/5000000000 : ℝ)^1087 ≤ (31869729794547/100000000000000 : ℝ)^831 := by
    have hnat : (2085969869 : ℕ)^1087*100000000000000^831 ≤ 31869729794547^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085969869 5000000000 31869729794547 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3104599199/10000000000 : ℝ)^1087 ≤ (5413167535747/25000000000000 : ℝ)^831 := by
    have hnat : (3104599199 : ℕ)^1087*25000000000000^831 ≤ 5413167535747^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104599199 10000000000 5413167535747 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5566873143/10000000000 : ℝ)^1087 ≤ (2904850002931/6250000000000 : ℝ)^831 := by
    have hnat : (5566873143 : ℕ)^1087*6250000000000^831 ≤ 2904850002931^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5566873143 10000000000 2904850002931 6250000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2085969869/5000000000 : ℝ), (3104599199/10000000000 : ℝ), (5566873143/10000000000 : ℝ)] ![(31869729794547/100000000000000 : ℝ), (5413167535747/25000000000000 : ℝ), (2904850002931/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2085969869/5000000000 : ℝ)|^1087 ≤ (31869729794547/100000000000000 : ℝ)^831
        have hw : |(2085969869/5000000000 : ℝ)|=(2085969869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3104599199/10000000000 : ℝ)|^1087 ≤ (5413167535747/25000000000000 : ℝ)^831
        have hw : |(3104599199/10000000000 : ℝ)|=(3104599199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5566873143/10000000000 : ℝ)|^1087 ≤ (2904850002931/6250000000000 : ℝ)^831
        have hw : |(5566873143/10000000000 : ℝ)|=(5566873143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s0_4 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-111655201/625000000 : ℝ)*x 0 + (4851417721/10000000000 : ℝ)*x 1 + (5946572121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (111655201/625000000 : ℝ)^1087 ≤ (5254577622903/50000000000000 : ℝ)^831 := by
    have hnat : (111655201 : ℕ)^1087*50000000000000^831 ≤ 5254577622903^831*625000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111655201 625000000 5254577622903 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4851417721/10000000000 : ℝ)^1087 ≤ (4852958493039/12500000000000 : ℝ)^831 := by
    have hnat : (4851417721 : ℕ)^1087*12500000000000^831 ≤ 4852958493039^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4851417721 10000000000 4852958493039 12500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5946572121/10000000000 : ℝ)^1087 ≤ (10133435358389/20000000000000 : ℝ)^831 := by
    have hnat : (5946572121 : ℕ)^1087*20000000000000^831 ≤ 10133435358389^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5946572121 10000000000 10133435358389 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-111655201/625000000 : ℝ), (4851417721/10000000000 : ℝ), (5946572121/10000000000 : ℝ)] ![(5254577622903/50000000000000 : ℝ), (4852958493039/12500000000000 : ℝ), (10133435358389/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-111655201/625000000 : ℝ)|^1087 ≤ (5254577622903/50000000000000 : ℝ)^831
        have hw : |(-111655201/625000000 : ℝ)|=(111655201/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4851417721/10000000000 : ℝ)|^1087 ≤ (4852958493039/12500000000000 : ℝ)^831
        have hw : |(4851417721/10000000000 : ℝ)|=(4851417721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5946572121/10000000000 : ℝ)|^1087 ≤ (10133435358389/20000000000000 : ℝ)^831
        have hw : |(5946572121/10000000000 : ℝ)|=(5946572121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s0_5 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5181487407/10000000000 : ℝ)*x 0 + (-1312084179/10000000000 : ℝ)*x 1 + (5946570183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5181487407/10000000000 : ℝ)^1087 ≤ (4231443521639/10000000000000 : ℝ)^831 := by
    have hnat : (5181487407 : ℕ)^1087*10000000000000^831 ≤ 4231443521639^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181487407 10000000000 4231443521639 10000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1312084179/10000000000 : ℝ)^1087 ≤ (7018409566939/100000000000000 : ℝ)^831 := by
    have hnat : (1312084179 : ℕ)^1087*100000000000000^831 ≤ 7018409566939^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312084179 10000000000 7018409566939 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5946570183/10000000000 : ℝ)^1087 ≤ (10133431038503/20000000000000 : ℝ)^831 := by
    have hnat : (5946570183 : ℕ)^1087*20000000000000^831 ≤ 10133431038503^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5946570183 10000000000 10133431038503 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5181487407/10000000000 : ℝ), (-1312084179/10000000000 : ℝ), (5946570183/10000000000 : ℝ)] ![(4231443521639/10000000000000 : ℝ), (7018409566939/100000000000000 : ℝ), (10133431038503/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5181487407/10000000000 : ℝ)|^1087 ≤ (4231443521639/10000000000000 : ℝ)^831
        have hw : |(5181487407/10000000000 : ℝ)|=(5181487407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1312084179/10000000000 : ℝ)|^1087 ≤ (7018409566939/100000000000000 : ℝ)^831
        have hw : |(-1312084179/10000000000 : ℝ)|=(1312084179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5946570183/10000000000 : ℝ)|^1087 ≤ (10133431038503/20000000000000 : ℝ)^831
        have hw : |(5946570183/10000000000 : ℝ)|=(5946570183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s0_6 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5181483741/10000000000 : ℝ)*x 0 + (743321877/1250000000 : ℝ)*x 1 + (-1312082079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5181483741/10000000000 : ℝ)^1087 ≤ (42314396055277/100000000000000 : ℝ)^831 := by
    have hnat : (5181483741 : ℕ)^1087*100000000000000^831 ≤ 42314396055277^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181483741 10000000000 42314396055277 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (743321877/1250000000 : ℝ)^1087 ≤ (50667209057351/100000000000000 : ℝ)^831 := by
    have hnat : (743321877 : ℕ)^1087*100000000000000^831 ≤ 50667209057351^831*1250000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743321877 1250000000 50667209057351 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1312082079/10000000000 : ℝ)^1087 ≤ (7018394873457/100000000000000 : ℝ)^831 := by
    have hnat : (1312082079 : ℕ)^1087*100000000000000^831 ≤ 7018394873457^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312082079 10000000000 7018394873457 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5181483741/10000000000 : ℝ), (743321877/1250000000 : ℝ), (-1312082079/10000000000 : ℝ)] ![(42314396055277/100000000000000 : ℝ), (50667209057351/100000000000000 : ℝ), (7018394873457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5181483741/10000000000 : ℝ)|^1087 ≤ (42314396055277/100000000000000 : ℝ)^831
        have hw : |(5181483741/10000000000 : ℝ)|=(5181483741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(743321877/1250000000 : ℝ)|^1087 ≤ (50667209057351/100000000000000 : ℝ)^831
        have hw : |(743321877/1250000000 : ℝ)|=(743321877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1312082079/10000000000 : ℝ)|^1087 ≤ (7018394873457/100000000000000 : ℝ)^831
        have hw : |(-1312082079/10000000000 : ℝ)|=(1312082079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s0_7 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4180924799/10000000000 : ℝ)*x 0 + (687961147/1250000000 : ℝ)*x 1 + (3170047327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180924799/10000000000 : ℝ)^1087 ≤ (7989885423449/25000000000000 : ℝ)^831 := by
    have hnat : (4180924799 : ℕ)^1087*25000000000000^831 ≤ 7989885423449^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180924799 10000000000 7989885423449 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (687961147/1250000000 : ℝ)^1087 ≤ (11447194968567/25000000000000 : ℝ)^831 := by
    have hnat : (687961147 : ℕ)^1087*25000000000000^831 ≤ 11447194968567^831*1250000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687961147 1250000000 11447194968567 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3170047327/10000000000 : ℝ)^1087 ≤ (4450335683829/20000000000000 : ℝ)^831 := by
    have hnat : (3170047327 : ℕ)^1087*20000000000000^831 ≤ 4450335683829^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3170047327 10000000000 4450335683829 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180924799/10000000000 : ℝ), (687961147/1250000000 : ℝ), (3170047327/10000000000 : ℝ)] ![(7989885423449/25000000000000 : ℝ), (11447194968567/25000000000000 : ℝ), (4450335683829/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180924799/10000000000 : ℝ)|^1087 ≤ (7989885423449/25000000000000 : ℝ)^831
        have hw : |(4180924799/10000000000 : ℝ)|=(4180924799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(687961147/1250000000 : ℝ)|^1087 ≤ (11447194968567/25000000000000 : ℝ)^831
        have hw : |(687961147/1250000000 : ℝ)|=(687961147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3170047327/10000000000 : ℝ)|^1087 ≤ (4450335683829/20000000000000 : ℝ)^831
        have hw : |(3170047327/10000000000 : ℝ)|=(3170047327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1388_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (877/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1659/6250 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4347/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4347 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4347*1^1024 ≤ 0^1024*1^4347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4347 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4347/1024 : ℝ) ≤ (204502221263946109/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4347 ≤ (204502221263946109/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4347*10000000000000000000^1024 ≤ 204502221263946109^1024*5^4347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 204502221263946109 10000000000000000000 4347 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (204502221263946109/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4347 := by
      have hnat : (1 : ℕ)^1024*1^4347 ≤ 1^4347*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10204502221263946109/10000000000000000000 : ℝ) ≤ (10047801436882053/10000000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (10204502221263946109/10000000000000000000 : ℝ)^1024 ≤ (10047801436882053/10000000000000000 : ℝ)^4347 := by
      have hnat : (10204502221263946109 : ℕ)^1024*10000000000000000^4347 ≤ 10047801436882053^4347*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10204502221263946109 10000000000000000000 10047801436882053 10000000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10047801436882053/10000000000000000 : ℝ)) (X := (10204502221263946109/10000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5204502221263946109/5000000000000000000 : ℝ) ≤ (5047801436882053/5000000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (5204502221263946109/5000000000000000000 : ℝ)^1024 ≤ (5047801436882053/5000000000000000 : ℝ)^4347 := by
      have hnat : (5204502221263946109 : ℕ)^1024*5000000000000000^4347 ≤ 5047801436882053^4347*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5204502221263946109 5000000000000000000 5047801436882053 5000000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5047801436882053/5000000000000000 : ℝ)) (X := (5204502221263946109/5000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(47801436882053/4000000000000000 : ℝ)*(0 : ℝ))^(4347/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(47801436882053/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(204502221263946109/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(47801436882053/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4347/1024 : ℝ) := by
    rw [show (1 : ℝ)+(47801436882053/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10047801436882053/10000000000000000 : ℝ) by norm_num, show 1+(204502221263946109/10000000000000000000 : ℝ)+(0 : ℝ)=(10204502221263946109/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(204502221263946109/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(47801436882053/4000000000000000 : ℝ)*(2/5 : ℝ))^(4347/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(47801436882053/4000000000000000 : ℝ)*(2/5 : ℝ)=(5047801436882053/5000000000000000 : ℝ) by norm_num, show 1+2*(204502221263946109/10000000000000000000 : ℝ)=(5204502221263946109/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(47801436882053/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47801436882053/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(47801436882053/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47801436882053/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(47801436882053/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47801436882053/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1782262857/10000000000 : ℝ)*X 0 0+(5977284697/10000000000 : ℝ)*X 0 1+(4821764953/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((21471361/39062500 : ℝ)*X 1 0+(-2436890543/10000000000 : ℝ)*X 1 1+(4821765059/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2748334213/5000000000 : ℝ)*X 2 0+(2410882517/5000000000 : ℝ)*X 2 1+(-2436890561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2085969869/5000000000 : ℝ)*X 0 0+(3104599199/10000000000 : ℝ)*X 0 1+(5566873143/10000000000 : ℝ)*X 0 2+(2085969869/5000000000 : ℝ)*X 1 0+(3104599199/10000000000 : ℝ)*X 1 1+(5566873143/10000000000 : ℝ)*X 1 2+(2085969869/5000000000 : ℝ)*X 2 0+(3104599199/10000000000 : ℝ)*X 2 1+(5566873143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-111655201/625000000 : ℝ)*X 0 0+(4851417721/10000000000 : ℝ)*X 0 1+(5946572121/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5181487407/10000000000 : ℝ)*X 1 0+(-1312084179/10000000000 : ℝ)*X 1 1+(5946570183/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5181483741/10000000000 : ℝ)*X 2 0+(743321877/1250000000 : ℝ)*X 2 1+(-1312082079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4180924799/10000000000 : ℝ)*X 0 0+(687961147/1250000000 : ℝ)*X 0 1+(3170047327/10000000000 : ℝ)*X 0 2+(4180924799/10000000000 : ℝ)*X 1 0+(687961147/1250000000 : ℝ)*X 1 1+(3170047327/10000000000 : ℝ)*X 1 2+(4180924799/10000000000 : ℝ)*X 2 0+(687961147/1250000000 : ℝ)*X 2 1+(3170047327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (229920622955617997969067/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31458431/100000000000000 : ℝ)*(base1) + (1079596957/100000000000000 : ℝ)*(base19) + (1081171397/100000000000000 : ℝ)*(base23) + (27240373/20000000000000 : ℝ)*(upper3) + (65998983/50000000000000 : ℝ)*(upper5) + (635775443808987/100000000000000 : ℝ)*(major0) + (635775443808987/100000000000000 : ℝ)*(major1) + (635775443808987/100000000000000 : ℝ)*(major2) + (865414972176409/100000000000000 : ℝ)*(sp0) + (432708783516897/50000000000000 : ℝ)*(sp1) + (865417565459353/100000000000000 : ℝ)*(sp2) + (101532575656683/25000000000000 : ℝ)*(sp3) + (926478193/25000000000000 : ℝ)*(sp4) + (876810821/50000000000000 : ℝ)*(sp7) + (81226417541361/20000000000000 : ℝ)*(f.failure) + (3461674586523/400000000000 : ℝ)*(f.sum) + (373363198610311/200000000000000000000000000000 : ℝ)*base65 + (726211242410311/400000000000000000000000000000 : ℝ)*base67 + (1166350260810311/400000000000000000000000000000 : ℝ)*base69 + (833047210789689/400000000000000000000000000000 : ℝ)*base72 + (830258476810311/200000000000000000000000000000 : ℝ)*base73 + (1353162001989689/400000000000000000000000000000 : ℝ)*base76 + (952137559610311/400000000000000000000000000000 : ℝ)*base77 + (893204315610311/400000000000000000000000000000 : ℝ)*base79 + (813594865010311/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (826473/2000000000000000000000 : ℝ)*base90 + (826473/2000000000000000000000 : ℝ)*base92 + (826473/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8222660212533274977/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1293760389/100000000000000 : ℝ)*(base19) + (60570439/4000000000000 : ℝ)*(base23) + (161203969/50000000000000 : ℝ)*(base39) + (121123469/50000000000000 : ℝ)*(upper2) + (2224097/800000000000 : ℝ)*(upper5) + (670812454726907/100000000000000 : ℝ)*(major0) + (670812454726907/100000000000000 : ℝ)*(major1) + (670812132318969/100000000000000 : ℝ)*(major2) + (308903153/10000000000000 : ℝ)*(sp1) + (558835539/12500000000000 : ℝ)*(sp2) + (913110652433031/100000000000000 : ℝ)*(sp4) + (913106269641113/100000000000000 : ℝ)*(sp5) + (456552494947841/50000000000000 : ℝ)*(sp6) + (214256830262083/50000000000000 : ℝ)*(sp7) + (214256830262083/50000000000000 : ℝ)*(f.failure) + (913110974840969/100000000000000 : ℝ)*(f.sum) + (386629615784143/100000000000000000000000000000 : ℝ)*base66 + (1678080000763357/400000000000000000000000000000 : ℝ)*base67 + (1043965528699929/400000000000000000000000000000 : ℝ)*base70 + (764537414436643/400000000000000000000000000000 : ℝ)*base72 + (361683358115857/100000000000000000000000000000 : ℝ)*base73 + (3130331607899929/400000000000000000000000000000 : ℝ)*base76 + (287925078699929/400000000000000000000000000000 : ℝ)*base78 + (247745790100071/400000000000000000000000000000 : ℝ)*base79 + (22179210100071/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (17013419/5000000000000000000000 : ℝ)*base90 + (17013419/5000000000000000000000 : ℝ)*base92 + (17013419/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1388_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (877/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1659/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1388_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1388_s1_0 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-490115217/2500000000 : ℝ)*x 0 + (2811051927/5000000000 : ℝ)*x 1 + (506277143/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (490115217/2500000000 : ℝ)^1087 ≤ (11867526656953/100000000000000 : ℝ)^831 := by
    have hnat : (490115217 : ℕ)^1087*100000000000000^831 ≤ 11867526656953^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490115217 2500000000 11867526656953 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2811051927/5000000000 : ℝ)^1087 ≤ (47081692198161/100000000000000 : ℝ)^831 := by
    have hnat : (2811051927 : ℕ)^1087*100000000000000^831 ≤ 47081692198161^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2811051927 5000000000 47081692198161 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506277143/1000000000 : ℝ)^1087 ≤ (41050781128629/100000000000000 : ℝ)^831 := by
    have hnat : (506277143 : ℕ)^1087*100000000000000^831 ≤ 41050781128629^831*1000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506277143 1000000000 41050781128629 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-490115217/2500000000 : ℝ), (2811051927/5000000000 : ℝ), (506277143/1000000000 : ℝ)] ![(11867526656953/100000000000000 : ℝ), (47081692198161/100000000000000 : ℝ), (41050781128629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-490115217/2500000000 : ℝ)|^1087 ≤ (11867526656953/100000000000000 : ℝ)^831
        have hw : |(-490115217/2500000000 : ℝ)|=(490115217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2811051927/5000000000 : ℝ)|^1087 ≤ (47081692198161/100000000000000 : ℝ)^831
        have hw : |(2811051927/5000000000 : ℝ)|=(2811051927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(506277143/1000000000 : ℝ)|^1087 ≤ (41050781128629/100000000000000 : ℝ)^831
        have hw : |(506277143/1000000000 : ℝ)|=(506277143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s1_1 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5400965353/10000000000 : ℝ)*x 0 + (-451559233/2000000000 : ℝ)*x 1 + (39552913/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400965353/10000000000 : ℝ)^1087 ≤ (4467410279361/10000000000000 : ℝ)^831 := by
    have hnat : (5400965353 : ℕ)^1087*10000000000000^831 ≤ 4467410279361^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400965353 10000000000 4467410279361 10000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451559233/2000000000 : ℝ)^1087 ≤ (1784387605273/12500000000000 : ℝ)^831 := by
    have hnat : (451559233 : ℕ)^1087*12500000000000^831 ≤ 1784387605273^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451559233 2000000000 1784387605273 12500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39552913/78125000 : ℝ)^1087 ≤ (641418692781/1562500000000 : ℝ)^831 := by
    have hnat : (39552913 : ℕ)^1087*1562500000000^831 ≤ 641418692781^831*78125000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39552913 78125000 641418692781 1562500000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400965353/10000000000 : ℝ), (-451559233/2000000000 : ℝ), (39552913/78125000 : ℝ)] ![(4467410279361/10000000000000 : ℝ), (1784387605273/12500000000000 : ℝ), (641418692781/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400965353/10000000000 : ℝ)|^1087 ≤ (4467410279361/10000000000000 : ℝ)^831
        have hw : |(5400965353/10000000000 : ℝ)|=(5400965353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-451559233/2000000000 : ℝ)|^1087 ≤ (1784387605273/12500000000000 : ℝ)^831
        have hw : |(-451559233/2000000000 : ℝ)|=(451559233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(39552913/78125000 : ℝ)|^1087 ≤ (641418692781/1562500000000 : ℝ)^831
        have hw : |(39552913/78125000 : ℝ)|=(39552913/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s1_2 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5400966181/10000000000 : ℝ)*x 0 + (5062771611/10000000000 : ℝ)*x 1 + (-2257796689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400966181/10000000000 : ℝ)^1087 ≤ (1786964470091/4000000000000 : ℝ)^831 := by
    have hnat : (5400966181 : ℕ)^1087*4000000000000^831 ≤ 1786964470091^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400966181 10000000000 1786964470091 4000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5062771611/10000000000 : ℝ)^1087 ≤ (41050783048359/100000000000000 : ℝ)^831 := by
    have hnat : (5062771611 : ℕ)^1087*100000000000000^831 ≤ 41050783048359^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5062771611 10000000000 41050783048359 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257796689/10000000000 : ℝ)^1087 ≤ (14275105175839/100000000000000 : ℝ)^831 := by
    have hnat : (2257796689 : ℕ)^1087*100000000000000^831 ≤ 14275105175839^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257796689 10000000000 14275105175839 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400966181/10000000000 : ℝ), (5062771611/10000000000 : ℝ), (-2257796689/10000000000 : ℝ)] ![(1786964470091/4000000000000 : ℝ), (41050783048359/100000000000000 : ℝ), (14275105175839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400966181/10000000000 : ℝ)|^1087 ≤ (1786964470091/4000000000000 : ℝ)^831
        have hw : |(5400966181/10000000000 : ℝ)|=(5400966181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5062771611/10000000000 : ℝ)|^1087 ≤ (41050783048359/100000000000000 : ℝ)^831
        have hw : |(5062771611/10000000000 : ℝ)|=(5062771611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2257796689/10000000000 : ℝ)|^1087 ≤ (14275105175839/100000000000000 : ℝ)^831
        have hw : |(-2257796689/10000000000 : ℝ)|=(2257796689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s1_3 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4284060823/10000000000 : ℝ)*x 0 + (931445587/2500000000 : ℝ)*x 1 + (1229412107/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4284060823/10000000000 : ℝ)^1087 ≤ (32994695509873/100000000000000 : ℝ)^831 := by
    have hnat : (4284060823 : ℕ)^1087*100000000000000^831 ≤ 32994695509873^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4284060823 10000000000 32994695509873 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (931445587/2500000000 : ℝ)^1087 ≤ (13743445925823/50000000000000 : ℝ)^831 := by
    have hnat : (931445587 : ℕ)^1087*50000000000000^831 ≤ 13743445925823^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931445587 2500000000 13743445925823 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1229412107/2500000000 : ℝ)^1087 ≤ (3951841262627/10000000000000 : ℝ)^831 := by
    have hnat : (1229412107 : ℕ)^1087*10000000000000^831 ≤ 3951841262627^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1229412107 2500000000 3951841262627 10000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4284060823/10000000000 : ℝ), (931445587/2500000000 : ℝ), (1229412107/2500000000 : ℝ)] ![(32994695509873/100000000000000 : ℝ), (13743445925823/50000000000000 : ℝ), (3951841262627/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4284060823/10000000000 : ℝ)|^1087 ≤ (32994695509873/100000000000000 : ℝ)^831
        have hw : |(4284060823/10000000000 : ℝ)|=(4284060823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(931445587/2500000000 : ℝ)|^1087 ≤ (13743445925823/50000000000000 : ℝ)^831
        have hw : |(931445587/2500000000 : ℝ)|=(931445587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1229412107/2500000000 : ℝ)|^1087 ≤ (3951841262627/10000000000000 : ℝ)^831
        have hw : |(1229412107/2500000000 : ℝ)|=(1229412107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s1_4 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-196091921/1000000000 : ℝ)*x 0 + (5069544673/10000000000 : ℝ)*x 1 + (5615211799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196091921/1000000000 : ℝ)^1087 ≤ (5935578032727/50000000000000 : ℝ)^831 := by
    have hnat : (196091921 : ℕ)^1087*50000000000000^831 ≤ 5935578032727^831*1000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196091921 1000000000 5935578032727 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5069544673/10000000000 : ℝ)^1087 ≤ (2570164662357/6250000000000 : ℝ)^831 := by
    have hnat : (5069544673 : ℕ)^1087*6250000000000^831 ≤ 2570164662357^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5069544673 10000000000 2570164662357 6250000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5615211799/10000000000 : ℝ)^1087 ≤ (47006209325761/100000000000000 : ℝ)^831 := by
    have hnat : (5615211799 : ℕ)^1087*100000000000000^831 ≤ 47006209325761^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5615211799 10000000000 47006209325761 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-196091921/1000000000 : ℝ), (5069544673/10000000000 : ℝ), (5615211799/10000000000 : ℝ)] ![(5935578032727/50000000000000 : ℝ), (2570164662357/6250000000000 : ℝ), (47006209325761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-196091921/1000000000 : ℝ)|^1087 ≤ (5935578032727/50000000000000 : ℝ)^831
        have hw : |(-196091921/1000000000 : ℝ)|=(196091921/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5069544673/10000000000 : ℝ)|^1087 ≤ (2570164662357/6250000000000 : ℝ)^831
        have hw : |(5069544673/10000000000 : ℝ)|=(5069544673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5615211799/10000000000 : ℝ)|^1087 ≤ (47006209325761/100000000000000 : ℝ)^831
        have hw : |(5615211799/10000000000 : ℝ)|=(5615211799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s1_5 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5255283919/10000000000 : ℝ)*x 0 + (-1705357053/10000000000 : ℝ)*x 1 + (2807605921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255283919/10000000000 : ℝ)^1087 ≤ (8620894304619/20000000000000 : ℝ)^831 := by
    have hnat : (5255283919 : ℕ)^1087*20000000000000^831 ≤ 8620894304619^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255283919 10000000000 8620894304619 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1705357053/10000000000 : ℝ)^1087 ≤ (4944659332553/50000000000000 : ℝ)^831 := by
    have hnat : (1705357053 : ℕ)^1087*50000000000000^831 ≤ 4944659332553^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705357053 10000000000 4944659332553 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2807605921/5000000000 : ℝ)^1087 ≤ (9401241959323/20000000000000 : ℝ)^831 := by
    have hnat : (2807605921 : ℕ)^1087*20000000000000^831 ≤ 9401241959323^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2807605921 5000000000 9401241959323 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255283919/10000000000 : ℝ), (-1705357053/10000000000 : ℝ), (2807605921/5000000000 : ℝ)] ![(8620894304619/20000000000000 : ℝ), (4944659332553/50000000000000 : ℝ), (9401241959323/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255283919/10000000000 : ℝ)|^1087 ≤ (8620894304619/20000000000000 : ℝ)^831
        have hw : |(5255283919/10000000000 : ℝ)|=(5255283919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1705357053/10000000000 : ℝ)|^1087 ≤ (4944659332553/50000000000000 : ℝ)^831
        have hw : |(-1705357053/10000000000 : ℝ)|=(1705357053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2807605921/5000000000 : ℝ)|^1087 ≤ (9401241959323/20000000000000 : ℝ)^831
        have hw : |(2807605921/5000000000 : ℝ)|=(2807605921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s1_6 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2627642157/5000000000 : ℝ)*x 0 + (5615212193/10000000000 : ℝ)*x 1 + (-426338997/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627642157/5000000000 : ℝ)^1087 ≤ (8620895152201/20000000000000 : ℝ)^831 := by
    have hnat : (2627642157 : ℕ)^1087*20000000000000^831 ≤ 8620895152201^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627642157 5000000000 8620895152201 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5615212193/10000000000 : ℝ)^1087 ≤ (1468944176253/3125000000000 : ℝ)^831 := by
    have hnat : (5615212193 : ℕ)^1087*3125000000000^831 ≤ 1468944176253^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5615212193 10000000000 1468944176253 3125000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (426338997/2500000000 : ℝ)^1087 ≤ (2472327646659/25000000000000 : ℝ)^831 := by
    have hnat : (426338997 : ℕ)^1087*25000000000000^831 ≤ 2472327646659^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426338997 2500000000 2472327646659 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627642157/5000000000 : ℝ), (5615212193/10000000000 : ℝ), (-426338997/2500000000 : ℝ)] ![(8620895152201/20000000000000 : ℝ), (1468944176253/3125000000000 : ℝ), (2472327646659/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627642157/5000000000 : ℝ)|^1087 ≤ (8620895152201/20000000000000 : ℝ)^831
        have hw : |(2627642157/5000000000 : ℝ)|=(2627642157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5615212193/10000000000 : ℝ)|^1087 ≤ (1468944176253/3125000000000 : ℝ)^831
        have hw : |(5615212193/10000000000 : ℝ)|=(5615212193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-426338997/2500000000 : ℝ)|^1087 ≤ (2472327646659/25000000000000 : ℝ)^831
        have hw : |(-426338997/2500000000 : ℝ)|=(426338997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s1_7 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4285039021/10000000000 : ℝ)*x 0 + (2451608073/5000000000 : ℝ)*x 1 + (748093139/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4285039021/10000000000 : ℝ)^1087 ≤ (33004550565067/100000000000000 : ℝ)^831 := by
    have hnat : (4285039021 : ℕ)^1087*100000000000000^831 ≤ 33004550565067^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4285039021 10000000000 33004550565067 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2451608073/5000000000 : ℝ)^1087 ≤ (39366774279559/100000000000000 : ℝ)^831 := by
    have hnat : (2451608073 : ℕ)^1087*100000000000000^831 ≤ 39366774279559^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2451608073 5000000000 39366774279559 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (748093139/2000000000 : ℝ)^1087 ≤ (27628675141763/100000000000000 : ℝ)^831 := by
    have hnat : (748093139 : ℕ)^1087*100000000000000^831 ≤ 27628675141763^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748093139 2000000000 27628675141763 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4285039021/10000000000 : ℝ), (2451608073/5000000000 : ℝ), (748093139/2000000000 : ℝ)] ![(33004550565067/100000000000000 : ℝ), (39366774279559/100000000000000 : ℝ), (27628675141763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4285039021/10000000000 : ℝ)|^1087 ≤ (33004550565067/100000000000000 : ℝ)^831
        have hw : |(4285039021/10000000000 : ℝ)|=(4285039021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2451608073/5000000000 : ℝ)|^1087 ≤ (39366774279559/100000000000000 : ℝ)^831
        have hw : |(2451608073/5000000000 : ℝ)|=(2451608073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(748093139/2000000000 : ℝ)|^1087 ≤ (27628675141763/100000000000000 : ℝ)^831
        have hw : |(748093139/2000000000 : ℝ)|=(748093139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1388_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1659/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (877/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (913/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19127/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1659/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (877/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1659/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (877/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1659/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (877/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1659/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (877/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1659/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (877/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1659/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (877/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (877/50000 : ℝ) ^ (4347/1024 : ℝ) ≤ (3513175356167/100000000000000000000 : ℝ) := by
    have hpowers : (877/50000 : ℝ)^4347 ≤ (3513175356167/100000000000000000000 : ℝ)^1024 := by
      have hnat : (877 : ℕ)^4347*100000000000000000000^1024 ≤ 3513175356167^1024*50000^4347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        877 50000 3513175356167 100000000000000000000 4347 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (877/50000 : ℝ)) (X := (3513175356167/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1659/6250 : ℝ) ^ (4347/1024 : ℝ) ≤ (35864908823998719/10000000000000000000 : ℝ) := by
    have hpowers : (1659/6250 : ℝ)^4347 ≤ (35864908823998719/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1659 : ℕ)^4347*10000000000000000000^1024 ≤ 35864908823998719^1024*6250^4347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1659 6250 35864908823998719 10000000000000000000 4347 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1659/6250 : ℝ)) (X := (35864908823998719/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000003513175356167/50000000000000000000 : ℝ) ≤ (1250000020689507/1250000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (50000003513175356167/50000000000000000000 : ℝ)^1024 ≤ (1250000020689507/1250000000000000 : ℝ)^4347 := by
      have hnat : (50000003513175356167 : ℕ)^1024*1250000000000000^4347 ≤ 1250000020689507^4347*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000003513175356167 50000000000000000000 1250000020689507 1250000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000020689507/1250000000000000 : ℝ)) (X := (50000003513175356167/50000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100358652601415343357/100000000000000000000 : ℝ) ≤ (10008437034059221/10000000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (100358652601415343357/100000000000000000000 : ℝ)^1024 ≤ (10008437034059221/10000000000000000 : ℝ)^4347 := by
      have hnat : (100358652601415343357 : ℕ)^1024*10000000000000000^4347 ≤ 10008437034059221^4347*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100358652601415343357 100000000000000000000 10008437034059221 10000000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008437034059221/10000000000000000 : ℝ)) (X := (100358652601415343357/100000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5035864908823998719/5000000000000000000 : ℝ) ≤ (5008436951301193/5000000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (5035864908823998719/5000000000000000000 : ℝ)^1024 ≤ (5008436951301193/5000000000000000 : ℝ)^4347 := by
      have hnat : (5035864908823998719 : ℕ)^1024*5000000000000000^4347 ≤ 5008436951301193^4347*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5035864908823998719 5000000000000000000 5008436951301193 5000000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008436951301193/5000000000000000 : ℝ)) (X := (5035864908823998719/5000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3513175356167/100000000000000000000 : ℝ) ≤ ((12393520378414680271/12395000000000000000 : ℝ)+2*(1687373708633/495800000000000 : ℝ)*(877/50000 : ℝ))^(4347/1024 : ℝ) := by
    rw [show (12393520378414680271/12395000000000000000 : ℝ)+2*(1687373708633/495800000000000 : ℝ)*(877/50000 : ℝ)=(1250000020689507/1250000000000000 : ℝ) by norm_num, show 1+2*(3513175356167/100000000000000000000 : ℝ)=(50000003513175356167/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35864908823998719/10000000000000000000 : ℝ)+(3513175356167/100000000000000000000 : ℝ) ≤ ((12393520378414680271/12395000000000000000 : ℝ)+(1687373708633/495800000000000 : ℝ)*((1659/6250 : ℝ)+(877/50000 : ℝ)))^(4347/1024 : ℝ) := by
    rw [show (12393520378414680271/12395000000000000000 : ℝ)+(1687373708633/495800000000000 : ℝ)*((1659/6250 : ℝ)+(877/50000 : ℝ))=(10008437034059221/10000000000000000 : ℝ) by norm_num, show 1+(35864908823998719/10000000000000000000 : ℝ)+(3513175356167/100000000000000000000 : ℝ)=(100358652601415343357/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35864908823998719/10000000000000000000 : ℝ) ≤ ((12393520378414680271/12395000000000000000 : ℝ)+2*(1687373708633/495800000000000 : ℝ)*(1659/6250 : ℝ))^(4347/1024 : ℝ) := by
    rw [show (12393520378414680271/12395000000000000000 : ℝ)+2*(1687373708633/495800000000000 : ℝ)*(1659/6250 : ℝ)=(5008436951301193/5000000000000000 : ℝ) by norm_num, show 1+2*(35864908823998719/10000000000000000000 : ℝ)=(5035864908823998719/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12393520378414680271/12395000000000000000 : ℝ)*(X 1 0+X 2 0)+(1687373708633/495800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (877/50000 : ℝ)) (hi := (1659/6250 : ℝ)) (c := (12393520378414680271/12395000000000000000 : ℝ)) (alpha := (1687373708633/495800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12393520378414680271/12395000000000000000 : ℝ)*(X 0 1+X 2 1)+(1687373708633/495800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (877/50000 : ℝ)) (hi := (1659/6250 : ℝ)) (c := (12393520378414680271/12395000000000000000 : ℝ)) (alpha := (1687373708633/495800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12393520378414680271/12395000000000000000 : ℝ)*(X 0 2+X 1 2)+(1687373708633/495800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (877/50000 : ℝ)) (hi := (1659/6250 : ℝ)) (c := (12393520378414680271/12395000000000000000 : ℝ)) (alpha := (1687373708633/495800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-490115217/2500000000 : ℝ)*X 0 0+(2811051927/5000000000 : ℝ)*X 0 1+(506277143/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5400965353/10000000000 : ℝ)*X 1 0+(-451559233/2000000000 : ℝ)*X 1 1+(39552913/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5400966181/10000000000 : ℝ)*X 2 0+(5062771611/10000000000 : ℝ)*X 2 1+(-2257796689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4284060823/10000000000 : ℝ)*X 0 0+(931445587/2500000000 : ℝ)*X 0 1+(1229412107/2500000000 : ℝ)*X 0 2+(4284060823/10000000000 : ℝ)*X 1 0+(931445587/2500000000 : ℝ)*X 1 1+(1229412107/2500000000 : ℝ)*X 1 2+(4284060823/10000000000 : ℝ)*X 2 0+(931445587/2500000000 : ℝ)*X 2 1+(1229412107/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-196091921/1000000000 : ℝ)*X 0 0+(5069544673/10000000000 : ℝ)*X 0 1+(5615211799/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5255283919/10000000000 : ℝ)*X 1 0+(-1705357053/10000000000 : ℝ)*X 1 1+(2807605921/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2627642157/5000000000 : ℝ)*X 2 0+(5615212193/10000000000 : ℝ)*X 2 1+(-426338997/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4285039021/10000000000 : ℝ)*X 0 0+(2451608073/5000000000 : ℝ)*X 0 1+(748093139/2000000000 : ℝ)*X 0 2+(4285039021/10000000000 : ℝ)*X 1 0+(2451608073/5000000000 : ℝ)*X 1 1+(748093139/2000000000 : ℝ)*X 1 2+(4285039021/10000000000 : ℝ)*X 2 0+(2451608073/5000000000 : ℝ)*X 2 1+(748093139/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (809659420073507652890061189/123950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (554813391/50000000000000 : ℝ)*(base19) + (1360273347/100000000000000 : ℝ)*(base23) + (196339897/100000000000000 : ℝ)*(upper3) + (12662081/100000000000000 : ℝ)*(upper4) + (13914729/100000000000000 : ℝ)*(upper5) + (262689742361251/20000000000000 : ℝ)*(major0) + (262689742361251/20000000000000 : ℝ)*(major1) + (262689742361251/20000000000000 : ℝ)*(major2) + (1787857780092601/100000000000000 : ℝ)*(sp0) + (1787867674159013/100000000000000 : ℝ)*(sp1) + (13967714246191/781250000000 : ℝ)*(sp2) + (839023763257211/100000000000000 : ℝ)*(sp3) + (5501846597/50000000000000 : ℝ)*(sp4) + (2329415659/50000000000000 : ℝ)*(sp7) + (52439276380533/6250000000000 : ℝ)*(f.failure) + (893934391892897/50000000000000 : ℝ)*(f.sum) + (8047747181649/4958000000000000000000000000 : ℝ)*base65 + (107730867247145979/247900000000000000000000000000000 : ℝ)*base68 + (2387326077174945979/247900000000000000000000000000000 : ℝ)*base70 + (222525733826345979/247900000000000000000000000000000 : ℝ)*base72 + (1184260546651/991600000000000000000000000 : ℝ)*base74 + (1498713106803345979/247900000000000000000000000000000 : ℝ)*base76 + (1029401685128445979/247900000000000000000000000000000 : ℝ)*base78 + (1126965250031945979/247900000000000000000000000000000 : ℝ)*base80 + (8398922938597/991600000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1134269/625000000000000000000 : ℝ)*base90 + (1134269/625000000000000000000 : ℝ)*base92 + (1134269/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3235784659016340534422947923/619750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (174024609/100000000000000 : ℝ)*(base1) + (17356401/1250000000000 : ℝ)*(base19) + (1612778641/100000000000000 : ℝ)*(base23) + (13407819/10000000000000 : ℝ)*(upper3) + (101907997/50000000000000 : ℝ)*(upper5) + (1346325214075471/100000000000000 : ℝ)*(major0) + (1346325214075471/100000000000000 : ℝ)*(major1) + (1346325214075471/100000000000000 : ℝ)*(major2) + (6967587781/100000000000000 : ℝ)*(sp1) + (403550077/4000000000000 : ℝ)*(sp2) + (916310280927943/50000000000000 : ℝ)*(sp4) + (229076503966427/12500000000000 : ℝ)*(sp5) + (183260868630071/10000000000000 : ℝ)*(sp6) + (860029692257957/100000000000000 : ℝ)*(sp7) + (430014933141283/50000000000000 : ℝ)*(f.failure) + (1832620387831277/100000000000000 : ℝ)*(f.sum) + (15428467023913/24790000000000000000000000000 : ℝ)*base65 + (1439517732142692359/1239500000000000000000000000000000 : ℝ)*base68 + (12461294310588192359/1239500000000000000000000000000000 : ℝ)*base70 + (4480534417655692359/1239500000000000000000000000000000 : ℝ)*base72 + (79741987746033/24790000000000000000000000000 : ℝ)*base73 + (2132050144597192359/1239500000000000000000000000000000 : ℝ)*base76 + (508874056208307641/1239500000000000000000000000000000 : ℝ)*base77 + (9340211819840807641/1239500000000000000000000000000000 : ℝ)*base79 + (139285607473757/24790000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (12059019/5000000000000000000000 : ℝ)*base90 + (12059019/5000000000000000000000 : ℝ)*base92 + (12059019/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1388_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1659/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (877/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (913/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19127/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1388_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1388_s2_0 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1996767849/10000000000 : ℝ)*x 0 + (5467805291/10000000000 : ℝ)*x 1 + (5193752929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1996767849/10000000000 : ℝ)^1087 ≤ (12155831916469/100000000000000 : ℝ)^831 := by
    have hnat : (1996767849 : ℕ)^1087*100000000000000^831 ≤ 12155831916469^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1996767849 10000000000 12155831916469 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467805291/10000000000 : ℝ)^1087 ≤ (283741635989/625000000000 : ℝ)^831 := by
    have hnat : (5467805291 : ℕ)^1087*625000000000^831 ≤ 283741635989^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467805291 10000000000 283741635989 625000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5193752929/10000000000 : ℝ)^1087 ≤ (42445506301523/100000000000000 : ℝ)^831 := by
    have hnat : (5193752929 : ℕ)^1087*100000000000000^831 ≤ 42445506301523^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193752929 10000000000 42445506301523 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1996767849/10000000000 : ℝ), (5467805291/10000000000 : ℝ), (5193752929/10000000000 : ℝ)] ![(12155831916469/100000000000000 : ℝ), (283741635989/625000000000 : ℝ), (42445506301523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1996767849/10000000000 : ℝ)|^1087 ≤ (12155831916469/100000000000000 : ℝ)^831
        have hw : |(-1996767849/10000000000 : ℝ)|=(1996767849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5467805291/10000000000 : ℝ)|^1087 ≤ (283741635989/625000000000 : ℝ)^831
        have hw : |(5467805291/10000000000 : ℝ)|=(5467805291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5193752929/10000000000 : ℝ)|^1087 ≤ (42445506301523/100000000000000 : ℝ)^831
        have hw : |(5193752929/10000000000 : ℝ)|=(5193752929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s2_1 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2681402041/5000000000 : ℝ)*x 0 + (-267254421/1250000000 : ℝ)*x 1 + (259687643/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681402041/5000000000 : ℝ)^1087 ≤ (22130830763091/50000000000000 : ℝ)^831 := by
    have hnat : (2681402041 : ℕ)^1087*50000000000000^831 ≤ 22130830763091^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681402041 5000000000 22130830763091 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267254421/1250000000 : ℝ)^1087 ≤ (13292832897523/100000000000000 : ℝ)^831 := by
    have hnat : (267254421 : ℕ)^1087*100000000000000^831 ≤ 13292832897523^831*1250000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267254421 1250000000 13292832897523 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259687643/500000000 : ℝ)^1087 ≤ (42445505563911/100000000000000 : ℝ)^831 := by
    have hnat : (259687643 : ℕ)^1087*100000000000000^831 ≤ 42445505563911^831*500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259687643 500000000 42445505563911 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681402041/5000000000 : ℝ), (-267254421/1250000000 : ℝ), (259687643/500000000 : ℝ)] ![(22130830763091/50000000000000 : ℝ), (13292832897523/100000000000000 : ℝ), (42445505563911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681402041/5000000000 : ℝ)|^1087 ≤ (22130830763091/50000000000000 : ℝ)^831
        have hw : |(2681402041/5000000000 : ℝ)|=(2681402041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-267254421/1250000000 : ℝ)|^1087 ≤ (13292832897523/100000000000000 : ℝ)^831
        have hw : |(-267254421/1250000000 : ℝ)|=(267254421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259687643/500000000 : ℝ)|^1087 ≤ (42445505563911/100000000000000 : ℝ)^831
        have hw : |(259687643/500000000 : ℝ)|=(259687643/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s2_2 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5362803923/10000000000 : ℝ)*x 0 + (2596876513/5000000000 : ℝ)*x 1 + (-2138035361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362803923/10000000000 : ℝ)^1087 ≤ (44261659809613/100000000000000 : ℝ)^831 := by
    have hnat : (5362803923 : ℕ)^1087*100000000000000^831 ≤ 44261659809613^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362803923 10000000000 44261659809613 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2596876513/5000000000 : ℝ)^1087 ≤ (5305688417307/12500000000000 : ℝ)^831 := by
    have hnat : (2596876513 : ℕ)^1087*12500000000000^831 ≤ 5305688417307^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596876513 5000000000 5305688417307 12500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2138035361/10000000000 : ℝ)^1087 ≤ (6646416420297/50000000000000 : ℝ)^831 := by
    have hnat : (2138035361 : ℕ)^1087*50000000000000^831 ≤ 6646416420297^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138035361 10000000000 6646416420297 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362803923/10000000000 : ℝ), (2596876513/5000000000 : ℝ), (-2138035361/10000000000 : ℝ)] ![(44261659809613/100000000000000 : ℝ), (5305688417307/12500000000000 : ℝ), (6646416420297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362803923/10000000000 : ℝ)|^1087 ≤ (44261659809613/100000000000000 : ℝ)^831
        have hw : |(5362803923/10000000000 : ℝ)|=(5362803923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2596876513/5000000000 : ℝ)|^1087 ≤ (5305688417307/12500000000000 : ℝ)^831
        have hw : |(2596876513/5000000000 : ℝ)|=(2596876513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2138035361/10000000000 : ℝ)|^1087 ≤ (6646416420297/50000000000000 : ℝ)^831
        have hw : |(-2138035361/10000000000 : ℝ)|=(2138035361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s2_3 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2154790147/5000000000 : ℝ)*x 0 + (4026631089/10000000000 : ℝ)*x 1 + (4610604161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154790147/5000000000 : ℝ)^1087 ≤ (8313005787733/25000000000000 : ℝ)^831 := by
    have hnat : (2154790147 : ℕ)^1087*25000000000000^831 ≤ 8313005787733^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154790147 5000000000 8313005787733 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4026631089/10000000000 : ℝ)^1087 ≤ (30425604031757/100000000000000 : ℝ)^831 := by
    have hnat : (4026631089 : ℕ)^1087*100000000000000^831 ≤ 30425604031757^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026631089 10000000000 30425604031757 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4610604161/10000000000 : ℝ)^1087 ≤ (2270148299867/6250000000000 : ℝ)^831 := by
    have hnat : (4610604161 : ℕ)^1087*6250000000000^831 ≤ 2270148299867^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4610604161 10000000000 2270148299867 6250000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154790147/5000000000 : ℝ), (4026631089/10000000000 : ℝ), (4610604161/10000000000 : ℝ)] ![(8313005787733/25000000000000 : ℝ), (30425604031757/100000000000000 : ℝ), (2270148299867/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154790147/5000000000 : ℝ)|^1087 ≤ (8313005787733/25000000000000 : ℝ)^831
        have hw : |(2154790147/5000000000 : ℝ)|=(2154790147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4026631089/10000000000 : ℝ)|^1087 ≤ (30425604031757/100000000000000 : ℝ)^831
        have hw : |(4026631089/10000000000 : ℝ)|=(4026631089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4610604161/10000000000 : ℝ)|^1087 ≤ (2270148299867/6250000000000 : ℝ)^831
        have hw : |(4610604161/10000000000 : ℝ)|=(4610604161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s2_4 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-998410761/5000000000 : ℝ)*x 0 + (5195388551/10000000000 : ℝ)*x 1 + (5466155867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (998410761/5000000000 : ℝ)^1087 ≤ (12156259325111/100000000000000 : ℝ)^831 := by
    have hnat : (998410761 : ℕ)^1087*100000000000000^831 ≤ 12156259325111^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998410761 5000000000 12156259325111 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195388551/10000000000 : ℝ)^1087 ≤ (42462991999011/100000000000000 : ℝ)^831 := by
    have hnat : (5195388551 : ℕ)^1087*100000000000000^831 ≤ 42462991999011^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195388551 10000000000 42462991999011 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5466155867/10000000000 : ℝ)^1087 ≤ (11345187165507/25000000000000 : ℝ)^831 := by
    have hnat : (5466155867 : ℕ)^1087*25000000000000^831 ≤ 11345187165507^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466155867 10000000000 11345187165507 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-998410761/5000000000 : ℝ), (5195388551/10000000000 : ℝ), (5466155867/10000000000 : ℝ)] ![(12156259325111/100000000000000 : ℝ), (42462991999011/100000000000000 : ℝ), (11345187165507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-998410761/5000000000 : ℝ)|^1087 ≤ (12156259325111/100000000000000 : ℝ)^831
        have hw : |(-998410761/5000000000 : ℝ)|=(998410761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195388551/10000000000 : ℝ)|^1087 ≤ (42462991999011/100000000000000 : ℝ)^831
        have hw : |(5195388551/10000000000 : ℝ)|=(5195388551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5466155867/10000000000 : ℝ)|^1087 ≤ (11345187165507/25000000000000 : ℝ)^831
        have hw : |(5466155867/10000000000 : ℝ)|=(5466155867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s2_5 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1322956417/2500000000 : ℝ)*x 0 + (-1865633003/10000000000 : ℝ)*x 1 + (5466155553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322956417/2500000000 : ℝ)^1087 ≤ (21748471519321/50000000000000 : ℝ)^831 := by
    have hnat : (1322956417 : ℕ)^1087*50000000000000^831 ≤ 21748471519321^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322956417 2500000000 21748471519321 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1865633003/10000000000 : ℝ)^1087 ≤ (11122311704213/100000000000000 : ℝ)^831 := by
    have hnat : (1865633003 : ℕ)^1087*100000000000000^831 ≤ 11122311704213^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865633003 10000000000 11122311704213 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5466155553/10000000000 : ℝ)^1087 ≤ (567259315651/1250000000000 : ℝ)^831 := by
    have hnat : (5466155553 : ℕ)^1087*1250000000000^831 ≤ 567259315651^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466155553 10000000000 567259315651 1250000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322956417/2500000000 : ℝ), (-1865633003/10000000000 : ℝ), (5466155553/10000000000 : ℝ)] ![(21748471519321/50000000000000 : ℝ), (11122311704213/100000000000000 : ℝ), (567259315651/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322956417/2500000000 : ℝ)|^1087 ≤ (21748471519321/50000000000000 : ℝ)^831
        have hw : |(1322956417/2500000000 : ℝ)|=(1322956417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1865633003/10000000000 : ℝ)|^1087 ≤ (11122311704213/100000000000000 : ℝ)^831
        have hw : |(-1865633003/10000000000 : ℝ)|=(1865633003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5466155553/10000000000 : ℝ)|^1087 ≤ (567259315651/1250000000000 : ℝ)^831
        have hw : |(5466155553/10000000000 : ℝ)|=(5466155553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s2_6 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5291827117/10000000000 : ℝ)*x 0 + (5466155581/10000000000 : ℝ)*x 1 + (-466407741/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291827117/10000000000 : ℝ)^1087 ≤ (43496958618021/100000000000000 : ℝ)^831 := by
    have hnat : (5291827117 : ℕ)^1087*100000000000000^831 ≤ 43496958618021^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291827117 10000000000 43496958618021 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5466155581/10000000000 : ℝ)^1087 ≤ (45380745556151/100000000000000 : ℝ)^831 := by
    have hnat : (5466155581 : ℕ)^1087*100000000000000^831 ≤ 45380745556151^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466155581 10000000000 45380745556151 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (466407741/2500000000 : ℝ)^1087 ≤ (1390286975447/12500000000000 : ℝ)^831 := by
    have hnat : (466407741 : ℕ)^1087*12500000000000^831 ≤ 1390286975447^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466407741 2500000000 1390286975447 12500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291827117/10000000000 : ℝ), (5466155581/10000000000 : ℝ), (-466407741/2500000000 : ℝ)] ![(43496958618021/100000000000000 : ℝ), (45380745556151/100000000000000 : ℝ), (1390286975447/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291827117/10000000000 : ℝ)|^1087 ≤ (43496958618021/100000000000000 : ℝ)^831
        have hw : |(5291827117/10000000000 : ℝ)|=(5291827117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5466155581/10000000000 : ℝ)|^1087 ≤ (45380745556151/100000000000000 : ℝ)^831
        have hw : |(5466155581/10000000000 : ℝ)|=(5466155581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-466407741/2500000000 : ℝ)|^1087 ≤ (1390286975447/12500000000000 : ℝ)^831
        have hw : |(-466407741/2500000000 : ℝ)|=(466407741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s2_7 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2154848063/5000000000 : ℝ)*x 0 + (2303559687/5000000000 : ℝ)*x 1 + (2015072581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154848063/5000000000 : ℝ)^1087 ≤ (33253192224849/100000000000000 : ℝ)^831 := by
    have hnat : (2154848063 : ℕ)^1087*100000000000000^831 ≤ 33253192224849^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154848063 5000000000 33253192224849 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2303559687/5000000000 : ℝ)^1087 ≤ (3628646650577/10000000000000 : ℝ)^831 := by
    have hnat : (2303559687 : ℕ)^1087*10000000000000^831 ≤ 3628646650577^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2303559687 5000000000 3628646650577 10000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015072581/5000000000 : ℝ)^1087 ≤ (3807542656179/12500000000000 : ℝ)^831 := by
    have hnat : (2015072581 : ℕ)^1087*12500000000000^831 ≤ 3807542656179^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015072581 5000000000 3807542656179 12500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154848063/5000000000 : ℝ), (2303559687/5000000000 : ℝ), (2015072581/5000000000 : ℝ)] ![(33253192224849/100000000000000 : ℝ), (3628646650577/10000000000000 : ℝ), (3807542656179/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154848063/5000000000 : ℝ)|^1087 ≤ (33253192224849/100000000000000 : ℝ)^831
        have hw : |(2154848063/5000000000 : ℝ)|=(2154848063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2303559687/5000000000 : ℝ)|^1087 ≤ (3628646650577/10000000000000 : ℝ)^831
        have hw : |(2303559687/5000000000 : ℝ)|=(2303559687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2015072581/5000000000 : ℝ)|^1087 ≤ (3807542656179/12500000000000 : ℝ)^831
        have hw : |(2015072581/5000000000 : ℝ)|=(2015072581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1388_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19127/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (913/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10137/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15933/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19127/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (913/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19127/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (913/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19127/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (913/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19127/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (913/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19127/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (913/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19127/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (913/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (913/12500 : ℝ) ^ (4347/1024 : ℝ) ≤ (299717612625463/20000000000000000000 : ℝ) := by
    have hpowers : (913/12500 : ℝ)^4347 ≤ (299717612625463/20000000000000000000 : ℝ)^1024 := by
      have hnat : (913 : ℕ)^4347*20000000000000000000^1024 ≤ 299717612625463^1024*12500^4347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        913 12500 299717612625463 20000000000000000000 4347 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (913/12500 : ℝ)) (X := (299717612625463/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19127/100000 : ℝ) ^ (4347/1024 : ℝ) ≤ (17845828920831737/20000000000000000000 : ℝ) := by
    have hpowers : (19127/100000 : ℝ)^4347 ≤ (17845828920831737/20000000000000000000 : ℝ)^1024 := by
      have hnat : (19127 : ℕ)^4347*20000000000000000000^1024 ≤ 17845828920831737^1024*100000^4347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19127 100000 17845828920831737 20000000000000000000 4347 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19127/100000 : ℝ)) (X := (17845828920831737/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000299717612625463/10000000000000000000 : ℝ) ≤ (2500017650524471/2500000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (10000299717612625463/10000000000000000000 : ℝ)^1024 ≤ (2500017650524471/2500000000000000 : ℝ)^4347 := by
      have hnat : (10000299717612625463 : ℕ)^1024*2500000000000000^4347 ≤ 2500017650524471^4347*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000299717612625463 10000000000000000000 2500017650524471 2500000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500017650524471/2500000000000000 : ℝ)) (X := (10000299717612625463/10000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50045363866333643/50000000000000000 : ℝ) ≤ (80017091879091/80000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (50045363866333643/50000000000000000 : ℝ)^1024 ≤ (80017091879091/80000000000000 : ℝ)^4347 := by
      have hnat : (50045363866333643 : ℕ)^1024*80000000000000^4347 ≤ 80017091879091^4347*50000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50045363866333643 50000000000000000 80017091879091 80000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80017091879091/80000000000000 : ℝ)) (X := (50045363866333643/50000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10017845828920831737/10000000000000000000 : ℝ) ≤ (5002101183837433/5000000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (10017845828920831737/10000000000000000000 : ℝ)^1024 ≤ (5002101183837433/5000000000000000 : ℝ)^4347 := by
      have hnat : (10017845828920831737 : ℕ)^1024*5000000000000000^4347 ≤ 5002101183837433^4347*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10017845828920831737 10000000000000000000 5002101183837433 5000000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002101183837433/5000000000000000 : ℝ)) (X := (10017845828920831737/10000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(299717612625463/20000000000000000000 : ℝ) ≤ ((29550164078207251501/29557500000000000000 : ℝ)+2*(2065882788491/1182300000000000 : ℝ)*(913/12500 : ℝ))^(4347/1024 : ℝ) := by
    rw [show (29550164078207251501/29557500000000000000 : ℝ)+2*(2065882788491/1182300000000000 : ℝ)*(913/12500 : ℝ)=(2500017650524471/2500000000000000 : ℝ) by norm_num, show 1+2*(299717612625463/20000000000000000000 : ℝ)=(10000299717612625463/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17845828920831737/20000000000000000000 : ℝ)+(299717612625463/20000000000000000000 : ℝ) ≤ ((29550164078207251501/29557500000000000000 : ℝ)+(2065882788491/1182300000000000 : ℝ)*((19127/100000 : ℝ)+(913/12500 : ℝ)))^(4347/1024 : ℝ) := by
    rw [show (29550164078207251501/29557500000000000000 : ℝ)+(2065882788491/1182300000000000 : ℝ)*((19127/100000 : ℝ)+(913/12500 : ℝ))=(80017091879091/80000000000000 : ℝ) by norm_num, show 1+(17845828920831737/20000000000000000000 : ℝ)+(299717612625463/20000000000000000000 : ℝ)=(50045363866333643/50000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17845828920831737/20000000000000000000 : ℝ) ≤ ((29550164078207251501/29557500000000000000 : ℝ)+2*(2065882788491/1182300000000000 : ℝ)*(19127/100000 : ℝ))^(4347/1024 : ℝ) := by
    rw [show (29550164078207251501/29557500000000000000 : ℝ)+2*(2065882788491/1182300000000000 : ℝ)*(19127/100000 : ℝ)=(5002101183837433/5000000000000000 : ℝ) by norm_num, show 1+2*(17845828920831737/20000000000000000000 : ℝ)=(10017845828920831737/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29550164078207251501/29557500000000000000 : ℝ)*(X 1 0+X 2 0)+(2065882788491/1182300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (913/12500 : ℝ)) (hi := (19127/100000 : ℝ)) (c := (29550164078207251501/29557500000000000000 : ℝ)) (alpha := (2065882788491/1182300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29550164078207251501/29557500000000000000 : ℝ)*(X 0 1+X 2 1)+(2065882788491/1182300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (913/12500 : ℝ)) (hi := (19127/100000 : ℝ)) (c := (29550164078207251501/29557500000000000000 : ℝ)) (alpha := (2065882788491/1182300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29550164078207251501/29557500000000000000 : ℝ)*(X 0 2+X 1 2)+(2065882788491/1182300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (913/12500 : ℝ)) (hi := (19127/100000 : ℝ)) (c := (29550164078207251501/29557500000000000000 : ℝ)) (alpha := (2065882788491/1182300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1996767849/10000000000 : ℝ)*X 0 0+(5467805291/10000000000 : ℝ)*X 0 1+(5193752929/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2681402041/5000000000 : ℝ)*X 1 0+(-267254421/1250000000 : ℝ)*X 1 1+(259687643/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5362803923/10000000000 : ℝ)*X 2 0+(2596876513/5000000000 : ℝ)*X 2 1+(-2138035361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2154790147/5000000000 : ℝ)*X 0 0+(4026631089/10000000000 : ℝ)*X 0 1+(4610604161/10000000000 : ℝ)*X 0 2+(2154790147/5000000000 : ℝ)*X 1 0+(4026631089/10000000000 : ℝ)*X 1 1+(4610604161/10000000000 : ℝ)*X 1 2+(2154790147/5000000000 : ℝ)*X 2 0+(4026631089/10000000000 : ℝ)*X 2 1+(4610604161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-998410761/5000000000 : ℝ)*X 0 0+(5195388551/10000000000 : ℝ)*X 0 1+(5466155867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322956417/2500000000 : ℝ)*X 1 0+(-1865633003/10000000000 : ℝ)*X 1 1+(5466155553/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5291827117/10000000000 : ℝ)*X 2 0+(5466155581/10000000000 : ℝ)*X 2 1+(-466407741/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2154848063/5000000000 : ℝ)*X 0 0+(2303559687/5000000000 : ℝ)*X 0 1+(2015072581/5000000000 : ℝ)*X 0 2+(2154848063/5000000000 : ℝ)*X 1 0+(2303559687/5000000000 : ℝ)*X 1 1+(2015072581/5000000000 : ℝ)*X 1 2+(2154848063/5000000000 : ℝ)*X 2 0+(2303559687/5000000000 : ℝ)*X 2 1+(2015072581/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41672693633046782212706013/3848632812500000000000000000000 : ℝ) := by norm_num
    linear_combination (405574583/20000000000000 : ℝ)*(base19) + (217261937/12500000000000 : ℝ)*(base23) + (97383097/100000000000000 : ℝ)*(lower2) + (162023729/50000000000000 : ℝ)*(upper3) + (81039141/50000000000000 : ℝ)*(upper5) + (167544327717927/6250000000000 : ℝ)*(major0) + (167544327717927/6250000000000 : ℝ)*(major1) + (167544327717927/6250000000000 : ℝ)*(major2) + (1824481719541257/50000000000000 : ℝ)*(sp0) + (1824492185297001/50000000000000 : ℝ)*(sp1) + (1824492330185711/50000000000000 : ℝ)*(sp2) + (856209385361589/50000000000000 : ℝ)*(sp3) + (5739846101/25000000000000 : ℝ)*(sp4) + (12956852847/100000000000000 : ℝ)*(sp7) + (214053965947003/12500000000000 : ℝ)*(f.failure) + (1824493199233459/50000000000000 : ℝ)*(f.sum) + (40229027432849/4926250000000000000000000000 : ℝ)*base66 + (547842561969165941/61578125000000000000000000000000 : ℝ)*base68 + (19232712656165941/61578125000000000000000000000000 : ℝ)*base70 + (526361797863228441/61578125000000000000000000000000 : ℝ)*base72 + (17911075977679/4926250000000000000000000000 : ℝ)*base74 + (904853955919052809/61578125000000000000000000000000 : ℝ)*base75 + (517024850985447191/61578125000000000000000000000000 : ℝ)*base78 + (456219410268447191/61578125000000000000000000000000 : ℝ)*base80 + (284396954927/9852500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (738979/1250000000000000000000 : ℝ)*base90 + (738979/1250000000000000000000 : ℝ)*base92 + (738979/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (354952968791458422989591919/246312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54934567/12500000000000 : ℝ)*(base19) + (1847280583/100000000000000 : ℝ)*(base23) + (76086311/50000000000000 : ℝ)*(lower2) + (83284939/100000000000000 : ℝ)*(upper3) + (136261313/100000000000000 : ℝ)*(lower4) + (1356599893054473/50000000000000 : ℝ)*(major0) + (1356599893054473/50000000000000 : ℝ)*(major1) + (1356599893054473/50000000000000 : ℝ)*(major2) + (15903109689/50000000000000 : ℝ)*(sp2) + (142952199/10000000000000 : ℝ)*(sp3) + (1846606451333187/50000000000000 : ℝ)*(sp4) + (3693212463189839/100000000000000 : ℝ)*(sp5) + (1846589624583207/50000000000000 : ℝ)*(sp6) + (1733185191993931/100000000000000 : ℝ)*(sp7) + (21664832768949/1250000000000 : ℝ)*(f.failure) + (1846606451333187/50000000000000 : ℝ)*(f.sum) + (6074696757133/1231562500000000000000000000 : ℝ)*base66 + (1897996614208887009/492625000000000000000000000000000 : ℝ)*base68 + (423805509280387009/492625000000000000000000000000000 : ℝ)*base70 + (1941058660088887009/492625000000000000000000000000000 : ℝ)*base72 + (66653080872673/19705000000000000000000000000 : ℝ)*base74 + (8482810454676512009/492625000000000000000000000000000 : ℝ)*base76 + (2044943853598887009/492625000000000000000000000000000 : ℝ)*base78 + (291502294834887009/492625000000000000000000000000000 : ℝ)*base80 + (5948741274909/2463125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (861357/125000000000000000000 : ℝ)*base90 + (861357/125000000000000000000 : ℝ)*base92 + (861357/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1388_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19127/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (913/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10137/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15933/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1388_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1388_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10137/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15933/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1388_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1388_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1388_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10137/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15933/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1388_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

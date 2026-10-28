-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1150_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:35:23.534418+00:00
-- url     : https://prove2.me/submissions/68cf4627-3bf9-46d8-8767-83b4dfcae07d

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
theorem support_rectangle_w1150_s6_0 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2163036937/10000000000 : ℝ)*x 0 + (5393219979/10000000000 : ℝ)*x 1 + (1316389107/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163036937/10000000000 : ℝ)^8343 ≤ (1643029139031/12500000000000 : ℝ)^6295 := by
    have hnat : (2163036937 : ℕ)^8343*12500000000000^6295 ≤ 1643029139031^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163036937 10000000000 1643029139031 12500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393219979/10000000000 : ℝ)^8343 ≤ (441172322447/1000000000000 : ℝ)^6295 := by
    have hnat : (5393219979 : ℕ)^8343*1000000000000^6295 ≤ 441172322447^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393219979 10000000000 441172322447 1000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316389107/2500000000 : ℝ)^8343 ≤ (8547706925113/20000000000000 : ℝ)^6295 := by
    have hnat : (1316389107 : ℕ)^8343*20000000000000^6295 ≤ 8547706925113^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316389107 2500000000 8547706925113 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2163036937/10000000000 : ℝ), (5393219979/10000000000 : ℝ), (1316389107/2500000000 : ℝ)] ![(1643029139031/12500000000000 : ℝ), (441172322447/1000000000000 : ℝ), (8547706925113/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2163036937/10000000000 : ℝ)|^8343 ≤ (1643029139031/12500000000000 : ℝ)^6295
        have hw : |(-2163036937/10000000000 : ℝ)|=(2163036937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393219979/10000000000 : ℝ)|^8343 ≤ (441172322447/1000000000000 : ℝ)^6295
        have hw : |(5393219979/10000000000 : ℝ)|=(5393219979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316389107/2500000000 : ℝ)|^8343 ≤ (8547706925113/20000000000000 : ℝ)^6295
        have hw : |(1316389107/2500000000 : ℝ)|=(1316389107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s6_1 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336202727/2500000000 : ℝ)*x 0 + (-2227793323/10000000000 : ℝ)*x 1 + (5265556567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336202727/2500000000 : ℝ)^8343 ≤ (21796588231019/50000000000000 : ℝ)^6295 := by
    have hnat : (1336202727 : ℕ)^8343*50000000000000^6295 ≤ 21796588231019^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336202727 2500000000 21796588231019 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2227793323/10000000000 : ℝ)^8343 ≤ (13668287407353/100000000000000 : ℝ)^6295 := by
    have hnat : (2227793323 : ℕ)^8343*100000000000000^6295 ≤ 13668287407353^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2227793323 10000000000 13668287407353 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265556567/10000000000 : ℝ)^8343 ≤ (1709541444833/4000000000000 : ℝ)^6295 := by
    have hnat : (5265556567 : ℕ)^8343*4000000000000^6295 ≤ 1709541444833^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265556567 10000000000 1709541444833 4000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336202727/2500000000 : ℝ), (-2227793323/10000000000 : ℝ), (5265556567/10000000000 : ℝ)] ![(21796588231019/50000000000000 : ℝ), (13668287407353/100000000000000 : ℝ), (1709541444833/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336202727/2500000000 : ℝ)|^8343 ≤ (21796588231019/50000000000000 : ℝ)^6295
        have hw : |(1336202727/2500000000 : ℝ)|=(1336202727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2227793323/10000000000 : ℝ)|^8343 ≤ (13668287407353/100000000000000 : ℝ)^6295
        have hw : |(-2227793323/10000000000 : ℝ)|=(2227793323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265556567/10000000000 : ℝ)|^8343 ≤ (1709541444833/4000000000000 : ℝ)^6295
        have hw : |(5265556567/10000000000 : ℝ)|=(5265556567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s6_2 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068962299/2000000000 : ℝ)*x 0 + (2632778031/5000000000 : ℝ)*x 1 + (-2227793211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068962299/2000000000 : ℝ)^8343 ≤ (21796591403659/50000000000000 : ℝ)^6295 := by
    have hnat : (1068962299 : ℕ)^8343*50000000000000^6295 ≤ 21796591403659^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068962299 2000000000 21796591403659 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632778031/5000000000 : ℝ)^8343 ≤ (21369265344203/50000000000000 : ℝ)^6295 := by
    have hnat : (2632778031 : ℕ)^8343*50000000000000^6295 ≤ 21369265344203^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632778031 5000000000 21369265344203 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2227793211/10000000000 : ℝ)^8343 ≤ (2733657299327/20000000000000 : ℝ)^6295 := by
    have hnat : (2227793211 : ℕ)^8343*20000000000000^6295 ≤ 2733657299327^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2227793211 10000000000 2733657299327 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068962299/2000000000 : ℝ), (2632778031/5000000000 : ℝ), (-2227793211/10000000000 : ℝ)] ![(21796591403659/50000000000000 : ℝ), (21369265344203/50000000000000 : ℝ), (2733657299327/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068962299/2000000000 : ℝ)|^8343 ≤ (21796591403659/50000000000000 : ℝ)^6295
        have hw : |(1068962299/2000000000 : ℝ)|=(1068962299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632778031/5000000000 : ℝ)|^8343 ≤ (21369265344203/50000000000000 : ℝ)^6295
        have hw : |(2632778031/5000000000 : ℝ)|=(2632778031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2227793211/10000000000 : ℝ)|^8343 ≤ (2733657299327/20000000000000 : ℝ)^6295
        have hw : |(-2227793211/10000000000 : ℝ)|=(2227793211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s6_3 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4363531631/10000000000 : ℝ)*x 0 + (4238180277/10000000000 : ℝ)*x 1 + (2246281659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363531631/10000000000 : ℝ)^8343 ≤ (16658425270237/50000000000000 : ℝ)^6295 := by
    have hnat : (4363531631 : ℕ)^8343*50000000000000^6295 ≤ 16658425270237^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363531631 10000000000 16658425270237 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4238180277/10000000000 : ℝ)^8343 ≤ (32054343509781/100000000000000 : ℝ)^6295 := by
    have hnat : (4238180277 : ℕ)^8343*100000000000000^6295 ≤ 32054343509781^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238180277 10000000000 32054343509781 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246281659/5000000000 : ℝ)^8343 ≤ (34628805939477/100000000000000 : ℝ)^6295 := by
    have hnat : (2246281659 : ℕ)^8343*100000000000000^6295 ≤ 34628805939477^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246281659 5000000000 34628805939477 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363531631/10000000000 : ℝ), (4238180277/10000000000 : ℝ), (2246281659/5000000000 : ℝ)] ![(16658425270237/50000000000000 : ℝ), (32054343509781/100000000000000 : ℝ), (34628805939477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363531631/10000000000 : ℝ)|^8343 ≤ (16658425270237/50000000000000 : ℝ)^6295
        have hw : |(4363531631/10000000000 : ℝ)|=(4363531631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4238180277/10000000000 : ℝ)|^8343 ≤ (32054343509781/100000000000000 : ℝ)^6295
        have hw : |(4238180277/10000000000 : ℝ)|=(4238180277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246281659/5000000000 : ℝ)|^8343 ≤ (34628805939477/100000000000000 : ℝ)^6295
        have hw : |(2246281659/5000000000 : ℝ)|=(2246281659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s6_4 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-432608431/2000000000 : ℝ)*x 0 + (2632939289/5000000000 : ℝ)*x 1 + (84264007/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432608431/2000000000 : ℝ)^8343 ≤ (13144275136701/100000000000000 : ℝ)^6295 := by
    have hnat : (432608431 : ℕ)^8343*100000000000000^6295 ≤ 13144275136701^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432608431 2000000000 13144275136701 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632939289/5000000000 : ℝ)^8343 ≤ (42742000112957/100000000000000 : ℝ)^6295 := by
    have hnat : (2632939289 : ℕ)^8343*100000000000000^6295 ≤ 42742000112957^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632939289 5000000000 42742000112957 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84264007/156250000 : ℝ)^8343 ≤ (4411372473973/10000000000000 : ℝ)^6295 := by
    have hnat : (84264007 : ℕ)^8343*10000000000000^6295 ≤ 4411372473973^6295*156250000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84264007 156250000 4411372473973 10000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-432608431/2000000000 : ℝ), (2632939289/5000000000 : ℝ), (84264007/156250000 : ℝ)] ![(13144275136701/100000000000000 : ℝ), (42742000112957/100000000000000 : ℝ), (4411372473973/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-432608431/2000000000 : ℝ)|^8343 ≤ (13144275136701/100000000000000 : ℝ)^6295
        have hw : |(-432608431/2000000000 : ℝ)|=(432608431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632939289/5000000000 : ℝ)|^8343 ≤ (42742000112957/100000000000000 : ℝ)^6295
        have hw : |(2632939289/5000000000 : ℝ)|=(2632939289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84264007/156250000 : ℝ)|^8343 ≤ (4411372473973/10000000000000 : ℝ)^6295
        have hw : |(84264007/156250000 : ℝ)|=(84264007/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s6_5 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312448141/10000000000 : ℝ)*x 0 + (-2100452841/10000000000 : ℝ)*x 1 + (1348224113/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312448141/10000000000 : ℝ)^8343 ≤ (21621845236671/50000000000000 : ℝ)^6295 := by
    have hnat : (5312448141 : ℕ)^8343*50000000000000^6295 ≤ 21621845236671^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312448141 10000000000 21621845236671 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2100452841/10000000000 : ℝ)^8343 ≤ (2528516944993/20000000000000 : ℝ)^6295 := by
    have hnat : (2100452841 : ℕ)^8343*20000000000000^6295 ≤ 2528516944993^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100452841 10000000000 2528516944993 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348224113/2500000000 : ℝ)^8343 ≤ (8822744956619/20000000000000 : ℝ)^6295 := by
    have hnat : (1348224113 : ℕ)^8343*20000000000000^6295 ≤ 8822744956619^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348224113 2500000000 8822744956619 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312448141/10000000000 : ℝ), (-2100452841/10000000000 : ℝ), (1348224113/2500000000 : ℝ)] ![(21621845236671/50000000000000 : ℝ), (2528516944993/20000000000000 : ℝ), (8822744956619/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312448141/10000000000 : ℝ)|^8343 ≤ (21621845236671/50000000000000 : ℝ)^6295
        have hw : |(5312448141/10000000000 : ℝ)|=(5312448141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2100452841/10000000000 : ℝ)|^8343 ≤ (2528516944993/20000000000000 : ℝ)^6295
        have hw : |(-2100452841/10000000000 : ℝ)|=(2100452841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348224113/2500000000 : ℝ)|^8343 ≤ (8822744956619/20000000000000 : ℝ)^6295
        have hw : |(1348224113/2500000000 : ℝ)|=(1348224113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s6_6 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265622407/500000000 : ℝ)*x 0 + (2696448219/5000000000 : ℝ)*x 1 + (-1050226431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265622407/500000000 : ℝ)^8343 ≤ (21621845231277/50000000000000 : ℝ)^6295 := by
    have hnat : (265622407 : ℕ)^8343*50000000000000^6295 ≤ 21621845231277^6295*500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265622407 500000000 21621845231277 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696448219/5000000000 : ℝ)^8343 ≤ (44113724631317/100000000000000 : ℝ)^6295 := by
    have hnat : (2696448219 : ℕ)^8343*100000000000000^6295 ≤ 44113724631317^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696448219 5000000000 44113724631317 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050226431/5000000000 : ℝ)^8343 ≤ (2528516978497/20000000000000 : ℝ)^6295 := by
    have hnat : (1050226431 : ℕ)^8343*20000000000000^6295 ≤ 2528516978497^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050226431 5000000000 2528516978497 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265622407/500000000 : ℝ), (2696448219/5000000000 : ℝ), (-1050226431/5000000000 : ℝ)] ![(21621845231277/50000000000000 : ℝ), (44113724631317/100000000000000 : ℝ), (2528516978497/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265622407/500000000 : ℝ)|^8343 ≤ (21621845231277/50000000000000 : ℝ)^6295
        have hw : |(265622407/500000000 : ℝ)|=(265622407/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696448219/5000000000 : ℝ)|^8343 ≤ (44113724631317/100000000000000 : ℝ)^6295
        have hw : |(2696448219/5000000000 : ℝ)|=(2696448219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1050226431/5000000000 : ℝ)|^8343 ≤ (2528516978497/20000000000000 : ℝ)^6295
        have hw : |(-1050226431/5000000000 : ℝ)|=(1050226431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s6_7 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4363540817/10000000000 : ℝ)*x 0 + (4491920953/10000000000 : ℝ)*x 1 + (847765127/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363540817/10000000000 : ℝ)^8343 ≤ (4164617937099/12500000000000 : ℝ)^6295 := by
    have hnat : (4363540817 : ℕ)^8343*12500000000000^6295 ≤ 4164617937099^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363540817 10000000000 4164617937099 12500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491920953/10000000000 : ℝ)^8343 ≤ (34622243858473/100000000000000 : ℝ)^6295 := by
    have hnat : (4491920953 : ℕ)^8343*100000000000000^6295 ≤ 34622243858473^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491920953 10000000000 34622243858473 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847765127/2000000000 : ℝ)^8343 ≤ (32060812633021/100000000000000 : ℝ)^6295 := by
    have hnat : (847765127 : ℕ)^8343*100000000000000^6295 ≤ 32060812633021^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847765127 2000000000 32060812633021 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363540817/10000000000 : ℝ), (4491920953/10000000000 : ℝ), (847765127/2000000000 : ℝ)] ![(4164617937099/12500000000000 : ℝ), (34622243858473/100000000000000 : ℝ), (32060812633021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363540817/10000000000 : ℝ)|^8343 ≤ (4164617937099/12500000000000 : ℝ)^6295
        have hw : |(4363540817/10000000000 : ℝ)|=(4363540817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491920953/10000000000 : ℝ)|^8343 ≤ (34622243858473/100000000000000 : ℝ)^6295
        have hw : |(4491920953/10000000000 : ℝ)|=(4491920953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(847765127/2000000000 : ℝ)|^8343 ≤ (32060812633021/100000000000000 : ℝ)^6295
        have hw : |(847765127/2000000000 : ℝ)|=(847765127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1150_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11327/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11357/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14061/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3523/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11327/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3523/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11327/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3523/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11327/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3523/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11327/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3523/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11327/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3523/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11327/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11327/100000 : ℝ) ^ (4171/1024 : ℝ) ≤ (7016990887957551/50000000000000000000 : ℝ) := by
    have hpowers : (11327/100000 : ℝ)^4171 ≤ (7016990887957551/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11327 : ℕ)^4171*50000000000000000000^1024 ≤ 7016990887957551^1024*100000^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11327 100000 7016990887957551 50000000000000000000 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11327/100000 : ℝ)) (X := (7016990887957551/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3523/25000 : ℝ) ^ (4171/1024 : ℝ) ≤ (34163269910881597/100000000000000000000 : ℝ) := by
    have hpowers : (3523/25000 : ℝ)^4171 ≤ (34163269910881597/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3523 : ℕ)^4171*100000000000000000000^1024 ≤ 34163269910881597^1024*25000^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3523 25000 34163269910881597 100000000000000000000 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3523/25000 : ℝ)) (X := (34163269910881597/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007016990887957551/25000000000000000000 : ℝ) ≤ (10000689008675417/10000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (25007016990887957551/25000000000000000000 : ℝ)^1024 ≤ (10000689008675417/10000000000000000 : ℝ)^4171 := by
      have hnat : (25007016990887957551 : ℕ)^1024*10000000000000000^4171 ≤ 10000689008675417^4171*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007016990887957551 25000000000000000000 10000689008675417 10000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000689008675417/10000000000000000 : ℝ)) (X := (25007016990887957551/25000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048197251686796699/100000000000000000000 : ℝ) ≤ (2000236609995521/2000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (100048197251686796699/100000000000000000000 : ℝ)^1024 ≤ (2000236609995521/2000000000000000 : ℝ)^4171 := by
      have hnat : (100048197251686796699 : ℕ)^1024*2000000000000000^4171 ≤ 2000236609995521^4171*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048197251686796699 100000000000000000000 2000236609995521 2000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000236609995521/2000000000000000 : ℝ)) (X := (100048197251686796699/100000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034163269910881597/50000000000000000000 : ℝ) ≤ (10001677091279793/10000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (50034163269910881597/50000000000000000000 : ℝ)^1024 ≤ (10001677091279793/10000000000000000 : ℝ)^4171 := by
      have hnat : (50034163269910881597 : ℕ)^1024*10000000000000000^4171 ≤ 10001677091279793^4171*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034163269910881597 50000000000000000000 10001677091279793 10000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001677091279793/10000000000000000 : ℝ)) (X := (50034163269910881597/50000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7016990887957551/50000000000000000000 : ℝ) ≤ ((3948673299618251579/3950000000000000000 : ℝ)+2*(17644332221/9875000000000 : ℝ)*(11327/100000 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (3948673299618251579/3950000000000000000 : ℝ)+2*(17644332221/9875000000000 : ℝ)*(11327/100000 : ℝ)=(10000689008675417/10000000000000000 : ℝ) by norm_num, show 1+2*(7016990887957551/50000000000000000000 : ℝ)=(25007016990887957551/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34163269910881597/100000000000000000000 : ℝ)+(7016990887957551/50000000000000000000 : ℝ) ≤ ((3948673299618251579/3950000000000000000 : ℝ)+(17644332221/9875000000000 : ℝ)*((3523/25000 : ℝ)+(11327/100000 : ℝ)))^(4171/1024 : ℝ) := by
    rw [show (3948673299618251579/3950000000000000000 : ℝ)+(17644332221/9875000000000 : ℝ)*((3523/25000 : ℝ)+(11327/100000 : ℝ))=(2000236609995521/2000000000000000 : ℝ) by norm_num, show 1+(34163269910881597/100000000000000000000 : ℝ)+(7016990887957551/50000000000000000000 : ℝ)=(100048197251686796699/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34163269910881597/100000000000000000000 : ℝ) ≤ ((3948673299618251579/3950000000000000000 : ℝ)+2*(17644332221/9875000000000 : ℝ)*(3523/25000 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (3948673299618251579/3950000000000000000 : ℝ)+2*(17644332221/9875000000000 : ℝ)*(3523/25000 : ℝ)=(10001677091279793/10000000000000000 : ℝ) by norm_num, show 1+2*(34163269910881597/100000000000000000000 : ℝ)=(50034163269910881597/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3948673299618251579/3950000000000000000 : ℝ)*(X 1 0+X 2 0)+(17644332221/9875000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (11327/100000 : ℝ)) (hi := (3523/25000 : ℝ)) (c := (3948673299618251579/3950000000000000000 : ℝ)) (alpha := (17644332221/9875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3948673299618251579/3950000000000000000 : ℝ)*(X 0 1+X 2 1)+(17644332221/9875000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (11327/100000 : ℝ)) (hi := (3523/25000 : ℝ)) (c := (3948673299618251579/3950000000000000000 : ℝ)) (alpha := (17644332221/9875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3948673299618251579/3950000000000000000 : ℝ)*(X 0 2+X 1 2)+(17644332221/9875000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (11327/100000 : ℝ)) (hi := (3523/25000 : ℝ)) (c := (3948673299618251579/3950000000000000000 : ℝ)) (alpha := (17644332221/9875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2163036937/10000000000 : ℝ)*X 0 0+(5393219979/10000000000 : ℝ)*X 0 1+(1316389107/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336202727/2500000000 : ℝ)*X 1 0+(-2227793323/10000000000 : ℝ)*X 1 1+(5265556567/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068962299/2000000000 : ℝ)*X 2 0+(2632778031/5000000000 : ℝ)*X 2 1+(-2227793211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4363531631/10000000000 : ℝ)*X 0 0+(4238180277/10000000000 : ℝ)*X 0 1+(2246281659/5000000000 : ℝ)*X 0 2+(4363531631/10000000000 : ℝ)*X 1 0+(4238180277/10000000000 : ℝ)*X 1 1+(2246281659/5000000000 : ℝ)*X 1 2+(4363531631/10000000000 : ℝ)*X 2 0+(4238180277/10000000000 : ℝ)*X 2 1+(2246281659/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-432608431/2000000000 : ℝ)*X 0 0+(2632939289/5000000000 : ℝ)*X 0 1+(84264007/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312448141/10000000000 : ℝ)*X 1 0+(-2100452841/10000000000 : ℝ)*X 1 1+(1348224113/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265622407/500000000 : ℝ)*X 2 0+(2696448219/5000000000 : ℝ)*X 2 1+(-1050226431/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363540817/10000000000 : ℝ)*X 0 0+(4491920953/10000000000 : ℝ)*X 0 1+(847765127/2000000000 : ℝ)*X 0 2+(4363540817/10000000000 : ℝ)*X 1 0+(4491920953/10000000000 : ℝ)*X 1 1+(847765127/2000000000 : ℝ)*X 1 2+(4363540817/10000000000 : ℝ)*X 2 0+(4491920953/10000000000 : ℝ)*X 2 1+(847765127/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1116247552616570057253/197500000000000000000000000 : ℝ) := by norm_num
    linear_combination (32699573/50000000000000 : ℝ)*(base19) + (496877313/100000000000000 : ℝ)*(base23) + (183509409/50000000000000 : ℝ)*(lower2) + (139842567/100000000000000 : ℝ)*(upper3) + (137834403/100000000000000 : ℝ)*(lower4) + (80703339/50000000000000 : ℝ)*(upper5) + (1176416130248363/20000000000000 : ℝ)*(major0) + (1176416130248363/20000000000000 : ℝ)*(major1) + (1176416130248363/20000000000000 : ℝ)*(major2) + (7833072663523183/100000000000000 : ℝ)*(sp0) + (1958268149531009/25000000000000 : ℝ)*(sp1) + (783307216664587/10000000000000 : ℝ)*(sp2) + (1965540424724327/50000000000000 : ℝ)*(sp3) + (950139447/12500000000000 : ℝ)*(sp7) + (393108845056423/10000000000000 : ℝ)*(f.failure) + (7833072663523183/100000000000000 : ℝ)*(f.sum) + (2719366847867/395000000000000000000000000 : ℝ)*base65 + (232102813579115177/79000000000000000000000000000000 : ℝ)*base67 + (408674150647884823/79000000000000000000000000000000 : ℝ)*base70 + (179481647410115177/79000000000000000000000000000000 : ℝ)*base71 + (639889459509/197500000000000000000000000 : ℝ)*base74 + (992179596400115177/79000000000000000000000000000000 : ℝ)*base75 + (106537138587884823/79000000000000000000000000000000 : ℝ)*base78 + (550035958277884823/79000000000000000000000000000000 : ℝ)*base80 + (208317733549/197500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1723353/500000000000000000000 : ℝ)*base89 + (1723353/500000000000000000000 : ℝ)*base91 + (1723353/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (669564923486032288856168019/98750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (168983177/12500000000000 : ℝ)*(base19) + (709970889/50000000000000 : ℝ)*(base23) + (142621187/100000000000000 : ℝ)*(upper3) + (36721991/100000000000000 : ℝ)*(lower4) + (250823/160000000000 : ℝ)*(upper5) + (2955996921120787/50000000000000 : ℝ)*(major0) + (2955996921120787/50000000000000 : ℝ)*(major1) + (2955996921120787/50000000000000 : ℝ)*(major2) + (1897859313/5000000000000 : ℝ)*(sp1) + (38027723237/100000000000000 : ℝ)*(sp2) + (7872907544572837/100000000000000 : ℝ)*(sp4) + (3936434117760581/50000000000000 : ℝ)*(sp5) + (7872868096907823/100000000000000 : ℝ)*(sp6) + (1975539956948413/50000000000000 : ℝ)*(sp7) + (1975539956948413/50000000000000 : ℝ)*(f.failure) + (7872907544572837/100000000000000 : ℝ)*(f.sum) + (680660312909/1975000000000000000000000000 : ℝ)*base66 + (1902898571206727327/197500000000000000000000000000000 : ℝ)*base68 + (1909634215698272673/197500000000000000000000000000000 : ℝ)*base69 + (1519422656706727327/197500000000000000000000000000000 : ℝ)*base72 + (334976302579/493750000000000000000000000 : ℝ)*base73 + (4522301741268272673/197500000000000000000000000000000 : ℝ)*base75 + (171529517774227327/197500000000000000000000000000000 : ℝ)*base78 + (1823041694151727327/197500000000000000000000000000000 : ℝ)*base80 + (12020469946341/1975000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (186243/2500000000000000000000 : ℝ)*base89 + (186243/2500000000000000000000 : ℝ)*base91 + (186243/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1150_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11327/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1150_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1150_s7_0 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-540765657/2500000000 : ℝ)*x 0 + (33705697/62500000 : ℝ)*x 1 + (5265848061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540765657/2500000000 : ℝ)^8343 ≤ (13144440021387/100000000000000 : ℝ)^6295 := by
    have hnat : (540765657 : ℕ)^8343*100000000000000^6295 ≤ 13144440021387^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540765657 2500000000 13144440021387 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33705697/62500000 : ℝ)^8343 ≤ (44113888138671/100000000000000 : ℝ)^6295 := by
    have hnat : (33705697 : ℕ)^8343*100000000000000^6295 ≤ 44113888138671^6295*62500000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33705697 62500000 44113888138671 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265848061/10000000000 : ℝ)^8343 ≤ (21370835913639/50000000000000 : ℝ)^6295 := by
    have hnat : (5265848061 : ℕ)^8343*50000000000000^6295 ≤ 21370835913639^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265848061 10000000000 21370835913639 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-540765657/2500000000 : ℝ), (33705697/62500000 : ℝ), (5265848061/10000000000 : ℝ)] ![(13144440021387/100000000000000 : ℝ), (44113888138671/100000000000000 : ℝ), (21370835913639/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-540765657/2500000000 : ℝ)|^8343 ≤ (13144440021387/100000000000000 : ℝ)^6295
        have hw : |(-540765657/2500000000 : ℝ)|=(540765657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33705697/62500000 : ℝ)|^8343 ≤ (44113888138671/100000000000000 : ℝ)^6295
        have hw : |(33705697/62500000 : ℝ)|=(33705697/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265848061/10000000000 : ℝ)|^8343 ≤ (21370835913639/50000000000000 : ℝ)^6295
        have hw : |(5265848061/10000000000 : ℝ)|=(5265848061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s7_1 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534473417/1000000000 : ℝ)*x 0 + (-2227509699/10000000000 : ℝ)*x 1 + (2632924031/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534473417/1000000000 : ℝ)^8343 ≤ (21796173475527/50000000000000 : ℝ)^6295 := by
    have hnat : (534473417 : ℕ)^8343*50000000000000^6295 ≤ 21796173475527^6295*1000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534473417 1000000000 21796173475527 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2227509699/10000000000 : ℝ)^8343 ≤ (6832990596431/50000000000000 : ℝ)^6295 := by
    have hnat : (2227509699 : ℕ)^8343*50000000000000^6295 ≤ 6832990596431^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2227509699 10000000000 6832990596431 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632924031/5000000000 : ℝ)^8343 ≤ (8548334367607/20000000000000 : ℝ)^6295 := by
    have hnat : (2632924031 : ℕ)^8343*20000000000000^6295 ≤ 8548334367607^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632924031 5000000000 8548334367607 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534473417/1000000000 : ℝ), (-2227509699/10000000000 : ℝ), (2632924031/5000000000 : ℝ)] ![(21796173475527/50000000000000 : ℝ), (6832990596431/50000000000000 : ℝ), (8548334367607/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534473417/1000000000 : ℝ)|^8343 ≤ (21796173475527/50000000000000 : ℝ)^6295
        have hw : |(534473417/1000000000 : ℝ)|=(534473417/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2227509699/10000000000 : ℝ)|^8343 ≤ (6832990596431/50000000000000 : ℝ)^6295
        have hw : |(-2227509699/10000000000 : ℝ)|=(2227509699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632924031/5000000000 : ℝ)|^8343 ≤ (8548334367607/20000000000000 : ℝ)^6295
        have hw : |(2632924031/5000000000 : ℝ)|=(2632924031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s7_2 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344734171/10000000000 : ℝ)*x 0 + (5265848063/10000000000 : ℝ)*x 1 + (-1113754849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344734171/10000000000 : ℝ)^8343 ≤ (5449043370233/12500000000000 : ℝ)^6295 := by
    have hnat : (5344734171 : ℕ)^8343*12500000000000^6295 ≤ 5449043370233^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344734171 10000000000 5449043370233 12500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265848063/10000000000 : ℝ)^8343 ≤ (42741671848793/100000000000000 : ℝ)^6295 := by
    have hnat : (5265848063 : ℕ)^8343*100000000000000^6295 ≤ 42741671848793^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265848063 10000000000 42741671848793 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1113754849/5000000000 : ℝ)^8343 ≤ (13665981184731/100000000000000 : ℝ)^6295 := by
    have hnat : (1113754849 : ℕ)^8343*100000000000000^6295 ≤ 13665981184731^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113754849 5000000000 13665981184731 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344734171/10000000000 : ℝ), (5265848063/10000000000 : ℝ), (-1113754849/5000000000 : ℝ)] ![(5449043370233/12500000000000 : ℝ), (42741671848793/100000000000000 : ℝ), (13665981184731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344734171/10000000000 : ℝ)|^8343 ≤ (5449043370233/12500000000000 : ℝ)^6295
        have hw : |(5344734171/10000000000 : ℝ)|=(5344734171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265848063/10000000000 : ℝ)|^8343 ≤ (42741671848793/100000000000000 : ℝ)^6295
        have hw : |(5265848063/10000000000 : ℝ)|=(5265848063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1113754849/5000000000 : ℝ)|^8343 ≤ (13665981184731/100000000000000 : ℝ)^6295
        have hw : |(-1113754849/5000000000 : ℝ)|=(1113754849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s7_3 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872709249/2000000000 : ℝ)*x 0 + (847755411/2000000000 : ℝ)*x 1 + (280747703/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872709249/2000000000 : ℝ)^8343 ≤ (6663399684927/20000000000000 : ℝ)^6295 := by
    have hnat : (872709249 : ℕ)^8343*20000000000000^6295 ≤ 6663399684927^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872709249 2000000000 6663399684927 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847755411/2000000000 : ℝ)^8343 ≤ (6412065130367/20000000000000 : ℝ)^6295 := by
    have hnat : (847755411 : ℕ)^8343*20000000000000^6295 ≤ 6412065130367^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847755411 2000000000 6412065130367 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280747703/625000000 : ℝ)^8343 ≤ (17311337956873/50000000000000 : ℝ)^6295 := by
    have hnat : (280747703 : ℕ)^8343*50000000000000^6295 ≤ 17311337956873^6295*625000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280747703 625000000 17311337956873 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872709249/2000000000 : ℝ), (847755411/2000000000 : ℝ), (280747703/625000000 : ℝ)] ![(6663399684927/20000000000000 : ℝ), (6412065130367/20000000000000 : ℝ), (17311337956873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872709249/2000000000 : ℝ)|^8343 ≤ (6663399684927/20000000000000 : ℝ)^6295
        have hw : |(872709249/2000000000 : ℝ)|=(872709249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(847755411/2000000000 : ℝ)|^8343 ≤ (6412065130367/20000000000000 : ℝ)^6295
        have hw : |(847755411/2000000000 : ℝ)|=(847755411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280747703/625000000 : ℝ)|^8343 ≤ (17311337956873/50000000000000 : ℝ)^6295
        have hw : |(280747703/625000000 : ℝ)|=(280747703/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s7_4 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1081533653/5000000000 : ℝ)*x 0 + (5266167553/10000000000 : ℝ)*x 1 + (2696295507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081533653/5000000000 : ℝ)^8343 ≤ (13144477696961/100000000000000 : ℝ)^6295 := by
    have hnat : (1081533653 : ℕ)^8343*100000000000000^6295 ≤ 13144477696961^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081533653 5000000000 13144477696961 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266167553/10000000000 : ℝ)^8343 ≤ (21372554391609/50000000000000 : ℝ)^6295 := by
    have hnat : (5266167553 : ℕ)^8343*50000000000000^6295 ≤ 21372554391609^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266167553 10000000000 21372554391609 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696295507/5000000000 : ℝ)^8343 ≤ (44110413493053/100000000000000 : ℝ)^6295 := by
    have hnat : (2696295507 : ℕ)^8343*100000000000000^6295 ≤ 44110413493053^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696295507 5000000000 44110413493053 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1081533653/5000000000 : ℝ), (5266167553/10000000000 : ℝ), (2696295507/5000000000 : ℝ)] ![(13144477696961/100000000000000 : ℝ), (21372554391609/50000000000000 : ℝ), (44110413493053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1081533653/5000000000 : ℝ)|^8343 ≤ (13144477696961/100000000000000 : ℝ)^6295
        have hw : |(-1081533653/5000000000 : ℝ)|=(1081533653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266167553/10000000000 : ℝ)|^8343 ≤ (21372554391609/50000000000000 : ℝ)^6295
        have hw : |(5266167553/10000000000 : ℝ)|=(5266167553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696295507/5000000000 : ℝ)|^8343 ≤ (44110413493053/100000000000000 : ℝ)^6295
        have hw : |(2696295507/5000000000 : ℝ)|=(2696295507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s7_5 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312523121/10000000000 : ℝ)*x 0 + (-2100766699/10000000000 : ℝ)*x 1 + (2696295443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312523121/10000000000 : ℝ)^8343 ≤ (43244499384803/100000000000000 : ℝ)^6295 := by
    have hnat : (5312523121 : ℕ)^8343*100000000000000^6295 ≤ 43244499384803^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312523121 10000000000 43244499384803 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2100766699/10000000000 : ℝ)^8343 ≤ (1580636060987/12500000000000 : ℝ)^6295 := by
    have hnat : (2100766699 : ℕ)^8343*12500000000000^6295 ≤ 1580636060987^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100766699 10000000000 1580636060987 12500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696295443/5000000000 : ℝ)^8343 ≤ (22055206052701/50000000000000 : ℝ)^6295 := by
    have hnat : (2696295443 : ℕ)^8343*50000000000000^6295 ≤ 22055206052701^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696295443 5000000000 22055206052701 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312523121/10000000000 : ℝ), (-2100766699/10000000000 : ℝ), (2696295443/5000000000 : ℝ)] ![(43244499384803/100000000000000 : ℝ), (1580636060987/12500000000000 : ℝ), (22055206052701/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312523121/10000000000 : ℝ)|^8343 ≤ (43244499384803/100000000000000 : ℝ)^6295
        have hw : |(5312523121/10000000000 : ℝ)|=(5312523121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2100766699/10000000000 : ℝ)|^8343 ≤ (1580636060987/12500000000000 : ℝ)^6295
        have hw : |(-2100766699/10000000000 : ℝ)|=(2100766699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696295443/5000000000 : ℝ)|^8343 ≤ (22055206052701/50000000000000 : ℝ)^6295
        have hw : |(2696295443/5000000000 : ℝ)|=(2696295443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s7_6 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (332032693/625000000 : ℝ)*x 0 + (539259089/1000000000 : ℝ)*x 1 + (-2100766739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332032693/625000000 : ℝ)^8343 ≤ (43244499028787/100000000000000 : ℝ)^6295 := by
    have hnat : (332032693 : ℕ)^8343*100000000000000^6295 ≤ 43244499028787^6295*625000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332032693 625000000 43244499028787 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539259089/1000000000 : ℝ)^8343 ≤ (44110412148767/100000000000000 : ℝ)^6295 := by
    have hnat : (539259089 : ℕ)^8343*100000000000000^6295 ≤ 44110412148767^6295*1000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539259089 1000000000 44110412148767 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2100766739/10000000000 : ℝ)^8343 ≤ (12645088806999/100000000000000 : ℝ)^6295 := by
    have hnat : (2100766739 : ℕ)^8343*100000000000000^6295 ≤ 12645088806999^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100766739 10000000000 12645088806999 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332032693/625000000 : ℝ), (539259089/1000000000 : ℝ), (-2100766739/10000000000 : ℝ)] ![(43244499028787/100000000000000 : ℝ), (44110412148767/100000000000000 : ℝ), (12645088806999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332032693/625000000 : ℝ)|^8343 ≤ (43244499028787/100000000000000 : ℝ)^6295
        have hw : |(332032693/625000000 : ℝ)|=(332032693/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539259089/1000000000 : ℝ)|^8343 ≤ (44110412148767/100000000000000 : ℝ)^6295
        have hw : |(539259089/1000000000 : ℝ)|=(539259089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2100766739/10000000000 : ℝ)|^8343 ≤ (12645088806999/100000000000000 : ℝ)^6295
        have hw : |(-2100766739/10000000000 : ℝ)|=(2100766739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s7_7 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4363555871/10000000000 : ℝ)*x 0 + (1122831669/2500000000 : ℝ)*x 1 + (529927001/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363555871/10000000000 : ℝ)^8343 ≤ (33317095833573/100000000000000 : ℝ)^6295 := by
    have hnat : (4363555871 : ℕ)^8343*100000000000000^6295 ≤ 33317095833573^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363555871 10000000000 33317095833573 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122831669/2500000000 : ℝ)^8343 ≤ (34616173292399/100000000000000 : ℝ)^6295 := by
    have hnat : (1122831669 : ℕ)^8343*100000000000000^6295 ≤ 34616173292399^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122831669 2500000000 34616173292399 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529927001/1250000000 : ℝ)^8343 ≤ (4008341357827/12500000000000 : ℝ)^6295 := by
    have hnat : (529927001 : ℕ)^8343*12500000000000^6295 ≤ 4008341357827^6295*1250000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529927001 1250000000 4008341357827 12500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363555871/10000000000 : ℝ), (1122831669/2500000000 : ℝ), (529927001/1250000000 : ℝ)] ![(33317095833573/100000000000000 : ℝ), (34616173292399/100000000000000 : ℝ), (4008341357827/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363555871/10000000000 : ℝ)|^8343 ≤ (33317095833573/100000000000000 : ℝ)^6295
        have hw : |(4363555871/10000000000 : ℝ)|=(4363555871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122831669/2500000000 : ℝ)|^8343 ≤ (34616173292399/100000000000000 : ℝ)^6295
        have hw : |(1122831669/2500000000 : ℝ)|=(1122831669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(529927001/1250000000 : ℝ)|^8343 ≤ (4008341357827/12500000000000 : ℝ)^6295
        have hw : |(529927001/1250000000 : ℝ)|=(529927001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1150_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11363/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7027/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14061/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11357/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14061/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11357/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14061/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11357/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14061/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11357/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14061/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11357/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14061/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11357/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11357/100000 : ℝ) ^ (4171/1024 : ℝ) ≤ (2837199927914993/20000000000000000000 : ℝ) := by
    have hpowers : (11357/100000 : ℝ)^4171 ≤ (2837199927914993/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11357 : ℕ)^4171*20000000000000000000^1024 ≤ 2837199927914993^1024*100000^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11357 100000 2837199927914993 20000000000000000000 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11357/100000 : ℝ)) (X := (2837199927914993/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14061/100000 : ℝ) ^ (4171/1024 : ℝ) ≤ (33858185210933771/100000000000000000000 : ℝ) := by
    have hpowers : (14061/100000 : ℝ)^4171 ≤ (33858185210933771/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14061 : ℕ)^4171*100000000000000000000^1024 ≤ 33858185210933771^1024*100000^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14061 100000 33858185210933771 100000000000000000000 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14061/100000 : ℝ)) (X := (33858185210933771/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002837199927914993/10000000000000000000 : ℝ) ≤ (10000696471305787/10000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (10002837199927914993/10000000000000000000 : ℝ)^1024 ≤ (10000696471305787/10000000000000000 : ℝ)^4171 := by
      have hnat : (10002837199927914993 : ℕ)^1024*10000000000000000^4171 ≤ 10000696471305787^4171*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002837199927914993 10000000000000000000 10000696471305787 10000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000696471305787/10000000000000000 : ℝ)) (X := (10002837199927914993/10000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1563250690388289199/1562500000000000000 : ℝ) ≤ (10001179293478999/10000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (1563250690388289199/1562500000000000000 : ℝ)^1024 ≤ (10001179293478999/10000000000000000 : ℝ)^4171 := by
      have hnat : (1563250690388289199 : ℕ)^1024*10000000000000000^4171 ≤ 10001179293478999^4171*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563250690388289199 1562500000000000000 10001179293478999 10000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001179293478999/10000000000000000 : ℝ)) (X := (1563250690388289199/1562500000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033858185210933771/50000000000000000000 : ℝ) ≤ (10001662115652211/10000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (50033858185210933771/50000000000000000000 : ℝ)^1024 ≤ (10001662115652211/10000000000000000 : ℝ)^4171 := by
      have hnat : (50033858185210933771 : ℕ)^1024*10000000000000000^4171 ≤ 10001662115652211^4171*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033858185210933771 50000000000000000000 10001662115652211 10000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001662115652211/10000000000000000 : ℝ)) (X := (50033858185210933771/50000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2837199927914993/20000000000000000000 : ℝ) ≤ ((675772910889212767/676000000000000000 : ℝ)+2*(120705543303/67600000000000 : ℝ)*(11357/100000 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (675772910889212767/676000000000000000 : ℝ)+2*(120705543303/67600000000000 : ℝ)*(11357/100000 : ℝ)=(10000696471305787/10000000000000000 : ℝ) by norm_num, show 1+2*(2837199927914993/20000000000000000000 : ℝ)=(10002837199927914993/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33858185210933771/100000000000000000000 : ℝ)+(2837199927914993/20000000000000000000 : ℝ) ≤ ((675772910889212767/676000000000000000 : ℝ)+(120705543303/67600000000000 : ℝ)*((14061/100000 : ℝ)+(11357/100000 : ℝ)))^(4171/1024 : ℝ) := by
    rw [show (675772910889212767/676000000000000000 : ℝ)+(120705543303/67600000000000 : ℝ)*((14061/100000 : ℝ)+(11357/100000 : ℝ))=(10001179293478999/10000000000000000 : ℝ) by norm_num, show 1+(33858185210933771/100000000000000000000 : ℝ)+(2837199927914993/20000000000000000000 : ℝ)=(1563250690388289199/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33858185210933771/100000000000000000000 : ℝ) ≤ ((675772910889212767/676000000000000000 : ℝ)+2*(120705543303/67600000000000 : ℝ)*(14061/100000 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (675772910889212767/676000000000000000 : ℝ)+2*(120705543303/67600000000000 : ℝ)*(14061/100000 : ℝ)=(10001662115652211/10000000000000000 : ℝ) by norm_num, show 1+2*(33858185210933771/100000000000000000000 : ℝ)=(50033858185210933771/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (675772910889212767/676000000000000000 : ℝ)*(X 1 0+X 2 0)+(120705543303/67600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (11357/100000 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (675772910889212767/676000000000000000 : ℝ)) (alpha := (120705543303/67600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (675772910889212767/676000000000000000 : ℝ)*(X 0 1+X 2 1)+(120705543303/67600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (11357/100000 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (675772910889212767/676000000000000000 : ℝ)) (alpha := (120705543303/67600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (675772910889212767/676000000000000000 : ℝ)*(X 0 2+X 1 2)+(120705543303/67600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (11357/100000 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (675772910889212767/676000000000000000 : ℝ)) (alpha := (120705543303/67600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-540765657/2500000000 : ℝ)*X 0 0+(33705697/62500000 : ℝ)*X 0 1+(5265848061/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534473417/1000000000 : ℝ)*X 1 0+(-2227509699/10000000000 : ℝ)*X 1 1+(2632924031/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344734171/10000000000 : ℝ)*X 2 0+(5265848063/10000000000 : ℝ)*X 2 1+(-1113754849/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((872709249/2000000000 : ℝ)*X 0 0+(847755411/2000000000 : ℝ)*X 0 1+(280747703/625000000 : ℝ)*X 0 2+(872709249/2000000000 : ℝ)*X 1 0+(847755411/2000000000 : ℝ)*X 1 1+(280747703/625000000 : ℝ)*X 1 2+(872709249/2000000000 : ℝ)*X 2 0+(847755411/2000000000 : ℝ)*X 2 1+(280747703/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1081533653/5000000000 : ℝ)*X 0 0+(5266167553/10000000000 : ℝ)*X 0 1+(2696295507/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312523121/10000000000 : ℝ)*X 1 0+(-2100766699/10000000000 : ℝ)*X 1 1+(2696295443/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((332032693/625000000 : ℝ)*X 2 0+(539259089/1000000000 : ℝ)*X 2 1+(-2100766739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363555871/10000000000 : ℝ)*X 0 0+(1122831669/2500000000 : ℝ)*X 0 1+(529927001/1250000000 : ℝ)*X 0 2+(4363555871/10000000000 : ℝ)*X 1 0+(1122831669/2500000000 : ℝ)*X 1 1+(529927001/1250000000 : ℝ)*X 1 2+(4363555871/10000000000 : ℝ)*X 2 0+(1122831669/2500000000 : ℝ)*X 2 1+(529927001/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4036884541821237765969/676000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1181353369/100000000000000 : ℝ)*(base19) + (1101522733/100000000000000 : ℝ)*(base23) + (4345437/10000000000000 : ℝ)*(lower2) + (75103691/50000000000000 : ℝ)*(upper3) + (93113107/100000000000000 : ℝ)*(upper5) + (1181984521225479/20000000000000 : ℝ)*(major0) + (1181984521225479/20000000000000 : ℝ)*(major1) + (1181984521225479/20000000000000 : ℝ)*(major2) + (7870117002353581/100000000000000 : ℝ)*(sp0) + (7870148158125019/100000000000000 : ℝ)*(sp1) + (1574029647591131/20000000000000 : ℝ)*(sp2) + (1974839113654557/50000000000000 : ℝ)*(sp3) + (32337124807/100000000000000 : ℝ)*(sp4) + (136300077/781250000000 : ℝ)*(sp7) + (394969567371897/10000000000000 : ℝ)*(f.failure) + (1967537334869597/25000000000000 : ℝ)*(f.sum) + (2966352986641/676000000000000000000000000 : ℝ)*base65 + (157351823461979607/13520000000000000000000000000000 : ℝ)*base68 + (59013880330180393/13520000000000000000000000000000 : ℝ)*base69 + (243228192166859607/13520000000000000000000000000000 : ℝ)*base72 + (2076109693117/676000000000000000000000000 : ℝ)*base73 + (314745728954900393/13520000000000000000000000000000 : ℝ)*base75 + (77466373115140393/13520000000000000000000000000000 : ℝ)*base77 + (143003126878459607/13520000000000000000000000000000 : ℝ)*base80 + (933264035543/676000000000000000000000000 : ℝ)*base82 + (2956167/500000000000000000000 : ℝ)*base89 + (2956167/500000000000000000000 : ℝ)*base91 + (2956167/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15342350515887045843/8450000000000000000000000 : ℝ) := by norm_num
    linear_combination (30648237/10000000000000 : ℝ)*(base19) + (255333471/50000000000000 : ℝ)*(base23) + (51884373/50000000000000 : ℝ)*(lower3) + (13441799/10000000000000 : ℝ)*(lower4) + (148494785698989/2500000000000 : ℝ)*(major0) + (148494785698989/2500000000000 : ℝ)*(major1) + (148494785698989/2500000000000 : ℝ)*(major2) + (7711391/3125000000000 : ℝ)*(sp0) + (11587104569/100000000000000 : ℝ)*(sp1) + (2909058223/25000000000000 : ℝ)*(sp2) + (7909925064204329/100000000000000 : ℝ)*(sp4) + (7909913417381901/100000000000000 : ℝ)*(sp5) + (3954956582034503/50000000000000 : ℝ)*(sp6) + (1984828742214089/50000000000000 : ℝ)*(sp7) + (1984828742214089/50000000000000 : ℝ)*(f.failure) + (7909925310968841/100000000000000 : ℝ)*(f.sum) + (573132190799/84500000000000000000000000 : ℝ)*base66 + (2047781398987437/1690000000000000000000000000000 : ℝ)*base68 + (13968360841682563/1690000000000000000000000000000 : ℝ)*base69 + (13730746808947437/1690000000000000000000000000000 : ℝ)*base72 + (56550958441/21125000000000000000000000 : ℝ)*base74 + (35076733394742563/1690000000000000000000000000000 : ℝ)*base75 + (785190161157437/1690000000000000000000000000000 : ℝ)*base78 + (9092481674302563/1690000000000000000000000000000 : ℝ)*base79 + (86562159609/21125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (11481079/2500000000000000000000 : ℝ)*base89 + (11481079/2500000000000000000000 : ℝ)*base91 + (11481079/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1150_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1150_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1150_s8_0 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2163070501/10000000000 : ℝ)*x 0 + (215713811/400000000 : ℝ)*x 1 + (5265908927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163070501/10000000000 : ℝ)^8343 ≤ (13144503428797/100000000000000 : ℝ)^6295 := by
    have hnat : (2163070501 : ℕ)^8343*100000000000000^6295 ≤ 13144503428797^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163070501 10000000000 13144503428797 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215713811/400000000 : ℝ)^8343 ≤ (11028292490709/25000000000000 : ℝ)^6295 := by
    have hnat : (215713811 : ℕ)^8343*25000000000000^6295 ≤ 11028292490709^6295*400000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215713811 400000000 11028292490709 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265908927/10000000000 : ℝ)^8343 ≤ (8548465318399/20000000000000 : ℝ)^6295 := by
    have hnat : (5265908927 : ℕ)^8343*20000000000000^6295 ≤ 8548465318399^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265908927 10000000000 8548465318399 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2163070501/10000000000 : ℝ), (215713811/400000000 : ℝ), (5265908927/10000000000 : ℝ)] ![(13144503428797/100000000000000 : ℝ), (11028292490709/25000000000000 : ℝ), (8548465318399/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2163070501/10000000000 : ℝ)|^8343 ≤ (13144503428797/100000000000000 : ℝ)^6295
        have hw : |(-2163070501/10000000000 : ℝ)|=(2163070501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215713811/400000000 : ℝ)|^8343 ≤ (11028292490709/25000000000000 : ℝ)^6295
        have hw : |(215713811/400000000 : ℝ)|=(215713811/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265908927/10000000000 : ℝ)|^8343 ≤ (8548465318399/20000000000000 : ℝ)^6295
        have hw : |(5265908927/10000000000 : ℝ)|=(5265908927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s8_1 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672358443/5000000000 : ℝ)*x 0 + (-111372611/500000000 : ℝ)*x 1 + (42127271/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672358443/5000000000 : ℝ)^8343 ≤ (2724510007349/6250000000000 : ℝ)^6295 := by
    have hnat : (2672358443 : ℕ)^8343*6250000000000^6295 ≤ 2724510007349^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672358443 5000000000 2724510007349 6250000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111372611/500000000 : ℝ)^8343 ≤ (546620553161/4000000000000 : ℝ)^6295 := by
    have hnat : (111372611 : ℕ)^8343*4000000000000^6295 ≤ 546620553161^6295*500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111372611 500000000 546620553161 4000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42127271/80000000 : ℝ)^8343 ≤ (8548465206521/20000000000000 : ℝ)^6295 := by
    have hnat : (42127271 : ℕ)^8343*20000000000000^6295 ≤ 8548465206521^6295*80000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42127271 80000000 8548465206521 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672358443/5000000000 : ℝ), (-111372611/500000000 : ℝ), (42127271/80000000 : ℝ)] ![(2724510007349/6250000000000 : ℝ), (546620553161/4000000000000 : ℝ), (8548465206521/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672358443/5000000000 : ℝ)|^8343 ≤ (2724510007349/6250000000000 : ℝ)^6295
        have hw : |(2672358443/5000000000 : ℝ)|=(2672358443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-111372611/500000000 : ℝ)|^8343 ≤ (546620553161/4000000000000 : ℝ)^6295
        have hw : |(-111372611/500000000 : ℝ)|=(111372611/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42127271/80000000 : ℝ)|^8343 ≤ (8548465206521/20000000000000 : ℝ)^6295
        have hw : |(42127271/80000000 : ℝ)|=(42127271/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s8_2 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344716839/10000000000 : ℝ)*x 0 + (5265908881/10000000000 : ℝ)*x 1 + (-556863069/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344716839/10000000000 : ℝ)^8343 ≤ (10898039902383/25000000000000 : ℝ)^6295 := by
    have hnat : (5344716839 : ℕ)^8343*25000000000000^6295 ≤ 10898039902383^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344716839 10000000000 10898039902383 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265908881/10000000000 : ℝ)^8343 ≤ (854846521943/2000000000000 : ℝ)^6295 := by
    have hnat : (5265908881 : ℕ)^8343*2000000000000^6295 ≤ 854846521943^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265908881 10000000000 854846521943 2000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (556863069/2500000000 : ℝ)^8343 ≤ (13665514284361/100000000000000 : ℝ)^6295 := by
    have hnat : (556863069 : ℕ)^8343*100000000000000^6295 ≤ 13665514284361^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556863069 2500000000 13665514284361 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344716839/10000000000 : ℝ), (5265908881/10000000000 : ℝ), (-556863069/2500000000 : ℝ)] ![(10898039902383/25000000000000 : ℝ), (854846521943/2000000000000 : ℝ), (13665514284361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344716839/10000000000 : ℝ)|^8343 ≤ (10898039902383/25000000000000 : ℝ)^6295
        have hw : |(5344716839/10000000000 : ℝ)|=(5344716839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265908881/10000000000 : ℝ)|^8343 ≤ (854846521943/2000000000000 : ℝ)^6295
        have hw : |(5265908881/10000000000 : ℝ)|=(5265908881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-556863069/2500000000 : ℝ)|^8343 ≤ (13665514284361/100000000000000 : ℝ)^6295
        have hw : |(-556863069/2500000000 : ℝ)|=(556863069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s8_3 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2181774763/5000000000 : ℝ)*x 0 + (529862907/1250000000 : ℝ)*x 1 + (2245918077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181774763/5000000000 : ℝ)^8343 ≤ (13014465479/39062500000 : ℝ)^6295 := by
    have hnat : (2181774763 : ℕ)^8343*39062500000^6295 ≤ 13014465479^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181774763 5000000000 13014465479 39062500000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529862907/1250000000 : ℝ)^8343 ≤ (32061590734087/100000000000000 : ℝ)^6295 := by
    have hnat : (529862907 : ℕ)^8343*100000000000000^6295 ≤ 32061590734087^6295*1250000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529862907 1250000000 32061590734087 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245918077/5000000000 : ℝ)^8343 ≤ (34621377616921/100000000000000 : ℝ)^6295 := by
    have hnat : (2245918077 : ℕ)^8343*100000000000000^6295 ≤ 34621377616921^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245918077 5000000000 34621377616921 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181774763/5000000000 : ℝ), (529862907/1250000000 : ℝ), (2245918077/5000000000 : ℝ)] ![(13014465479/39062500000 : ℝ), (32061590734087/100000000000000 : ℝ), (34621377616921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181774763/5000000000 : ℝ)|^8343 ≤ (13014465479/39062500000 : ℝ)^6295
        have hw : |(2181774763/5000000000 : ℝ)|=(2181774763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(529862907/1250000000 : ℝ)|^8343 ≤ (32061590734087/100000000000000 : ℝ)^6295
        have hw : |(529862907/1250000000 : ℝ)|=(529862907/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2245918077/5000000000 : ℝ)|^8343 ≤ (34621377616921/100000000000000 : ℝ)^6295
        have hw : |(2245918077/5000000000 : ℝ)|=(2245918077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s8_4 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-432615083/2000000000 : ℝ)*x 0 + (2633114017/5000000000 : ℝ)*x 1 + (215700999/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432615083/2000000000 : ℝ)^8343 ≤ (1314454300511/10000000000000 : ℝ)^6295 := by
    have hnat : (432615083 : ℕ)^8343*10000000000000^6295 ≤ 1314454300511^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432615083 2000000000 1314454300511 10000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633114017/5000000000 : ℝ)^8343 ≤ (42745759419141/100000000000000 : ℝ)^6295 := by
    have hnat : (2633114017 : ℕ)^8343*100000000000000^6295 ≤ 42745759419141^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633114017 5000000000 42745759419141 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215700999/400000000 : ℝ)^8343 ≤ (8821939512869/20000000000000 : ℝ)^6295 := by
    have hnat : (215700999 : ℕ)^8343*20000000000000^6295 ≤ 8821939512869^6295*400000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215700999 400000000 8821939512869 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-432615083/2000000000 : ℝ), (2633114017/5000000000 : ℝ), (215700999/400000000 : ℝ)] ![(1314454300511/10000000000000 : ℝ), (42745759419141/100000000000000 : ℝ), (8821939512869/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-432615083/2000000000 : ℝ)|^8343 ≤ (1314454300511/10000000000000 : ℝ)^6295
        have hw : |(-432615083/2000000000 : ℝ)|=(432615083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633114017/5000000000 : ℝ)|^8343 ≤ (42745759419141/100000000000000 : ℝ)^6295
        have hw : |(2633114017/5000000000 : ℝ)|=(2633114017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215700999/400000000 : ℝ)|^8343 ≤ (8821939512869/20000000000000 : ℝ)^6295
        have hw : |(215700999/400000000 : ℝ)|=(215700999/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s8_5 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312537501/10000000000 : ℝ)*x 0 + (-65651117/312500000 : ℝ)*x 1 + (674065721/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312537501/10000000000 : ℝ)^8343 ≤ (43244654521889/100000000000000 : ℝ)^6295 := by
    have hnat : (5312537501 : ℕ)^8343*100000000000000^6295 ≤ 43244654521889^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312537501 10000000000 43244654521889 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65651117/312500000 : ℝ)^8343 ≤ (6322819651039/50000000000000 : ℝ)^6295 := by
    have hnat : (65651117 : ℕ)^8343*50000000000000^6295 ≤ 6322819651039^6295*312500000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65651117 312500000 6322819651039 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674065721/1250000000 : ℝ)^8343 ≤ (1102742654031/2500000000000 : ℝ)^6295 := by
    have hnat : (674065721 : ℕ)^8343*2500000000000^6295 ≤ 1102742654031^6295*1250000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674065721 1250000000 1102742654031 2500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312537501/10000000000 : ℝ), (-65651117/312500000 : ℝ), (674065721/1250000000 : ℝ)] ![(43244654521889/100000000000000 : ℝ), (6322819651039/50000000000000 : ℝ), (1102742654031/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312537501/10000000000 : ℝ)|^8343 ≤ (43244654521889/100000000000000 : ℝ)^6295
        have hw : |(5312537501/10000000000 : ℝ)|=(5312537501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-65651117/312500000 : ℝ)|^8343 ≤ (6322819651039/50000000000000 : ℝ)^6295
        have hw : |(-65651117/312500000 : ℝ)|=(65651117/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674065721/1250000000 : ℝ)|^8343 ≤ (1102742654031/2500000000000 : ℝ)^6295
        have hw : |(674065721/1250000000 : ℝ)|=(674065721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s8_6 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664067261/1250000000 : ℝ)*x 0 + (5392525117/10000000000 : ℝ)*x 1 + (-420167167/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664067261/1250000000 : ℝ)^8343 ≤ (21622330427339/50000000000000 : ℝ)^6295 := by
    have hnat : (664067261 : ℕ)^8343*50000000000000^6295 ≤ 21622330427339^6295*1250000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664067261 1250000000 21622330427339 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392525117/10000000000 : ℝ)^8343 ≤ (11027424775941/25000000000000 : ℝ)^6295 := by
    have hnat : (5392525117 : ℕ)^8343*25000000000000^6295 ≤ 11027424775941^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392525117 10000000000 11027424775941 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420167167/2000000000 : ℝ)^8343 ≤ (3161410007011/25000000000000 : ℝ)^6295 := by
    have hnat : (420167167 : ℕ)^8343*25000000000000^6295 ≤ 3161410007011^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420167167 2000000000 3161410007011 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664067261/1250000000 : ℝ), (5392525117/10000000000 : ℝ), (-420167167/2000000000 : ℝ)] ![(21622330427339/50000000000000 : ℝ), (11027424775941/25000000000000 : ℝ), (3161410007011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664067261/1250000000 : ℝ)|^8343 ≤ (21622330427339/50000000000000 : ℝ)^6295
        have hw : |(664067261/1250000000 : ℝ)|=(664067261/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392525117/10000000000 : ℝ)|^8343 ≤ (11027424775941/25000000000000 : ℝ)^6295
        have hw : |(5392525117/10000000000 : ℝ)|=(5392525117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-420167167/2000000000 : ℝ)|^8343 ≤ (3161410007011/25000000000000 : ℝ)^6295
        have hw : |(-420167167/2000000000 : ℝ)|=(420167167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s8_7 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2181779473/5000000000 : ℝ)*x 0 + (1122800291/2500000000 : ℝ)*x 1 + (2119770397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181779473/5000000000 : ℝ)^8343 ≤ (8329281737653/25000000000000 : ℝ)^6295 := by
    have hnat : (2181779473 : ℕ)^8343*25000000000000^6295 ≤ 8329281737653^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181779473 5000000000 8329281737653 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122800291/2500000000 : ℝ)^8343 ≤ (34614891215141/100000000000000 : ℝ)^6295 := by
    have hnat : (1122800291 : ℕ)^8343*100000000000000^6295 ≤ 34614891215141^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122800291 2500000000 34614891215141 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119770397/5000000000 : ℝ)^8343 ≤ (125265553991/390625000000 : ℝ)^6295 := by
    have hnat : (2119770397 : ℕ)^8343*390625000000^6295 ≤ 125265553991^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119770397 5000000000 125265553991 390625000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181779473/5000000000 : ℝ), (1122800291/2500000000 : ℝ), (2119770397/5000000000 : ℝ)] ![(8329281737653/25000000000000 : ℝ), (34614891215141/100000000000000 : ℝ), (125265553991/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181779473/5000000000 : ℝ)|^8343 ≤ (8329281737653/25000000000000 : ℝ)^6295
        have hw : |(2181779473/5000000000 : ℝ)|=(2181779473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122800291/2500000000 : ℝ)|^8343 ≤ (34614891215141/100000000000000 : ℝ)^6295
        have hw : |(1122800291/2500000000 : ℝ)|=(1122800291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2119770397/5000000000 : ℝ)|^8343 ≤ (125265553991/390625000000 : ℝ)^6295
        have hw : |(2119770397/5000000000 : ℝ)|=(2119770397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1150_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2841/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14053/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7027/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11363/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7027/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11363/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7027/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11363/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7027/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11363/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7027/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11363/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7027/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11363/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11363/100000 : ℝ) ^ (4171/1024 : ℝ) ≤ (14216551689321517/100000000000000000000 : ℝ) := by
    have hpowers : (11363/100000 : ℝ)^4171 ≤ (14216551689321517/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11363 : ℕ)^4171*100000000000000000000^1024 ≤ 14216551689321517^1024*100000^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11363 100000 14216551689321517 100000000000000000000 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11363/100000 : ℝ)) (X := (14216551689321517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7027/50000 : ℝ) ^ (4171/1024 : ℝ) ≤ (8447395142206609/25000000000000000000 : ℝ) := by
    have hpowers : (7027/50000 : ℝ)^4171 ≤ (8447395142206609/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7027 : ℕ)^4171*25000000000000000000^1024 ≤ 8447395142206609^1024*50000^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7027 50000 8447395142206609 25000000000000000000 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7027/50000 : ℝ)) (X := (8447395142206609/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014216551689321517/50000000000000000000 : ℝ) ≤ (2500174492779651/2500000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (50014216551689321517/50000000000000000000 : ℝ)^1024 ≤ (2500174492779651/2500000000000000 : ℝ)^4171 := by
      have hnat : (50014216551689321517 : ℕ)^1024*2500000000000000^4171 ≤ 2500174492779651^4171*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014216551689321517 50000000000000000000 2500174492779651 2500000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500174492779651/2500000000000000 : ℝ)) (X := (50014216551689321517/50000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048006132258147953/100000000000000000000 : ℝ) ≤ (625073647475527/625000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (100048006132258147953/100000000000000000000 : ℝ)^1024 ≤ (625073647475527/625000000000000 : ℝ)^4171 := by
      have hnat : (100048006132258147953 : ℕ)^1024*625000000000000^4171 ≤ 625073647475527^4171*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048006132258147953 100000000000000000000 625073647475527 625000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625073647475527/625000000000000 : ℝ)) (X := (100048006132258147953/100000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508447395142206609/12500000000000000000 : ℝ) ≤ (500082937404913/500000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (12508447395142206609/12500000000000000000 : ℝ)^1024 ≤ (500082937404913/500000000000000 : ℝ)^4171 := by
      have hnat : (12508447395142206609 : ℕ)^1024*500000000000000^4171 ≤ 500082937404913^4171*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508447395142206609 12500000000000000000 500082937404913 500000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500082937404913/500000000000000 : ℝ)) (X := (12508447395142206609/12500000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14216551689321517/100000000000000000000 : ℝ) ≤ ((517326171758852543/517500000000000000 : ℝ)+2*(9238240189/5175000000000 : ℝ)*(11363/100000 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (517326171758852543/517500000000000000 : ℝ)+2*(9238240189/5175000000000 : ℝ)*(11363/100000 : ℝ)=(2500174492779651/2500000000000000 : ℝ) by norm_num, show 1+2*(14216551689321517/100000000000000000000 : ℝ)=(50014216551689321517/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8447395142206609/25000000000000000000 : ℝ)+(14216551689321517/100000000000000000000 : ℝ) ≤ ((517326171758852543/517500000000000000 : ℝ)+(9238240189/5175000000000 : ℝ)*((7027/50000 : ℝ)+(11363/100000 : ℝ)))^(4171/1024 : ℝ) := by
    rw [show (517326171758852543/517500000000000000 : ℝ)+(9238240189/5175000000000 : ℝ)*((7027/50000 : ℝ)+(11363/100000 : ℝ))=(625073647475527/625000000000000 : ℝ) by norm_num, show 1+(8447395142206609/25000000000000000000 : ℝ)+(14216551689321517/100000000000000000000 : ℝ)=(100048006132258147953/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8447395142206609/25000000000000000000 : ℝ) ≤ ((517326171758852543/517500000000000000 : ℝ)+2*(9238240189/5175000000000 : ℝ)*(7027/50000 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (517326171758852543/517500000000000000 : ℝ)+2*(9238240189/5175000000000 : ℝ)*(7027/50000 : ℝ)=(500082937404913/500000000000000 : ℝ) by norm_num, show 1+2*(8447395142206609/25000000000000000000 : ℝ)=(12508447395142206609/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (517326171758852543/517500000000000000 : ℝ)*(X 1 0+X 2 0)+(9238240189/5175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (11363/100000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (517326171758852543/517500000000000000 : ℝ)) (alpha := (9238240189/5175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (517326171758852543/517500000000000000 : ℝ)*(X 0 1+X 2 1)+(9238240189/5175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (11363/100000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (517326171758852543/517500000000000000 : ℝ)) (alpha := (9238240189/5175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (517326171758852543/517500000000000000 : ℝ)*(X 0 2+X 1 2)+(9238240189/5175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (11363/100000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (517326171758852543/517500000000000000 : ℝ)) (alpha := (9238240189/5175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2163070501/10000000000 : ℝ)*X 0 0+(215713811/400000000 : ℝ)*X 0 1+(5265908927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672358443/5000000000 : ℝ)*X 1 0+(-111372611/500000000 : ℝ)*X 1 1+(42127271/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344716839/10000000000 : ℝ)*X 2 0+(5265908881/10000000000 : ℝ)*X 2 1+(-556863069/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2181774763/5000000000 : ℝ)*X 0 0+(529862907/1250000000 : ℝ)*X 0 1+(2245918077/5000000000 : ℝ)*X 0 2+(2181774763/5000000000 : ℝ)*X 1 0+(529862907/1250000000 : ℝ)*X 1 1+(2245918077/5000000000 : ℝ)*X 1 2+(2181774763/5000000000 : ℝ)*X 2 0+(529862907/1250000000 : ℝ)*X 2 1+(2245918077/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-432615083/2000000000 : ℝ)*X 0 0+(2633114017/5000000000 : ℝ)*X 0 1+(215700999/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312537501/10000000000 : ℝ)*X 1 0+(-65651117/312500000 : ℝ)*X 1 1+(674065721/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664067261/1250000000 : ℝ)*X 2 0+(5392525117/10000000000 : ℝ)*X 2 1+(-420167167/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2181779473/5000000000 : ℝ)*X 0 0+(1122800291/2500000000 : ℝ)*X 0 1+(2119770397/5000000000 : ℝ)*X 0 2+(2181779473/5000000000 : ℝ)*X 1 0+(1122800291/2500000000 : ℝ)*X 1 1+(2119770397/5000000000 : ℝ)*X 1 2+(2181779473/5000000000 : ℝ)*X 2 0+(1122800291/2500000000 : ℝ)*X 2 1+(2119770397/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7538574426104720376639527/862500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (181142921/10000000000000 : ℝ)*(base19) + (776397057/50000000000000 : ℝ)*(base23) + (50603143/50000000000000 : ℝ)*(lower2) + (37758517/12500000000000 : ℝ)*(upper3) + (751567/1250000000000 : ℝ)*(upper5) + (591585927349163/10000000000000 : ℝ)*(major0) + (591585927349163/10000000000000 : ℝ)*(major1) + (591585927349163/10000000000000 : ℝ)*(major2) + (3939007188301887/50000000000000 : ℝ)*(sp0) + (1969513300216613/25000000000000 : ℝ)*(sp1) + (1969513364875387/25000000000000 : ℝ)*(sp2) + (790727534048403/20000000000000 : ℝ)*(sp3) + (2539730743/6250000000000 : ℝ)*(sp4) + (12786549849/50000000000000 : ℝ)*(sp7) + (247103952708857/6250000000000 : ℝ)*(f.failure) + (7878055012295663/100000000000000 : ℝ)*(f.sum) + (7638493927/3234375000000000000000000 : ℝ)*base65 + (14497605326086499/575000000000000000000000000000 : ℝ)*base68 + (5836195444036499/575000000000000000000000000000 : ℝ)*base70 + (7156026207786499/575000000000000000000000000000 : ℝ)*base72 + (134048982631/25875000000000000000000000 : ℝ)*base74 + (12381517160186499/575000000000000000000000000000 : ℝ)*base76 + (2732469730286499/575000000000000000000000000000 : ℝ)*base78 + (3406655580036499/575000000000000000000000000000 : ℝ)*base80 + (192838965631/103500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1616727/312500000000000000000 : ℝ)*base89 + (1616727/312500000000000000000 : ℝ)*base91 + (1616727/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (404792615828138818643533/62500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (145593237/50000000000000 : ℝ)*(base19) + (1355961953/100000000000000 : ℝ)*(base23) + (17147489/3125000000000 : ℝ)*(lower1) + (62600467/100000000000000 : ℝ)*(upper2) + (53331361/25000000000000 : ℝ)*(upper3) + (2972853078132413/50000000000000 : ℝ)*(major0) + (2972853078132413/50000000000000 : ℝ)*(major1) + (2972853078132413/50000000000000 : ℝ)*(major2) + (5949675001/50000000000000 : ℝ)*(sp2) + (3572818139/50000000000000 : ℝ)*(sp3) + (1979450426203213/25000000000000 : ℝ)*(sp4) + (3958900706813189/50000000000000 : ℝ)*(sp5) + (3958894224750449/50000000000000 : ℝ)*(sp6) + (3973603246191113/100000000000000 : ℝ)*(sp7) + (397361039182739/10000000000000 : ℝ)*(f.failure) + (1979450426203213/25000000000000 : ℝ)*(f.sum) + (135176488949/22500000000000000000000000 : ℝ)*base66 + (914564520570163/125000000000000000000000000000 : ℝ)*base68 + (760147966320163/125000000000000000000000000000 : ℝ)*base70 + (671799875070163/125000000000000000000000000000 : ℝ)*base72 + (52506538597/11250000000000000000000000 : ℝ)*base74 + (1707464166820163/125000000000000000000000000000 : ℝ)*base76 + (5488235540570163/125000000000000000000000000000 : ℝ)*base78 + (4453605753070163/125000000000000000000000000000 : ℝ)*base80 + (11903907823/2812500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1021229/500000000000000000000 : ℝ)*base89 + (1021229/500000000000000000000 : ℝ)*base91 + (1021229/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1150_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1150_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1150_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11327/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1150_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1150_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1150_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11327/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1150_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

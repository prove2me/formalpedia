-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1262_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:54:57.504008+00:00
-- url     : https://prove2.me/submissions/a7a71c39-9187-4f6c-b449-52af0e066be5

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
theorem support_rectangle_w1262_s0_0 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1854404579/10000000000 : ℝ)*x 0 + (3013504473/5000000000 : ℝ)*x 1 + (2397729459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1854404579/10000000000 : ℝ)^8455 ≤ (2164291592577/20000000000000 : ℝ)^6407 := by
    have hnat : (1854404579 : ℕ)^8455*20000000000000^6407 ≤ 2164291592577^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1854404579 10000000000 2164291592577 20000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3013504473/5000000000 : ℝ)^8455 ≤ (51263859987729/100000000000000 : ℝ)^6407 := by
    have hnat : (3013504473 : ℕ)^8455*100000000000000^6407 ≤ 51263859987729^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3013504473 5000000000 51263859987729 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2397729459/5000000000 : ℝ)^8455 ≤ (37914682029067/100000000000000 : ℝ)^6407 := by
    have hnat : (2397729459 : ℕ)^8455*100000000000000^6407 ≤ 37914682029067^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397729459 5000000000 37914682029067 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1854404579/10000000000 : ℝ), (3013504473/5000000000 : ℝ), (2397729459/5000000000 : ℝ)] ![(2164291592577/20000000000000 : ℝ), (51263859987729/100000000000000 : ℝ), (37914682029067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1854404579/10000000000 : ℝ)|^8455 ≤ (2164291592577/20000000000000 : ℝ)^6407
        have hw : |(-1854404579/10000000000 : ℝ)|=(1854404579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3013504473/5000000000 : ℝ)|^8455 ≤ (51263859987729/100000000000000 : ℝ)^6407
        have hw : |(3013504473/5000000000 : ℝ)|=(3013504473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2397729459/5000000000 : ℝ)|^8455 ≤ (37914682029067/100000000000000 : ℝ)^6407
        have hw : |(2397729459/5000000000 : ℝ)|=(2397729459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s0_1 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5510032719/10000000000 : ℝ)*x 0 + (-511583609/2000000000 : ℝ)*x 1 + (4795458889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5510032719/10000000000 : ℝ)^8455 ≤ (11385550143741/25000000000000 : ℝ)^6407 := by
    have hnat : (5510032719 : ℕ)^8455*25000000000000^6407 ≤ 11385550143741^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510032719 10000000000 11385550143741 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (511583609/2000000000 : ℝ)^8455 ≤ (4135779420427/25000000000000 : ℝ)^6407 := by
    have hnat : (511583609 : ℕ)^8455*25000000000000^6407 ≤ 4135779420427^6407*2000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511583609 2000000000 4135779420427 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4795458889/10000000000 : ℝ)^8455 ≤ (37914681726491/100000000000000 : ℝ)^6407 := by
    have hnat : (4795458889 : ℕ)^8455*100000000000000^6407 ≤ 37914681726491^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4795458889 10000000000 37914681726491 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5510032719/10000000000 : ℝ), (-511583609/2000000000 : ℝ), (4795458889/10000000000 : ℝ)] ![(11385550143741/25000000000000 : ℝ), (4135779420427/25000000000000 : ℝ), (37914681726491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5510032719/10000000000 : ℝ)|^8455 ≤ (11385550143741/25000000000000 : ℝ)^6407
        have hw : |(5510032719/10000000000 : ℝ)|=(5510032719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-511583609/2000000000 : ℝ)|^8455 ≤ (4135779420427/25000000000000 : ℝ)^6407
        have hw : |(-511583609/2000000000 : ℝ)|=(511583609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4795458889/10000000000 : ℝ)|^8455 ≤ (37914681726491/100000000000000 : ℝ)^6407
        have hw : |(4795458889/10000000000 : ℝ)|=(4795458889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s0_2 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (22040131/40000000 : ℝ)*x 0 + (4795458889/10000000000 : ℝ)*x 1 + (-1278959003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22040131/40000000 : ℝ)^8455 ≤ (11385550228273/25000000000000 : ℝ)^6407 := by
    have hnat : (22040131 : ℕ)^8455*25000000000000^6407 ≤ 11385550228273^6407*40000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22040131 40000000 11385550228273 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4795458889/10000000000 : ℝ)^8455 ≤ (37914681726491/100000000000000 : ℝ)^6407 := by
    have hnat : (4795458889 : ℕ)^8455*100000000000000^6407 ≤ 37914681726491^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4795458889 10000000000 37914681726491 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1278959003/5000000000 : ℝ)^8455 ≤ (8271558674427/50000000000000 : ℝ)^6407 := by
    have hnat : (1278959003 : ℕ)^8455*50000000000000^6407 ≤ 8271558674427^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1278959003 5000000000 8271558674427 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(22040131/40000000 : ℝ), (4795458889/10000000000 : ℝ), (-1278959003/5000000000 : ℝ)] ![(11385550228273/25000000000000 : ℝ), (37914681726491/100000000000000 : ℝ), (8271558674427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(22040131/40000000 : ℝ)|^8455 ≤ (11385550228273/25000000000000 : ℝ)^6407
        have hw : |(22040131/40000000 : ℝ)|=(22040131/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4795458889/10000000000 : ℝ)|^8455 ≤ (37914681726491/100000000000000 : ℝ)^6407
        have hw : |(4795458889/10000000000 : ℝ)|=(4795458889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1278959003/5000000000 : ℝ)|^8455 ≤ (8271558674427/50000000000000 : ℝ)^6407
        have hw : |(-1278959003/5000000000 : ℝ)|=(1278959003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s0_3 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (16765821/40000000 : ℝ)*x 0 + (155807881/500000000 : ℝ)*x 1 + (1124818987/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16765821/40000000 : ℝ)^8455 ≤ (31743412190949/100000000000000 : ℝ)^6407 := by
    have hnat : (16765821 : ℕ)^8455*100000000000000^6407 ≤ 31743412190949^6407*40000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16765821 40000000 31743412190949 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (155807881/500000000 : ℝ)^8455 ≤ (21466175208689/100000000000000 : ℝ)^6407 := by
    have hnat : (155807881 : ℕ)^8455*100000000000000^6407 ≤ 21466175208689^6407*500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155807881 500000000 21466175208689 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124818987/2000000000 : ℝ)^8455 ≤ (23395206294627/50000000000000 : ℝ)^6407 := by
    have hnat : (1124818987 : ℕ)^8455*50000000000000^6407 ≤ 23395206294627^6407*2000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124818987 2000000000 23395206294627 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16765821/40000000 : ℝ), (155807881/500000000 : ℝ), (1124818987/2000000000 : ℝ)] ![(31743412190949/100000000000000 : ℝ), (21466175208689/100000000000000 : ℝ), (23395206294627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16765821/40000000 : ℝ)|^8455 ≤ (31743412190949/100000000000000 : ℝ)^6407
        have hw : |(16765821/40000000 : ℝ)|=(16765821/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(155807881/500000000 : ℝ)|^8455 ≤ (21466175208689/100000000000000 : ℝ)^6407
        have hw : |(155807881/500000000 : ℝ)|=(155807881/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124818987/2000000000 : ℝ)|^8455 ≤ (23395206294627/50000000000000 : ℝ)^6407
        have hw : |(1124818987/2000000000 : ℝ)|=(1124818987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s0_4 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1859205441/10000000000 : ℝ)*x 0 + (1206790163/2500000000 : ℝ)*x 1 + (5994186129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1859205441/10000000000 : ℝ)^8455 ≤ (10858444098011/100000000000000 : ℝ)^6407 := by
    have hnat : (1859205441 : ℕ)^8455*100000000000000^6407 ≤ 10858444098011^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1859205441 10000000000 10858444098011 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1206790163/2500000000 : ℝ)^8455 ≤ (4780724459783/12500000000000 : ℝ)^6407 := by
    have hnat : (1206790163 : ℕ)^8455*12500000000000^6407 ≤ 4780724459783^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206790163 2500000000 4780724459783 12500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5994186129/10000000000 : ℝ)^8455 ≤ (50895760202563/100000000000000 : ℝ)^6407 := by
    have hnat : (5994186129 : ℕ)^8455*100000000000000^6407 ≤ 50895760202563^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5994186129 10000000000 50895760202563 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1859205441/10000000000 : ℝ), (1206790163/2500000000 : ℝ), (5994186129/10000000000 : ℝ)] ![(10858444098011/100000000000000 : ℝ), (4780724459783/12500000000000 : ℝ), (50895760202563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1859205441/10000000000 : ℝ)|^8455 ≤ (10858444098011/100000000000000 : ℝ)^6407
        have hw : |(-1859205441/10000000000 : ℝ)|=(1859205441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1206790163/2500000000 : ℝ)|^8455 ≤ (4780724459783/12500000000000 : ℝ)^6407
        have hw : |(1206790163/2500000000 : ℝ)|=(1206790163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5994186129/10000000000 : ℝ)|^8455 ≤ (50895760202563/100000000000000 : ℝ)^6407
        have hw : |(5994186129/10000000000 : ℝ)|=(5994186129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s0_5 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5174862519/10000000000 : ℝ)*x 0 + (-1359188391/10000000000 : ℝ)*x 1 + (5994188551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174862519/10000000000 : ℝ)^8455 ≤ (41922431481711/100000000000000 : ℝ)^6407 := by
    have hnat : (5174862519 : ℕ)^8455*100000000000000^6407 ≤ 41922431481711^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174862519 10000000000 41922431481711 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359188391/10000000000 : ℝ)^8455 ≤ (1436356231743/20000000000000 : ℝ)^6407 := by
    have hnat : (1359188391 : ℕ)^8455*20000000000000^6407 ≤ 1436356231743^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359188391 10000000000 1436356231743 20000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5994188551/10000000000 : ℝ)^8455 ≤ (2035831493639/4000000000000 : ℝ)^6407 := by
    have hnat : (5994188551 : ℕ)^8455*4000000000000^6407 ≤ 2035831493639^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5994188551 10000000000 2035831493639 4000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174862519/10000000000 : ℝ), (-1359188391/10000000000 : ℝ), (5994188551/10000000000 : ℝ)] ![(41922431481711/100000000000000 : ℝ), (1436356231743/20000000000000 : ℝ), (2035831493639/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174862519/10000000000 : ℝ)|^8455 ≤ (41922431481711/100000000000000 : ℝ)^6407
        have hw : |(5174862519/10000000000 : ℝ)|=(5174862519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1359188391/10000000000 : ℝ)|^8455 ≤ (1436356231743/20000000000000 : ℝ)^6407
        have hw : |(-1359188391/10000000000 : ℝ)|=(1359188391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5994188551/10000000000 : ℝ)|^8455 ≤ (2035831493639/4000000000000 : ℝ)^6407
        have hw : |(5994188551/10000000000 : ℝ)|=(5994188551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s0_6 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5174863581/10000000000 : ℝ)*x 0 + (2997093273/5000000000 : ℝ)*x 1 + (-271837997/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174863581/10000000000 : ℝ)^8455 ≤ (8384488567049/20000000000000 : ℝ)^6407 := by
    have hnat : (5174863581 : ℕ)^8455*20000000000000^6407 ≤ 8384488567049^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174863581 10000000000 8384488567049 20000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2997093273/5000000000 : ℝ)^8455 ≤ (5089576487503/10000000000000 : ℝ)^6407 := by
    have hnat : (2997093273 : ℕ)^8455*10000000000000^6407 ≤ 5089576487503^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2997093273 5000000000 5089576487503 10000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271837997/2000000000 : ℝ)^8455 ≤ (7181792273467/100000000000000 : ℝ)^6407 := by
    have hnat : (271837997 : ℕ)^8455*100000000000000^6407 ≤ 7181792273467^6407*2000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271837997 2000000000 7181792273467 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174863581/10000000000 : ℝ), (2997093273/5000000000 : ℝ), (-271837997/2000000000 : ℝ)] ![(8384488567049/20000000000000 : ℝ), (5089576487503/10000000000000 : ℝ), (7181792273467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174863581/10000000000 : ℝ)|^8455 ≤ (8384488567049/20000000000000 : ℝ)^6407
        have hw : |(5174863581/10000000000 : ℝ)|=(5174863581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2997093273/5000000000 : ℝ)|^8455 ≤ (5089576487503/10000000000000 : ℝ)^6407
        have hw : |(2997093273/5000000000 : ℝ)|=(2997093273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-271837997/2000000000 : ℝ)|^8455 ≤ (7181792273467/100000000000000 : ℝ)^6407
        have hw : |(-271837997/2000000000 : ℝ)|=(271837997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s0_7 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2100617129/5000000000 : ℝ)*x 0 + (2779771593/5000000000 : ℝ)*x 1 + (3182992167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100617129/5000000000 : ℝ)^8455 ≤ (31841181892691/100000000000000 : ℝ)^6407 := by
    have hnat : (2100617129 : ℕ)^8455*100000000000000^6407 ≤ 31841181892691^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100617129 5000000000 31841181892691 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2779771593/5000000000 : ℝ)^8455 ≤ (46083001876383/100000000000000 : ℝ)^6407 := by
    have hnat : (2779771593 : ℕ)^8455*100000000000000^6407 ≤ 46083001876383^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2779771593 5000000000 46083001876383 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3182992167/10000000000 : ℝ)^8455 ≤ (11037908103317/50000000000000 : ℝ)^6407 := by
    have hnat : (3182992167 : ℕ)^8455*50000000000000^6407 ≤ 11037908103317^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3182992167 10000000000 11037908103317 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2100617129/5000000000 : ℝ), (2779771593/5000000000 : ℝ), (3182992167/10000000000 : ℝ)] ![(31841181892691/100000000000000 : ℝ), (46083001876383/100000000000000 : ℝ), (11037908103317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2100617129/5000000000 : ℝ)|^8455 ≤ (31841181892691/100000000000000 : ℝ)^6407
        have hw : |(2100617129/5000000000 : ℝ)|=(2100617129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2779771593/5000000000 : ℝ)|^8455 ≤ (46083001876383/100000000000000 : ℝ)^6407
        have hw : |(2779771593/5000000000 : ℝ)|=(2779771593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3182992167/10000000000 : ℝ)|^8455 ≤ (11037908103317/50000000000000 : ℝ)^6407
        have hw : |(3182992167/10000000000 : ℝ)|=(3182992167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1262_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (897/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27361/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4227/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4227 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4227*1^1024 ≤ 0^1024*1^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4227/1024 : ℝ) ≤ (569208835845681307/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4227 ≤ (569208835845681307/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4227*25000000000000000000^1024 ≤ 569208835845681307^1024*5^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 569208835845681307 25000000000000000000 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (569208835845681307/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4227 := by
      have hnat : (1 : ℕ)^1024*1^4227 ≤ 1^4227*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25569208835845681307/25000000000000000000 : ℝ) ≤ (10054687282495441/10000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (25569208835845681307/25000000000000000000 : ℝ)^1024 ≤ (10054687282495441/10000000000000000 : ℝ)^4227 := by
      have hnat : (25569208835845681307 : ℕ)^1024*10000000000000000^4227 ≤ 10054687282495441^4227*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25569208835845681307 25000000000000000000 10054687282495441 10000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10054687282495441/10000000000000000 : ℝ)) (X := (25569208835845681307/25000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (13069208835845681307/12500000000000000000 : ℝ) ≤ (5054687282495441/5000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (13069208835845681307/12500000000000000000 : ℝ)^1024 ≤ (5054687282495441/5000000000000000 : ℝ)^4227 := by
      have hnat : (13069208835845681307 : ℕ)^1024*5000000000000000^4227 ≤ 5054687282495441^4227*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13069208835845681307 12500000000000000000 5054687282495441 5000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5054687282495441/5000000000000000 : ℝ)) (X := (13069208835845681307/12500000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(54687282495441/4000000000000000 : ℝ)*(0 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(54687282495441/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(569208835845681307/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(54687282495441/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4227/1024 : ℝ) := by
    rw [show (1 : ℝ)+(54687282495441/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10054687282495441/10000000000000000 : ℝ) by norm_num, show 1+(569208835845681307/25000000000000000000 : ℝ)+(0 : ℝ)=(25569208835845681307/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(569208835845681307/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(54687282495441/4000000000000000 : ℝ)*(2/5 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(54687282495441/4000000000000000 : ℝ)*(2/5 : ℝ)=(5054687282495441/5000000000000000 : ℝ) by norm_num, show 1+2*(569208835845681307/25000000000000000000 : ℝ)=(13069208835845681307/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(54687282495441/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54687282495441/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(54687282495441/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54687282495441/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(54687282495441/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54687282495441/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1854404579/10000000000 : ℝ)*X 0 0+(3013504473/5000000000 : ℝ)*X 0 1+(2397729459/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5510032719/10000000000 : ℝ)*X 1 0+(-511583609/2000000000 : ℝ)*X 1 1+(4795458889/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((22040131/40000000 : ℝ)*X 2 0+(4795458889/10000000000 : ℝ)*X 2 1+(-1278959003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((16765821/40000000 : ℝ)*X 0 0+(155807881/500000000 : ℝ)*X 0 1+(1124818987/2000000000 : ℝ)*X 0 2+(16765821/40000000 : ℝ)*X 1 0+(155807881/500000000 : ℝ)*X 1 1+(1124818987/2000000000 : ℝ)*X 1 2+(16765821/40000000 : ℝ)*X 2 0+(155807881/500000000 : ℝ)*X 2 1+(1124818987/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1859205441/10000000000 : ℝ)*X 0 0+(1206790163/2500000000 : ℝ)*X 0 1+(5994186129/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5174862519/10000000000 : ℝ)*X 1 0+(-1359188391/10000000000 : ℝ)*X 1 1+(5994188551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5174863581/10000000000 : ℝ)*X 2 0+(2997093273/5000000000 : ℝ)*X 2 1+(-271837997/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2100617129/5000000000 : ℝ)*X 0 0+(2779771593/5000000000 : ℝ)*X 0 1+(3182992167/10000000000 : ℝ)*X 0 2+(2100617129/5000000000 : ℝ)*X 1 0+(2779771593/5000000000 : ℝ)*X 1 1+(3182992167/10000000000 : ℝ)*X 1 2+(2100617129/5000000000 : ℝ)*X 2 0+(2779771593/5000000000 : ℝ)*X 2 1+(3182992167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (702389915420133455255007/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9862609/12500000000000 : ℝ)*(base1) + (854358291/50000000000000 : ℝ)*(base19) + (85664247/5000000000000 : ℝ)*(base23) + (193736881/100000000000000 : ℝ)*(upper3) + (204925121/100000000000000 : ℝ)*(upper5) + (605367454524709/100000000000000 : ℝ)*(major0) + (605367454524709/100000000000000 : ℝ)*(major1) + (605367454524709/100000000000000 : ℝ)*(major2) + (101498748491563/12500000000000 : ℝ)*(sp0) + (405996833808299/50000000000000 : ℝ)*(sp1) + (10149920788103/1250000000000 : ℝ)*(sp2) + (398736578779543/100000000000000 : ℝ)*(sp3) + (1366825387/25000000000000 : ℝ)*(sp4) + (2640905847/100000000000000 : ℝ)*(sp7) + (199369649293131/50000000000000 : ℝ)*(f.failure) + (40599768816659/5000000000000 : ℝ)*(f.sum) + (181711644048331/200000000000000000000000000000 : ℝ)*base66 + (973109601551669/400000000000000000000000000000 : ℝ)*base67 + (4335557292848331/400000000000000000000000000000 : ℝ)*base70 + (235557219151669/400000000000000000000000000000 : ℝ)*base71 + (472035055951669/200000000000000000000000000000 : ℝ)*base73 + (2556493796048331/400000000000000000000000000000 : ℝ)*base76 + (365398796048331/400000000000000000000000000000 : ℝ)*base78 + (853824510448331/400000000000000000000000000000 : ℝ)*base80 + (1428073028448331/200000000000000000000000000000 : ℝ)*base82 + (10279921/1250000000000000000000 : ℝ)*base89 + (10279921/1250000000000000000000 : ℝ)*base91 + (10279921/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (149821452599737624325301/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (195016707/100000000000000 : ℝ)*(base1) + (249661229/100000000000000 : ℝ)*(base19) + (365390309/100000000000000 : ℝ)*(base23) + (3959507/10000000000000 : ℝ)*(upper3) + (638829358039171/100000000000000 : ℝ)*(major0) + (638829358039171/100000000000000 : ℝ)*(major1) + (638829358039171/100000000000000 : ℝ)*(major2) + (630058401/50000000000000 : ℝ)*(sp1) + (331864237/100000000000000 : ℝ)*(sp2) + (777080039/100000000000000 : ℝ)*(sp3) + (856879104600181/100000000000000 : ℝ)*(sp4) + (428438699902721/50000000000000 : ℝ)*(sp5) + (26777444135279/3125000000000 : ℝ)*(sp6) + (13149337014301/3125000000000 : ℝ)*(sp7) + (210389878277189/50000000000000 : ℝ)*(f.failure) + (428439454791737/50000000000000 : ℝ)*(f.sum) + (167514109919411/200000000000000000000000000000 : ℝ)*base65 + (772971209319411/400000000000000000000000000000 : ℝ)*base67 + (1179515363719411/400000000000000000000000000000 : ℝ)*base69 + (1717745570119411/400000000000000000000000000000 : ℝ)*base71 + (66994142919411/200000000000000000000000000000 : ℝ)*base73 + (3438732095319411/400000000000000000000000000000 : ℝ)*base75 + (1460121617319411/400000000000000000000000000000 : ℝ)*base77 + (416260261719411/400000000000000000000000000000 : ℝ)*base79 + (248352805519411/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5780801/1250000000000000000000 : ℝ)*base90 + (5780801/1250000000000000000000 : ℝ)*base92 + (5780801/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1262_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (897/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27361/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1262_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1262_s1_0 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2050364737/10000000000 : ℝ)*x 0 + (2835305569/5000000000 : ℝ)*x 1 + (2513209429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2050364737/10000000000 : ℝ)^8455 ≤ (3088856185533/25000000000000 : ℝ)^6407 := by
    have hnat : (2050364737 : ℕ)^8455*25000000000000^6407 ≤ 3088856185533^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050364737 10000000000 3088856185533 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2835305569/5000000000 : ℝ)^8455 ≤ (5912723525943/12500000000000 : ℝ)^6407 := by
    have hnat : (2835305569 : ℕ)^8455*12500000000000^6407 ≤ 5912723525943^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2835305569 5000000000 5912723525943 12500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2513209429/5000000000 : ℝ)^8455 ≤ (32274229629/80000000000 : ℝ)^6407 := by
    have hnat : (2513209429 : ℕ)^8455*80000000000^6407 ≤ 32274229629^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2513209429 5000000000 32274229629 80000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2050364737/10000000000 : ℝ), (2835305569/5000000000 : ℝ), (2513209429/5000000000 : ℝ)] ![(3088856185533/25000000000000 : ℝ), (5912723525943/12500000000000 : ℝ), (32274229629/80000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2050364737/10000000000 : ℝ)|^8455 ≤ (3088856185533/25000000000000 : ℝ)^6407
        have hw : |(-2050364737/10000000000 : ℝ)|=(2050364737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2835305569/5000000000 : ℝ)|^8455 ≤ (5912723525943/12500000000000 : ℝ)^6407
        have hw : |(2835305569/5000000000 : ℝ)|=(2835305569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2513209429/5000000000 : ℝ)|^8455 ≤ (32274229629/80000000000 : ℝ)^6407
        have hw : |(2513209429/5000000000 : ℝ)|=(2513209429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s1_1 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2706285643/5000000000 : ℝ)*x 0 + (-1197979823/5000000000 : ℝ)*x 1 + (5026418699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706285643/5000000000 : ℝ)^8455 ≤ (44482173263573/100000000000000 : ℝ)^6407 := by
    have hnat : (2706285643 : ℕ)^8455*100000000000000^6407 ≤ 44482173263573^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706285643 5000000000 44482173263573 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1197979823/5000000000 : ℝ)^8455 ≤ (3035008274509/20000000000000 : ℝ)^6407 := by
    have hnat : (1197979823 : ℕ)^8455*20000000000000^6407 ≤ 3035008274509^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1197979823 5000000000 3035008274509 20000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5026418699/10000000000 : ℝ)^8455 ≤ (5042848169021/12500000000000 : ℝ)^6407 := by
    have hnat : (5026418699 : ℕ)^8455*12500000000000^6407 ≤ 5042848169021^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5026418699 10000000000 5042848169021 12500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706285643/5000000000 : ℝ), (-1197979823/5000000000 : ℝ), (5026418699/10000000000 : ℝ)] ![(44482173263573/100000000000000 : ℝ), (3035008274509/20000000000000 : ℝ), (5042848169021/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706285643/5000000000 : ℝ)|^8455 ≤ (44482173263573/100000000000000 : ℝ)^6407
        have hw : |(2706285643/5000000000 : ℝ)|=(2706285643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1197979823/5000000000 : ℝ)|^8455 ≤ (3035008274509/20000000000000 : ℝ)^6407
        have hw : |(-1197979823/5000000000 : ℝ)|=(1197979823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5026418699/10000000000 : ℝ)|^8455 ≤ (5042848169021/12500000000000 : ℝ)^6407
        have hw : |(5026418699/10000000000 : ℝ)|=(5026418699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s1_2 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5412571119/10000000000 : ℝ)*x 0 + (1256604713/2500000000 : ℝ)*x 1 + (-2395959669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412571119/10000000000 : ℝ)^8455 ≤ (4448217145241/10000000000000 : ℝ)^6407 := by
    have hnat : (5412571119 : ℕ)^8455*10000000000000^6407 ≤ 4448217145241^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412571119 10000000000 4448217145241 10000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1256604713/2500000000 : ℝ)^8455 ≤ (403427869727/1000000000000 : ℝ)^6407 := by
    have hnat : (1256604713 : ℕ)^8455*1000000000000^6407 ≤ 403427869727^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1256604713 2500000000 403427869727 1000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2395959669/10000000000 : ℝ)^8455 ≤ (7587520782391/50000000000000 : ℝ)^6407 := by
    have hnat : (2395959669 : ℕ)^8455*50000000000000^6407 ≤ 7587520782391^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2395959669 10000000000 7587520782391 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412571119/10000000000 : ℝ), (1256604713/2500000000 : ℝ), (-2395959669/10000000000 : ℝ)] ![(4448217145241/10000000000000 : ℝ), (403427869727/1000000000000 : ℝ), (7587520782391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412571119/10000000000 : ℝ)|^8455 ≤ (4448217145241/10000000000000 : ℝ)^6407
        have hw : |(5412571119/10000000000 : ℝ)|=(5412571119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1256604713/2500000000 : ℝ)|^8455 ≤ (403427869727/1000000000000 : ℝ)^6407
        have hw : |(1256604713/2500000000 : ℝ)|=(1256604713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2395959669/10000000000 : ℝ)|^8455 ≤ (7587520782391/50000000000000 : ℝ)^6407
        have hw : |(-2395959669/10000000000 : ℝ)|=(2395959669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s1_3 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2153558067/5000000000 : ℝ)*x 0 + (739810039/2000000000 : ℝ)*x 1 + (1252722019/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153558067/5000000000 : ℝ)^8455 ≤ (32904415679683/100000000000000 : ℝ)^6407 := by
    have hnat : (2153558067 : ℕ)^8455*100000000000000^6407 ≤ 32904415679683^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153558067 5000000000 32904415679683 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (739810039/2000000000 : ℝ)^8455 ≤ (26917213531351/100000000000000 : ℝ)^6407 := by
    have hnat : (739810039 : ℕ)^8455*100000000000000^6407 ≤ 26917213531351^6407*2000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739810039 2000000000 26917213531351 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1252722019/2500000000 : ℝ)^8455 ≤ (1255574086807/3125000000000 : ℝ)^6407 := by
    have hnat : (1252722019 : ℕ)^8455*3125000000000^6407 ≤ 1255574086807^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252722019 2500000000 1255574086807 3125000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153558067/5000000000 : ℝ), (739810039/2000000000 : ℝ), (1252722019/2500000000 : ℝ)] ![(32904415679683/100000000000000 : ℝ), (26917213531351/100000000000000 : ℝ), (1255574086807/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153558067/5000000000 : ℝ)|^8455 ≤ (32904415679683/100000000000000 : ℝ)^6407
        have hw : |(2153558067/5000000000 : ℝ)|=(2153558067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(739810039/2000000000 : ℝ)|^8455 ≤ (26917213531351/100000000000000 : ℝ)^6407
        have hw : |(739810039/2000000000 : ℝ)|=(739810039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1252722019/2500000000 : ℝ)|^8455 ≤ (1255574086807/3125000000000 : ℝ)^6407
        have hw : |(1252722019/2500000000 : ℝ)|=(1252722019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s1_4 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-256377229/1250000000 : ℝ)*x 0 + (2517407269/5000000000 : ℝ)*x 1 + (5662056883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256377229/1250000000 : ℝ)^8455 ≤ (12360618526437/100000000000000 : ℝ)^6407 := by
    have hnat : (256377229 : ℕ)^8455*100000000000000^6407 ≤ 12360618526437^6407*1250000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256377229 1250000000 12360618526437 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2517407269/5000000000 : ℝ)^8455 ≤ (1010793384499/2500000000000 : ℝ)^6407 := by
    have hnat : (2517407269 : ℕ)^8455*2500000000000^6407 ≤ 1010793384499^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2517407269 5000000000 1010793384499 2500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5662056883/10000000000 : ℝ)^8455 ≤ (47207646078459/100000000000000 : ℝ)^6407 := by
    have hnat : (5662056883 : ℕ)^8455*100000000000000^6407 ≤ 47207646078459^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5662056883 10000000000 47207646078459 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-256377229/1250000000 : ℝ), (2517407269/5000000000 : ℝ), (5662056883/10000000000 : ℝ)] ![(12360618526437/100000000000000 : ℝ), (1010793384499/2500000000000 : ℝ), (47207646078459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-256377229/1250000000 : ℝ)|^8455 ≤ (12360618526437/100000000000000 : ℝ)^6407
        have hw : |(-256377229/1250000000 : ℝ)|=(256377229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2517407269/5000000000 : ℝ)|^8455 ≤ (1010793384499/2500000000000 : ℝ)^6407
        have hw : |(2517407269/5000000000 : ℝ)|=(2517407269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5662056883/10000000000 : ℝ)|^8455 ≤ (47207646078459/100000000000000 : ℝ)^6407
        have hw : |(5662056883/10000000000 : ℝ)|=(5662056883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s1_5 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5246452903/10000000000 : ℝ)*x 0 + (-27505021/156250000 : ℝ)*x 1 + (5662057323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246452903/10000000000 : ℝ)^8455 ≤ (4268947045461/10000000000000 : ℝ)^6407 := by
    have hnat : (5246452903 : ℕ)^8455*10000000000000^6407 ≤ 4268947045461^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246452903 10000000000 4268947045461 10000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27505021/156250000 : ℝ)^8455 ≤ (5051439304249/50000000000000 : ℝ)^6407 := by
    have hnat : (27505021 : ℕ)^8455*50000000000000^6407 ≤ 5051439304249^6407*156250000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27505021 156250000 5051439304249 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5662057323/10000000000 : ℝ)^8455 ≤ (23603825459811/50000000000000 : ℝ)^6407 := by
    have hnat : (5662057323 : ℕ)^8455*50000000000000^6407 ≤ 23603825459811^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5662057323 10000000000 23603825459811 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246452903/10000000000 : ℝ), (-27505021/156250000 : ℝ), (5662057323/10000000000 : ℝ)] ![(4268947045461/10000000000000 : ℝ), (5051439304249/50000000000000 : ℝ), (23603825459811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246452903/10000000000 : ℝ)|^8455 ≤ (4268947045461/10000000000000 : ℝ)^6407
        have hw : |(5246452903/10000000000 : ℝ)|=(5246452903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27505021/156250000 : ℝ)|^8455 ≤ (5051439304249/50000000000000 : ℝ)^6407
        have hw : |(-27505021/156250000 : ℝ)|=(27505021/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5662057323/10000000000 : ℝ)|^8455 ≤ (23603825459811/50000000000000 : ℝ)^6407
        have hw : |(5662057323/10000000000 : ℝ)|=(5662057323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s1_6 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5246452821/10000000000 : ℝ)*x 0 + (70775713/125000000 : ℝ)*x 1 + (-1760321873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246452821/10000000000 : ℝ)^8455 ≤ (21344734787057/50000000000000 : ℝ)^6407 := by
    have hnat : (5246452821 : ℕ)^8455*50000000000000^6407 ≤ 21344734787057^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246452821 10000000000 21344734787057 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70775713/125000000 : ℝ)^8455 ≤ (23603823902937/50000000000000 : ℝ)^6407 := by
    have hnat : (70775713 : ℕ)^8455*50000000000000^6407 ≤ 23603823902937^6407*125000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70775713 125000000 23603823902937 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1760321873/10000000000 : ℝ)^8455 ≤ (5051441307511/50000000000000 : ℝ)^6407 := by
    have hnat : (1760321873 : ℕ)^8455*50000000000000^6407 ≤ 5051441307511^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1760321873 10000000000 5051441307511 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246452821/10000000000 : ℝ), (70775713/125000000 : ℝ), (-1760321873/10000000000 : ℝ)] ![(21344734787057/50000000000000 : ℝ), (23603823902937/50000000000000 : ℝ), (5051441307511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246452821/10000000000 : ℝ)|^8455 ≤ (21344734787057/50000000000000 : ℝ)^6407
        have hw : |(5246452821/10000000000 : ℝ)|=(5246452821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(70775713/125000000 : ℝ)|^8455 ≤ (23603823902937/50000000000000 : ℝ)^6407
        have hw : |(70775713/125000000 : ℝ)|=(70775713/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1760321873/10000000000 : ℝ)|^8455 ≤ (5051441307511/50000000000000 : ℝ)^6407
        have hw : |(-1760321873/10000000000 : ℝ)|=(1760321873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s1_7 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2154222821/5000000000 : ℝ)*x 0 + (624223899/1250000000 : ℝ)*x 1 + (3716469827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154222821/5000000000 : ℝ)^8455 ≤ (32917819816977/100000000000000 : ℝ)^6407 := by
    have hnat : (2154222821 : ℕ)^8455*100000000000000^6407 ≤ 32917819816977^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154222821 5000000000 32917819816977 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (624223899/1250000000 : ℝ)^8455 ≤ (39997563296123/100000000000000 : ℝ)^6407 := by
    have hnat : (624223899 : ℕ)^8455*100000000000000^6407 ≤ 39997563296123^6407*1250000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624223899 1250000000 39997563296123 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3716469827/10000000000 : ℝ)^8455 ≤ (27084616879737/100000000000000 : ℝ)^6407 := by
    have hnat : (3716469827 : ℕ)^8455*100000000000000^6407 ≤ 27084616879737^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3716469827 10000000000 27084616879737 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154222821/5000000000 : ℝ), (624223899/1250000000 : ℝ), (3716469827/10000000000 : ℝ)] ![(32917819816977/100000000000000 : ℝ), (39997563296123/100000000000000 : ℝ), (27084616879737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154222821/5000000000 : ℝ)|^8455 ≤ (32917819816977/100000000000000 : ℝ)^6407
        have hw : |(2154222821/5000000000 : ℝ)|=(2154222821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(624223899/1250000000 : ℝ)|^8455 ≤ (39997563296123/100000000000000 : ℝ)^6407
        have hw : |(624223899/1250000000 : ℝ)|=(624223899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3716469827/10000000000 : ℝ)|^8455 ≤ (27084616879737/100000000000000 : ℝ)^6407
        have hw : |(3716469827/10000000000 : ℝ)|=(3716469827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1262_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27361/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (897/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1259/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9957/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27361/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (897/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27361/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (897/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27361/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (897/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27361/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (897/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27361/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (897/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27361/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (897/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (897/100000 : ℝ) ^ (4227/1024 : ℝ) ≤ (17710921311/5000000000000000000 : ℝ) := by
    have hpowers : (897/100000 : ℝ)^4227 ≤ (17710921311/5000000000000000000 : ℝ)^1024 := by
      have hnat : (897 : ℕ)^4227*5000000000000000000^1024 ≤ 17710921311^1024*100000^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        897 100000 17710921311 5000000000000000000 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (897/100000 : ℝ)) (X := (17710921311/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27361/100000 : ℝ) ^ (4227/1024 : ℝ) ≤ (237405259993761267/50000000000000000000 : ℝ) := by
    have hpowers : (27361/100000 : ℝ)^4227 ≤ (237405259993761267/50000000000000000000 : ℝ)^1024 := by
      have hnat : (27361 : ℕ)^4227*50000000000000000000^1024 ≤ 237405259993761267^1024*100000^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27361 100000 237405259993761267 50000000000000000000 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27361/100000 : ℝ)) (X := (237405259993761267/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500000017710921311/2500000000000000000 : ℝ) ≤ (5000000008581019/5000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (2500000017710921311/2500000000000000000 : ℝ)^1024 ≤ (5000000008581019/5000000000000000 : ℝ)^4227 := by
      have hnat : (2500000017710921311 : ℕ)^1024*5000000000000000^4227 ≤ 5000000008581019^4227*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500000017710921311 2500000000000000000 5000000008581019 5000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000008581019/5000000000000000 : ℝ)) (X := (2500000017710921311/2500000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50237405437102974377/50000000000000000000 : ℝ) ≤ (10011481762649073/10000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (50237405437102974377/50000000000000000000 : ℝ)^1024 ≤ (10011481762649073/10000000000000000 : ℝ)^4227 := by
      have hnat : (50237405437102974377 : ℕ)^1024*10000000000000000^4227 ≤ 10011481762649073^4227*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50237405437102974377 50000000000000000000 10011481762649073 10000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011481762649073/10000000000000000 : ℝ)) (X := (50237405437102974377/50000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25237405259993761267/25000000000000000000 : ℝ) ≤ (2505740877034027/2500000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (25237405259993761267/25000000000000000000 : ℝ)^1024 ≤ (2505740877034027/2500000000000000 : ℝ)^4227 := by
      have hnat : (25237405259993761267 : ℕ)^1024*2500000000000000^4227 ≤ 2505740877034027^4227*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25237405259993761267 25000000000000000000 2505740877034027 2500000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2505740877034027/2500000000000000 : ℝ)) (X := (25237405259993761267/25000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(17710921311/5000000000000000000 : ℝ) ≤ ((132309701101386216421/132320000000000000000 : ℝ)+2*(2296349097407/529280000000000 : ℝ)*(897/100000 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (132309701101386216421/132320000000000000000 : ℝ)+2*(2296349097407/529280000000000 : ℝ)*(897/100000 : ℝ)=(5000000008581019/5000000000000000 : ℝ) by norm_num, show 1+2*(17710921311/5000000000000000000 : ℝ)=(2500000017710921311/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(237405259993761267/50000000000000000000 : ℝ)+(17710921311/5000000000000000000 : ℝ) ≤ ((132309701101386216421/132320000000000000000 : ℝ)+(2296349097407/529280000000000 : ℝ)*((27361/100000 : ℝ)+(897/100000 : ℝ)))^(4227/1024 : ℝ) := by
    rw [show (132309701101386216421/132320000000000000000 : ℝ)+(2296349097407/529280000000000 : ℝ)*((27361/100000 : ℝ)+(897/100000 : ℝ))=(10011481762649073/10000000000000000 : ℝ) by norm_num, show 1+(237405259993761267/50000000000000000000 : ℝ)+(17710921311/5000000000000000000 : ℝ)=(50237405437102974377/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(237405259993761267/50000000000000000000 : ℝ) ≤ ((132309701101386216421/132320000000000000000 : ℝ)+2*(2296349097407/529280000000000 : ℝ)*(27361/100000 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (132309701101386216421/132320000000000000000 : ℝ)+2*(2296349097407/529280000000000 : ℝ)*(27361/100000 : ℝ)=(2505740877034027/2500000000000000 : ℝ) by norm_num, show 1+2*(237405259993761267/50000000000000000000 : ℝ)=(25237405259993761267/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (132309701101386216421/132320000000000000000 : ℝ)*(X 1 0+X 2 0)+(2296349097407/529280000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (897/100000 : ℝ)) (hi := (27361/100000 : ℝ)) (c := (132309701101386216421/132320000000000000000 : ℝ)) (alpha := (2296349097407/529280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (132309701101386216421/132320000000000000000 : ℝ)*(X 0 1+X 2 1)+(2296349097407/529280000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (897/100000 : ℝ)) (hi := (27361/100000 : ℝ)) (c := (132309701101386216421/132320000000000000000 : ℝ)) (alpha := (2296349097407/529280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (132309701101386216421/132320000000000000000 : ℝ)*(X 0 2+X 1 2)+(2296349097407/529280000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (897/100000 : ℝ)) (hi := (27361/100000 : ℝ)) (c := (132309701101386216421/132320000000000000000 : ℝ)) (alpha := (2296349097407/529280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2050364737/10000000000 : ℝ)*X 0 0+(2835305569/5000000000 : ℝ)*X 0 1+(2513209429/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2706285643/5000000000 : ℝ)*X 1 0+(-1197979823/5000000000 : ℝ)*X 1 1+(5026418699/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5412571119/10000000000 : ℝ)*X 2 0+(1256604713/2500000000 : ℝ)*X 2 1+(-2395959669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2153558067/5000000000 : ℝ)*X 0 0+(739810039/2000000000 : ℝ)*X 0 1+(1252722019/2500000000 : ℝ)*X 0 2+(2153558067/5000000000 : ℝ)*X 1 0+(739810039/2000000000 : ℝ)*X 1 1+(1252722019/2500000000 : ℝ)*X 1 2+(2153558067/5000000000 : ℝ)*X 2 0+(739810039/2000000000 : ℝ)*X 2 1+(1252722019/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-256377229/1250000000 : ℝ)*X 0 0+(2517407269/5000000000 : ℝ)*X 0 1+(5662056883/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5246452903/10000000000 : ℝ)*X 1 0+(-27505021/156250000 : ℝ)*X 1 1+(5662057323/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5246452821/10000000000 : ℝ)*X 2 0+(70775713/125000000 : ℝ)*X 2 1+(-1760321873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2154222821/5000000000 : ℝ)*X 0 0+(624223899/1250000000 : ℝ)*X 0 1+(3716469827/10000000000 : ℝ)*X 0 2+(2154222821/5000000000 : ℝ)*X 1 0+(624223899/1250000000 : ℝ)*X 1 1+(3716469827/10000000000 : ℝ)*X 1 2+(2154222821/5000000000 : ℝ)*X 2 0+(624223899/1250000000 : ℝ)*X 2 1+(3716469827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5741384231625760344432443121/827000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7903103/10000000000000 : ℝ)*(base1) + (36379817/2500000000000 : ℝ)*(base19) + (351824113/25000000000000 : ℝ)*(base23) + (40608407/25000000000000 : ℝ)*(upper3) + (35405683/25000000000000 : ℝ)*(upper5) + (289330574572567/25000000000000 : ℝ)*(major0) + (289330574572567/25000000000000 : ℝ)*(major1) + (289330574572567/25000000000000 : ℝ)*(major2) + (38808487074899/2500000000000 : ℝ)*(sp0) + (1552345766297889/100000000000000 : ℝ)*(sp1) + (776172907097059/50000000000000 : ℝ)*(sp2) + (762293116017953/100000000000000 : ℝ)*(sp3) + (7817525639/100000000000000 : ℝ)*(sp4) + (197431343/5000000000000 : ℝ)*(sp7) + (762297143675843/100000000000000 : ℝ)*(f.failure) + (155234722149057/10000000000000 : ℝ)*(f.sum) + (230278866619/1323200000000000000000000000 : ℝ)*base66 + (2491448818037772707/3308000000000000000000000000000000 : ℝ)*base67 + (16288094797146227293/3308000000000000000000000000000000 : ℝ)*base70 + (13072700639534227293/3308000000000000000000000000000000 : ℝ)*base72 + (7266827819407/6616000000000000000000000000 : ℝ)*base74 + (7234394843298227293/3308000000000000000000000000000000 : ℝ)*base76 + (22410069142238227293/3308000000000000000000000000000000 : ℝ)*base78 + (40819435248354227293/3308000000000000000000000000000000 : ℝ)*base80 + (22646209701127/6616000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (4433287/2500000000000000000000 : ℝ)*base90 + (4433287/2500000000000000000000 : ℝ)*base92 + (4433287/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7693933583166038114169668349/3308000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85975959/25000000000000 : ℝ)*(base19) + (320215917/100000000000000 : ℝ)*(base23) + (17209429/100000000000000 : ℝ)*(upper2) + (77052589/100000000000000 : ℝ)*(upper3) + (23488023/50000000000000 : ℝ)*(upper5) + (1188583982668123/100000000000000 : ℝ)*(major0) + (1188583982668123/100000000000000 : ℝ)*(major1) + (1188583982668123/100000000000000 : ℝ)*(major2) + (559591633/25000000000000 : ℝ)*(sp1) + (1241241191/100000000000000 : ℝ)*(sp2) + (199284938933869/12500000000000 : ℝ)*(sp4) + (199284616150073/12500000000000 : ℝ)*(sp5) + (398569487503461/25000000000000 : ℝ)*(sp6) + (24465261760523/3125000000000 : ℝ)*(sp7) + (24465261760523/3125000000000 : ℝ)*(f.failure) + (199284938933869/12500000000000 : ℝ)*(f.sum) + (79039437769189/26464000000000000000000000000 : ℝ)*base65 + (45531566139454902217/13232000000000000000000000000000000 : ℝ)*base68 + (32218821829054902217/13232000000000000000000000000000000 : ℝ)*base70 + (62456227365950902217/13232000000000000000000000000000000 : ℝ)*base72 + (16232855484769/5292800000000000000000000000 : ℝ)*base73 + (27025207366142902217/13232000000000000000000000000000000 : ℝ)*base76 + (31227375990481097783/13232000000000000000000000000000000 : ℝ)*base77 + (31567761328766902217/13232000000000000000000000000000000 : ℝ)*base80 + (33774336857477/26464000000000000000000000000 : ℝ)*base81 + (421157/78125000000000000000 : ℝ)*base90 + (421157/78125000000000000000 : ℝ)*base92 + (421157/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1262_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27361/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (897/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1259/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9957/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1262_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1262_s2_0 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-209741429/1000000000 : ℝ)*x 0 + (5489412121/10000000000 : ℝ)*x 1 + (1294398721/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209741429/1000000000 : ℝ)^8455 ≤ (795683481799/6250000000000 : ℝ)^6407 := by
    have hnat : (209741429 : ℕ)^8455*6250000000000^6407 ≤ 795683481799^6407*1000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209741429 1000000000 795683481799 6250000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5489412121/10000000000 : ℝ)^8455 ≤ (5664677426337/12500000000000 : ℝ)^6407 := by
    have hnat : (5489412121 : ℕ)^8455*12500000000000^6407 ≤ 5664677426337^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489412121 10000000000 5664677426337 12500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294398721/2500000000 : ℝ)^8455 ≤ (209758224337/500000000000 : ℝ)^6407 := by
    have hnat : (1294398721 : ℕ)^8455*500000000000^6407 ≤ 209758224337^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294398721 2500000000 209758224337 500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-209741429/1000000000 : ℝ), (5489412121/10000000000 : ℝ), (1294398721/2500000000 : ℝ)] ![(795683481799/6250000000000 : ℝ), (5664677426337/12500000000000 : ℝ), (209758224337/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-209741429/1000000000 : ℝ)|^8455 ≤ (795683481799/6250000000000 : ℝ)^6407
        have hw : |(-209741429/1000000000 : ℝ)|=(209741429/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5489412121/10000000000 : ℝ)|^8455 ≤ (5664677426337/12500000000000 : ℝ)^6407
        have hw : |(5489412121/10000000000 : ℝ)|=(5489412121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294398721/2500000000 : ℝ)|^8455 ≤ (209758224337/500000000000 : ℝ)^6407
        have hw : |(1294398721/2500000000 : ℝ)|=(1294398721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s2_1 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368876327/10000000000 : ℝ)*x 0 + (-2258822027/10000000000 : ℝ)*x 1 + (5177595073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368876327/10000000000 : ℝ)^8455 ≤ (44008901218613/100000000000000 : ℝ)^6407 := by
    have hnat : (5368876327 : ℕ)^8455*100000000000000^6407 ≤ 44008901218613^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368876327 10000000000 44008901218613 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2258822027/10000000000 : ℝ)^8455 ≤ (7019725943473/50000000000000 : ℝ)^6407 := by
    have hnat : (2258822027 : ℕ)^8455*50000000000000^6407 ≤ 7019725943473^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258822027 10000000000 7019725943473 50000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177595073/10000000000 : ℝ)^8455 ≤ (8390329377657/20000000000000 : ℝ)^6407 := by
    have hnat : (5177595073 : ℕ)^8455*20000000000000^6407 ≤ 8390329377657^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177595073 10000000000 8390329377657 20000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368876327/10000000000 : ℝ), (-2258822027/10000000000 : ℝ), (5177595073/10000000000 : ℝ)] ![(44008901218613/100000000000000 : ℝ), (7019725943473/50000000000000 : ℝ), (8390329377657/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368876327/10000000000 : ℝ)|^8455 ≤ (44008901218613/100000000000000 : ℝ)^6407
        have hw : |(5368876327/10000000000 : ℝ)|=(5368876327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2258822027/10000000000 : ℝ)|^8455 ≤ (7019725943473/50000000000000 : ℝ)^6407
        have hw : |(-2258822027/10000000000 : ℝ)|=(2258822027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177595073/10000000000 : ℝ)|^8455 ≤ (8390329377657/20000000000000 : ℝ)^6407
        have hw : |(5177595073/10000000000 : ℝ)|=(5177595073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s2_2 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1073775251/2000000000 : ℝ)*x 0 + (2588797547/5000000000 : ℝ)*x 1 + (-1129411047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073775251/2000000000 : ℝ)^8455 ≤ (11002225109943/25000000000000 : ℝ)^6407 := by
    have hnat : (1073775251 : ℕ)^8455*25000000000000^6407 ≤ 11002225109943^6407*2000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073775251 2000000000 11002225109943 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588797547/5000000000 : ℝ)^8455 ≤ (10487911778207/25000000000000 : ℝ)^6407 := by
    have hnat : (2588797547 : ℕ)^8455*25000000000000^6407 ≤ 10487911778207^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588797547 5000000000 10487911778207 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129411047/5000000000 : ℝ)^8455 ≤ (1403945243649/10000000000000 : ℝ)^6407 := by
    have hnat : (1129411047 : ℕ)^8455*10000000000000^6407 ≤ 1403945243649^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129411047 5000000000 1403945243649 10000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073775251/2000000000 : ℝ), (2588797547/5000000000 : ℝ), (-1129411047/5000000000 : ℝ)] ![(11002225109943/25000000000000 : ℝ), (10487911778207/25000000000000 : ℝ), (1403945243649/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073775251/2000000000 : ℝ)|^8455 ≤ (11002225109943/25000000000000 : ℝ)^6407
        have hw : |(1073775251/2000000000 : ℝ)|=(1073775251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588797547/5000000000 : ℝ)|^8455 ≤ (10487911778207/25000000000000 : ℝ)^6407
        have hw : |(2588797547/5000000000 : ℝ)|=(2588797547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1129411047/5000000000 : ℝ)|^8455 ≤ (1403945243649/10000000000000 : ℝ)^6407
        have hw : |(-1129411047/5000000000 : ℝ)|=(1129411047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s2_3 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1084914251/2500000000 : ℝ)*x 0 + (4033362691/10000000000 : ℝ)*x 1 + (1167087253/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084914251/2500000000 : ℝ)^8455 ≤ (33232872927303/100000000000000 : ℝ)^6407 := by
    have hnat : (1084914251 : ℕ)^8455*100000000000000^6407 ≤ 33232872927303^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084914251 2500000000 33232872927303 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4033362691/10000000000 : ℝ)^8455 ≤ (3017301237769/10000000000000 : ℝ)^6407 := by
    have hnat : (4033362691 : ℕ)^8455*10000000000000^6407 ≤ 3017301237769^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033362691 10000000000 3017301237769 10000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1167087253/2500000000 : ℝ)^8455 ≤ (4574264335487/12500000000000 : ℝ)^6407 := by
    have hnat : (1167087253 : ℕ)^8455*12500000000000^6407 ≤ 4574264335487^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167087253 2500000000 4574264335487 12500000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084914251/2500000000 : ℝ), (4033362691/10000000000 : ℝ), (1167087253/2500000000 : ℝ)] ![(33232872927303/100000000000000 : ℝ), (3017301237769/10000000000000 : ℝ), (4574264335487/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084914251/2500000000 : ℝ)|^8455 ≤ (33232872927303/100000000000000 : ℝ)^6407
        have hw : |(1084914251/2500000000 : ℝ)|=(1084914251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4033362691/10000000000 : ℝ)|^8455 ≤ (3017301237769/10000000000000 : ℝ)^6407
        have hw : |(4033362691/10000000000 : ℝ)|=(4033362691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1167087253/2500000000 : ℝ)|^8455 ≤ (4574264335487/12500000000000 : ℝ)^6407
        have hw : |(1167087253/2500000000 : ℝ)|=(1167087253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s2_4 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2097488637/10000000000 : ℝ)*x 0 + (1294892967/2500000000 : ℝ)*x 1 + (5487416851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097488637/10000000000 : ℝ)^8455 ≤ (636576561751/5000000000000 : ℝ)^6407 := by
    have hnat : (2097488637 : ℕ)^8455*5000000000000^6407 ≤ 636576561751^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097488637 10000000000 636576561751 5000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294892967/2500000000 : ℝ)^8455 ≤ (41972785085819/100000000000000 : ℝ)^6407 := by
    have hnat : (1294892967 : ℕ)^8455*100000000000000^6407 ≤ 41972785085819^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294892967 2500000000 41972785085819 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5487416851/10000000000 : ℝ)^8455 ≤ (45295683659071/100000000000000 : ℝ)^6407 := by
    have hnat : (5487416851 : ℕ)^8455*100000000000000^6407 ≤ 45295683659071^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487416851 10000000000 45295683659071 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2097488637/10000000000 : ℝ), (1294892967/2500000000 : ℝ), (5487416851/10000000000 : ℝ)] ![(636576561751/5000000000000 : ℝ), (41972785085819/100000000000000 : ℝ), (45295683659071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2097488637/10000000000 : ℝ)|^8455 ≤ (636576561751/5000000000000 : ℝ)^6407
        have hw : |(-2097488637/10000000000 : ℝ)|=(2097488637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294892967/2500000000 : ℝ)|^8455 ≤ (41972785085819/100000000000000 : ℝ)^6407
        have hw : |(1294892967/2500000000 : ℝ)|=(1294892967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5487416851/10000000000 : ℝ)|^8455 ≤ (45295683659071/100000000000000 : ℝ)^6407
        have hw : |(5487416851/10000000000 : ℝ)|=(5487416851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s2_5 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289148279/10000000000 : ℝ)*x 0 + (-974499989/5000000000 : ℝ)*x 1 + (1097483379/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289148279/10000000000 : ℝ)^8455 ≤ (43148518539413/100000000000000 : ℝ)^6407 := by
    have hnat : (5289148279 : ℕ)^8455*100000000000000^6407 ≤ 43148518539413^6407*10000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289148279 10000000000 43148518539413 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (974499989/5000000000 : ℝ)^8455 ≤ (1155579730431/10000000000000 : ℝ)^6407 := by
    have hnat : (974499989 : ℕ)^8455*10000000000000^6407 ≤ 1155579730431^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974499989 5000000000 1155579730431 10000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097483379/2000000000 : ℝ)^8455 ≤ (11323921034591/25000000000000 : ℝ)^6407 := by
    have hnat : (1097483379 : ℕ)^8455*25000000000000^6407 ≤ 11323921034591^6407*2000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097483379 2000000000 11323921034591 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289148279/10000000000 : ℝ), (-974499989/5000000000 : ℝ), (1097483379/2000000000 : ℝ)] ![(43148518539413/100000000000000 : ℝ), (1155579730431/10000000000000 : ℝ), (11323921034591/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289148279/10000000000 : ℝ)|^8455 ≤ (43148518539413/100000000000000 : ℝ)^6407
        have hw : |(5289148279/10000000000 : ℝ)|=(5289148279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-974499989/5000000000 : ℝ)|^8455 ≤ (1155579730431/10000000000000 : ℝ)^6407
        have hw : |(-974499989/5000000000 : ℝ)|=(974499989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1097483379/2000000000 : ℝ)|^8455 ≤ (11323921034591/25000000000000 : ℝ)^6407
        have hw : |(1097483379/2000000000 : ℝ)|=(1097483379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s2_6 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322287101/2500000000 : ℝ)*x 0 + (342963563/625000000 : ℝ)*x 1 + (-38979993/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322287101/2500000000 : ℝ)^8455 ≤ (10787129971279/25000000000000 : ℝ)^6407 := by
    have hnat : (1322287101 : ℕ)^8455*25000000000000^6407 ≤ 10787129971279^6407*2500000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322287101 2500000000 10787129971279 25000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342963563/625000000 : ℝ)^8455 ≤ (45295685369273/100000000000000 : ℝ)^6407 := by
    have hnat : (342963563 : ℕ)^8455*100000000000000^6407 ≤ 45295685369273^6407*625000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342963563 625000000 45295685369273 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38979993/200000000 : ℝ)^8455 ≤ (1155579473793/10000000000000 : ℝ)^6407 := by
    have hnat : (38979993 : ℕ)^8455*10000000000000^6407 ≤ 1155579473793^6407*200000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38979993 200000000 1155579473793 10000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322287101/2500000000 : ℝ), (342963563/625000000 : ℝ), (-38979993/200000000 : ℝ)] ![(10787129971279/25000000000000 : ℝ), (45295685369273/100000000000000 : ℝ), (1155579473793/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322287101/2500000000 : ℝ)|^8455 ≤ (10787129971279/25000000000000 : ℝ)^6407
        have hw : |(1322287101/2500000000 : ℝ)|=(1322287101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(342963563/625000000 : ℝ)|^8455 ≤ (45295685369273/100000000000000 : ℝ)^6407
        have hw : |(342963563/625000000 : ℝ)|=(342963563/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38979993/200000000 : ℝ)|^8455 ≤ (1155579473793/10000000000000 : ℝ)^6407
        have hw : |(-38979993/200000000 : ℝ)|=(38979993/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1262_s2_7 (p : ℝ) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2169903983/5000000000 : ℝ)*x 0 + (2332161779/5000000000 : ℝ)*x 1 + (2018712483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169903983/5000000000 : ℝ)^8455 ≤ (51928747703/156250000000 : ℝ)^6407 := by
    have hnat : (2169903983 : ℕ)^8455*156250000000^6407 ≤ 51928747703^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169903983 5000000000 51928747703 156250000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2332161779/5000000000 : ℝ)^8455 ≤ (7310495874527/20000000000000 : ℝ)^6407 := by
    have hnat : (2332161779 : ℕ)^8455*20000000000000^6407 ≤ 7310495874527^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2332161779 5000000000 7310495874527 20000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2018712483/5000000000 : ℝ)^8455 ≤ (30213122084683/100000000000000 : ℝ)^6407 := by
    have hnat : (2018712483 : ℕ)^8455*100000000000000^6407 ≤ 30213122084683^6407*5000000000^8455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018712483 5000000000 30213122084683 100000000000000 8455 6407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8455/2048 : ℝ)) 8455 6407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169903983/5000000000 : ℝ), (2332161779/5000000000 : ℝ), (2018712483/5000000000 : ℝ)] ![(51928747703/156250000000 : ℝ), (7310495874527/20000000000000 : ℝ), (30213122084683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169903983/5000000000 : ℝ)|^8455 ≤ (51928747703/156250000000 : ℝ)^6407
        have hw : |(2169903983/5000000000 : ℝ)|=(2169903983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2332161779/5000000000 : ℝ)|^8455 ≤ (7310495874527/20000000000000 : ℝ)^6407
        have hw : |(2332161779/5000000000 : ℝ)|=(2332161779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2018712483/5000000000 : ℝ)|^8455 ≤ (30213122084683/100000000000000 : ℝ)^6407
        have hw : |(2018712483/5000000000 : ℝ)|=(2018712483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1262_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9957/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1259/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (479/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16171/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9957/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1259/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9957/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1259/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9957/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1259/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9957/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1259/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9957/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1259/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9957/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1259/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1259/20000 : ℝ) ^ (4227/1024 : ℝ) ≤ (110239906799531/10000000000000000000 : ℝ) := by
    have hpowers : (1259/20000 : ℝ)^4227 ≤ (110239906799531/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1259 : ℕ)^4227*10000000000000000000^1024 ≤ 110239906799531^1024*20000^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1259 20000 110239906799531 10000000000000000000 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1259/20000 : ℝ)) (X := (110239906799531/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9957/50000 : ℝ) ^ (4227/1024 : ℝ) ≤ (63965468007808813/50000000000000000000 : ℝ) := by
    have hpowers : (9957/50000 : ℝ)^4227 ≤ (63965468007808813/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9957 : ℕ)^4227*50000000000000000000^1024 ≤ 63965468007808813^1024*50000^4227 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9957 50000 63965468007808813 50000000000000000000 4227 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9957/50000 : ℝ)) (X := (63965468007808813/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000110239906799531/5000000000000000000 : ℝ) ≤ (250001335281779/250000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (5000110239906799531/5000000000000000000 : ℝ)^1024 ≤ (250001335281779/250000000000000 : ℝ)^4227 := by
      have hnat : (5000110239906799531 : ℕ)^1024*250000000000000^4227 ≤ 250001335281779^4227*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000110239906799531 5000000000000000000 250001335281779 250000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250001335281779/250000000000000 : ℝ)) (X := (5000110239906799531/5000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12516129166885451617/12500000000000000000 : ℝ) ≤ (10003124333782307/10000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (12516129166885451617/12500000000000000000 : ℝ)^1024 ≤ (10003124333782307/10000000000000000 : ℝ)^4227 := by
      have hnat : (12516129166885451617 : ℕ)^1024*10000000000000000^4227 ≤ 10003124333782307^4227*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12516129166885451617 12500000000000000000 10003124333782307 10000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003124333782307/10000000000000000 : ℝ)) (X := (12516129166885451617/12500000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25063965468007808813/25000000000000000000 : ℝ) ≤ (5003097628146727/5000000000000000 : ℝ) ^ (4227/1024 : ℝ) := by
    have hpowers : (25063965468007808813/25000000000000000000 : ℝ)^1024 ≤ (5003097628146727/5000000000000000 : ℝ)^4227 := by
      have hnat : (25063965468007808813 : ℕ)^1024*5000000000000000^4227 ≤ 5003097628146727^4227*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25063965468007808813 25000000000000000000 5003097628146727 5000000000000000 1024 4227 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003097628146727/5000000000000000 : ℝ)) (X := (25063965468007808813/25000000000000000000 : ℝ)) (by norm_num) 4227 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(110239906799531/10000000000000000000 : ℝ) ≤ ((13615206449368658731/13619000000000000000 : ℝ)+2*(3070922511147/1361900000000000 : ℝ)*(1259/20000 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (13615206449368658731/13619000000000000000 : ℝ)+2*(3070922511147/1361900000000000 : ℝ)*(1259/20000 : ℝ)=(250001335281779/250000000000000 : ℝ) by norm_num, show 1+2*(110239906799531/10000000000000000000 : ℝ)=(5000110239906799531/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(63965468007808813/50000000000000000000 : ℝ)+(110239906799531/10000000000000000000 : ℝ) ≤ ((13615206449368658731/13619000000000000000 : ℝ)+(3070922511147/1361900000000000 : ℝ)*((9957/50000 : ℝ)+(1259/20000 : ℝ)))^(4227/1024 : ℝ) := by
    rw [show (13615206449368658731/13619000000000000000 : ℝ)+(3070922511147/1361900000000000 : ℝ)*((9957/50000 : ℝ)+(1259/20000 : ℝ))=(10003124333782307/10000000000000000 : ℝ) by norm_num, show 1+(63965468007808813/50000000000000000000 : ℝ)+(110239906799531/10000000000000000000 : ℝ)=(12516129166885451617/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(63965468007808813/50000000000000000000 : ℝ) ≤ ((13615206449368658731/13619000000000000000 : ℝ)+2*(3070922511147/1361900000000000 : ℝ)*(9957/50000 : ℝ))^(4227/1024 : ℝ) := by
    rw [show (13615206449368658731/13619000000000000000 : ℝ)+2*(3070922511147/1361900000000000 : ℝ)*(9957/50000 : ℝ)=(5003097628146727/5000000000000000 : ℝ) by norm_num, show 1+2*(63965468007808813/50000000000000000000 : ℝ)=(25063965468007808813/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13615206449368658731/13619000000000000000 : ℝ)*(X 1 0+X 2 0)+(3070922511147/1361900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (1259/20000 : ℝ)) (hi := (9957/50000 : ℝ)) (c := (13615206449368658731/13619000000000000000 : ℝ)) (alpha := (3070922511147/1361900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13615206449368658731/13619000000000000000 : ℝ)*(X 0 1+X 2 1)+(3070922511147/1361900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (1259/20000 : ℝ)) (hi := (9957/50000 : ℝ)) (c := (13615206449368658731/13619000000000000000 : ℝ)) (alpha := (3070922511147/1361900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13615206449368658731/13619000000000000000 : ℝ)*(X 0 2+X 1 2)+(3070922511147/1361900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4227/1024 : ℝ)) (lo := (1259/20000 : ℝ)) (hi := (9957/50000 : ℝ)) (c := (13615206449368658731/13619000000000000000 : ℝ)) (alpha := (3070922511147/1361900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-209741429/1000000000 : ℝ)*X 0 0+(5489412121/10000000000 : ℝ)*X 0 1+(1294398721/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5368876327/10000000000 : ℝ)*X 1 0+(-2258822027/10000000000 : ℝ)*X 1 1+(5177595073/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1073775251/2000000000 : ℝ)*X 2 0+(2588797547/5000000000 : ℝ)*X 2 1+(-1129411047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1084914251/2500000000 : ℝ)*X 0 0+(4033362691/10000000000 : ℝ)*X 0 1+(1167087253/2500000000 : ℝ)*X 0 2+(1084914251/2500000000 : ℝ)*X 1 0+(4033362691/10000000000 : ℝ)*X 1 1+(1167087253/2500000000 : ℝ)*X 1 2+(1084914251/2500000000 : ℝ)*X 2 0+(4033362691/10000000000 : ℝ)*X 2 1+(1167087253/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2097488637/10000000000 : ℝ)*X 0 0+(1294892967/2500000000 : ℝ)*X 0 1+(5487416851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289148279/10000000000 : ℝ)*X 1 0+(-974499989/5000000000 : ℝ)*X 1 1+(1097483379/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322287101/2500000000 : ℝ)*X 2 0+(342963563/625000000 : ℝ)*X 2 1+(-38979993/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2169903983/5000000000 : ℝ)*X 0 0+(2332161779/5000000000 : ℝ)*X 0 1+(2018712483/5000000000 : ℝ)*X 0 2+(2169903983/5000000000 : ℝ)*X 1 0+(2332161779/5000000000 : ℝ)*X 1 1+(2018712483/5000000000 : ℝ)*X 1 2+(2169903983/5000000000 : ℝ)*X 2 0+(2332161779/5000000000 : ℝ)*X 2 1+(2018712483/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1262_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (834990981254279005775062107/170237500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10303569/1250000000000 : ℝ)*(base19) + (746117497/100000000000000 : ℝ)*(base23) + (18876841/100000000000000 : ℝ)*(lower2) + (69927233/50000000000000 : ℝ)*(upper3) + (13450311/25000000000000 : ℝ)*(upper5) + (1195468944525599/50000000000000 : ℝ)*(major0) + (1195468944525599/50000000000000 : ℝ)*(major1) + (1195468944525599/50000000000000 : ℝ)*(major2) + (3207018710245051/100000000000000 : ℝ)*(sp0) + (1603514079191389/50000000000000 : ℝ)*(sp1) + (1603514118275401/50000000000000 : ℝ)*(sp2) + (787420725381429/50000000000000 : ℝ)*(sp3) + (10272423247/100000000000000 : ℝ)*(sp4) + (5181175923/100000000000000 : ℝ)*(sp7) + (787423315969391/50000000000000 : ℝ)*(f.failure) + (1603514491334149/50000000000000 : ℝ)*(f.sum) + (216975929431389/68095000000000000000000000000 : ℝ)*base66 + (1914941647780165131/680950000000000000000000000000000 : ℝ)*base68 + (647653328340365131/680950000000000000000000000000000 : ℝ)*base70 + (2194167222468315131/680950000000000000000000000000000 : ℝ)*base72 + (50055067106241/17023750000000000000000000000 : ℝ)*base74 + (3175881934232284869/680950000000000000000000000000000 : ℝ)*base75 + (9378400887787115131/680950000000000000000000000000000 : ℝ)*base78 + (367065228540115131/680950000000000000000000000000000 : ℝ)*base80 + (38431076904517/8511875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (13619581/1250000000000000000000 : ℝ)*base89 + (13619581/1250000000000000000000 : ℝ)*base91 + (13619581/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (184850412171578116609043817/85118750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (206924671/25000000000000 : ℝ)*(base19) + (1137236961/100000000000000 : ℝ)*(base23) + (1408459/2000000000000 : ℝ)*(upper2) + (68565109/50000000000000 : ℝ)*(upper3) + (18443893/50000000000000 : ℝ)*(upper5) + (302721326481931/12500000000000 : ℝ)*(major0) + (302721326481931/12500000000000 : ℝ)*(major1) + (302721326481931/12500000000000 : ℝ)*(major2) + (809073379/10000000000000 : ℝ)*(sp1) + (7349844897/50000000000000 : ℝ)*(sp2) + (812096458050069/25000000000000 : ℝ)*(sp4) + (1624188456883901/50000000000000 : ℝ)*(sp5) + (3248369995273521/100000000000000 : ℝ)*(sp6) + (199394414890173/12500000000000 : ℝ)*(sp7) + (199394414890173/12500000000000 : ℝ)*(f.failure) + (812096458050069/25000000000000 : ℝ)*(f.sum) + (77915860751171/17023750000000000000000000000 : ℝ)*base66 + (95182710036540439/170237500000000000000000000000000 : ℝ)*base68 + (1568731556418209561/170237500000000000000000000000000 : ℝ)*base69 + (1549473743615359561/170237500000000000000000000000000 : ℝ)*base71 + (122689287604907/34047500000000000000000000000 : ℝ)*base74 + (121927798250490439/170237500000000000000000000000000 : ℝ)*base76 + (277944343302184561/170237500000000000000000000000000 : ℝ)*base77 + (1373578733287409561/170237500000000000000000000000000 : ℝ)*base79 + (169546088376173/34047500000000000000000000000 : ℝ)*base81 + (3779257/312500000000000000000 : ℝ)*base90 + (3779257/312500000000000000000 : ℝ)*base92 + (3779257/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1262_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9957/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1259/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (479/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16171/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1262_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1262_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (479/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16171/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1262_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1262_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1262_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4227/1024 : ℝ) ≤ p) (hpb : p ≤ (8455/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37955091/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (479/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16171/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1262_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

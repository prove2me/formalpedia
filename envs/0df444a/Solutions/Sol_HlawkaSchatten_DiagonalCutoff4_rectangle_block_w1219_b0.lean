-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1219_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:10:26.406044+00:00
-- url     : https://prove2.me/submissions/bacdf958-dd89-4b5d-85a4-ff1c45396edb

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
theorem support_rectangle_w1219_s0_0 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1867677681/10000000000 : ℝ)*x 0 + (377294007/625000000 : ℝ)*x 1 + (2395066411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1867677681/10000000000 : ℝ)^2103 ≤ (10884274093237/100000000000000 : ℝ)^1591 := by
    have hnat : (1867677681 : ℕ)^2103*100000000000000^1591 ≤ 10884274093237^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867677681 10000000000 10884274093237 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (377294007/625000000 : ℝ)^2103 ≤ (3207296271069/6250000000000 : ℝ)^1591 := by
    have hnat : (377294007 : ℕ)^2103*6250000000000^1591 ≤ 3207296271069^1591*625000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377294007 625000000 3207296271069 6250000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2395066411/5000000000 : ℝ)^2103 ≤ (37798985557683/100000000000000 : ℝ)^1591 := by
    have hnat : (2395066411 : ℕ)^2103*100000000000000^1591 ≤ 37798985557683^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2395066411 5000000000 37798985557683 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1867677681/10000000000 : ℝ), (377294007/625000000 : ℝ), (2395066411/5000000000 : ℝ)] ![(10884274093237/100000000000000 : ℝ), (3207296271069/6250000000000 : ℝ), (37798985557683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1867677681/10000000000 : ℝ)|^2103 ≤ (10884274093237/100000000000000 : ℝ)^1591
        have hw : |(-1867677681/10000000000 : ℝ)|=(1867677681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(377294007/625000000 : ℝ)|^2103 ≤ (3207296271069/6250000000000 : ℝ)^1591
        have hw : |(377294007/625000000 : ℝ)|=(377294007/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2395066411/5000000000 : ℝ)|^2103 ≤ (37798985557683/100000000000000 : ℝ)^1591
        have hw : |(2395066411/5000000000 : ℝ)|=(2395066411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s0_1 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (551245529/1000000000 : ℝ)*x 0 + (-2580937503/10000000000 : ℝ)*x 1 + (2395066393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551245529/1000000000 : ℝ)^2103 ≤ (22755023976383/50000000000000 : ℝ)^1591 := by
    have hnat : (551245529 : ℕ)^2103*50000000000000^1591 ≤ 22755023976383^1591*1000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551245529 1000000000 22755023976383 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2580937503/10000000000 : ℝ)^2103 ≤ (8345483425057/50000000000000 : ℝ)^1591 := by
    have hnat : (2580937503 : ℕ)^2103*50000000000000^1591 ≤ 8345483425057^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2580937503 10000000000 8345483425057 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2395066393/5000000000 : ℝ)^2103 ≤ (9449746295547/25000000000000 : ℝ)^1591 := by
    have hnat : (2395066393 : ℕ)^2103*25000000000000^1591 ≤ 9449746295547^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2395066393 5000000000 9449746295547 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(551245529/1000000000 : ℝ), (-2580937503/10000000000 : ℝ), (2395066393/5000000000 : ℝ)] ![(22755023976383/50000000000000 : ℝ), (8345483425057/50000000000000 : ℝ), (9449746295547/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(551245529/1000000000 : ℝ)|^2103 ≤ (22755023976383/50000000000000 : ℝ)^1591
        have hw : |(551245529/1000000000 : ℝ)|=(551245529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2580937503/10000000000 : ℝ)|^2103 ≤ (8345483425057/50000000000000 : ℝ)^1591
        have hw : |(-2580937503/10000000000 : ℝ)|=(2580937503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2395066393/5000000000 : ℝ)|^2103 ≤ (9449746295547/25000000000000 : ℝ)^1591
        have hw : |(2395066393/5000000000 : ℝ)|=(2395066393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s0_2 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (172264227/312500000 : ℝ)*x 0 + (2395066409/5000000000 : ℝ)*x 1 + (-2580937497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172264227/312500000 : ℝ)^2103 ≤ (11377511917259/25000000000000 : ℝ)^1591 := by
    have hnat : (172264227 : ℕ)^2103*25000000000000^1591 ≤ 11377511917259^1591*312500000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172264227 312500000 11377511917259 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2395066409/5000000000 : ℝ)^2103 ≤ (37798985515961/100000000000000 : ℝ)^1591 := by
    have hnat : (2395066409 : ℕ)^2103*100000000000000^1591 ≤ 37798985515961^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2395066409 5000000000 37798985515961 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2580937497/10000000000 : ℝ)^2103 ≤ (667638671953/4000000000000 : ℝ)^1591 := by
    have hnat : (2580937497 : ℕ)^2103*4000000000000^1591 ≤ 667638671953^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2580937497 10000000000 667638671953 4000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172264227/312500000 : ℝ), (2395066409/5000000000 : ℝ), (-2580937497/10000000000 : ℝ)] ![(11377511917259/25000000000000 : ℝ), (37798985515961/100000000000000 : ℝ), (667638671953/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172264227/312500000 : ℝ)|^2103 ≤ (11377511917259/25000000000000 : ℝ)^1591
        have hw : |(172264227/312500000 : ℝ)|=(172264227/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2395066409/5000000000 : ℝ)|^2103 ≤ (37798985515961/100000000000000 : ℝ)^1591
        have hw : |(2395066409/5000000000 : ℝ)|=(2395066409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2580937497/10000000000 : ℝ)|^2103 ≤ (667638671953/4000000000000 : ℝ)^1591
        have hw : |(-2580937497/10000000000 : ℝ)|=(2580937497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s0_3 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (262177123/625000000 : ℝ)*x 0 + (3117776603/10000000000 : ℝ)*x 1 + (1408827197/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262177123/625000000 : ℝ)^2103 ≤ (31717616914799/100000000000000 : ℝ)^1591 := by
    have hnat : (262177123 : ℕ)^2103*100000000000000^1591 ≤ 31717616914799^1591*625000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262177123 625000000 31717616914799 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3117776603/10000000000 : ℝ)^2103 ≤ (5356722730421/25000000000000 : ℝ)^1591 := by
    have hnat : (3117776603 : ℕ)^2103*25000000000000^1591 ≤ 5356722730421^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3117776603 10000000000 5356722730421 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1408827197/2500000000 : ℝ)^2103 ≤ (46855492143363/100000000000000 : ℝ)^1591 := by
    have hnat : (1408827197 : ℕ)^2103*100000000000000^1591 ≤ 46855492143363^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1408827197 2500000000 46855492143363 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262177123/625000000 : ℝ), (3117776603/10000000000 : ℝ), (1408827197/2500000000 : ℝ)] ![(31717616914799/100000000000000 : ℝ), (5356722730421/25000000000000 : ℝ), (46855492143363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262177123/625000000 : ℝ)|^2103 ≤ (31717616914799/100000000000000 : ℝ)^1591
        have hw : |(262177123/625000000 : ℝ)|=(262177123/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3117776603/10000000000 : ℝ)|^2103 ≤ (5356722730421/25000000000000 : ℝ)^1591
        have hw : |(3117776603/10000000000 : ℝ)|=(3117776603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1408827197/2500000000 : ℝ)|^2103 ≤ (46855492143363/100000000000000 : ℝ)^1591
        have hw : |(1408827197/2500000000 : ℝ)|=(1408827197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s0_4 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-468150237/2500000000 : ℝ)*x 0 + (1205562313/2500000000 : ℝ)*x 1 + (1200690653/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (468150237/2500000000 : ℝ)^2103 ≤ (10922214683333/100000000000000 : ℝ)^1591 := by
    have hnat : (468150237 : ℕ)^2103*100000000000000^1591 ≤ 10922214683333^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468150237 2500000000 10922214683333 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1205562313/2500000000 : ℝ)^2103 ≤ (9533583542171/25000000000000 : ℝ)^1591 := by
    have hnat : (1205562313 : ℕ)^2103*25000000000000^1591 ≤ 9533583542171^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205562313 2500000000 9533583542171 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1200690653/2000000000 : ℝ)^2103 ≤ (10188690228533/20000000000000 : ℝ)^1591 := by
    have hnat : (1200690653 : ℕ)^2103*20000000000000^1591 ≤ 10188690228533^1591*2000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200690653 2000000000 10188690228533 20000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-468150237/2500000000 : ℝ), (1205562313/2500000000 : ℝ), (1200690653/2000000000 : ℝ)] ![(10922214683333/100000000000000 : ℝ), (9533583542171/25000000000000 : ℝ), (10188690228533/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-468150237/2500000000 : ℝ)|^2103 ≤ (10922214683333/100000000000000 : ℝ)^1591
        have hw : |(-468150237/2500000000 : ℝ)|=(468150237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1205562313/2500000000 : ℝ)|^2103 ≤ (9533583542171/25000000000000 : ℝ)^1591
        have hw : |(1205562313/2500000000 : ℝ)|=(1205562313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1200690653/2000000000 : ℝ)|^2103 ≤ (10188690228533/20000000000000 : ℝ)^1591
        have hw : |(1200690653/2000000000 : ℝ)|=(1200690653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s0_5 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2586690051/5000000000 : ℝ)*x 0 + (-1367615261/10000000000 : ℝ)*x 1 + (1200691021/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586690051/5000000000 : ℝ)^2103 ≤ (20923487623221/50000000000000 : ℝ)^1591 := by
    have hnat : (2586690051 : ℕ)^2103*50000000000000^1591 ≤ 20923487623221^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586690051 5000000000 20923487623221 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367615261/10000000000 : ℝ)^2103 ≤ (720955295117/10000000000000 : ℝ)^1591 := by
    have hnat : (1367615261 : ℕ)^2103*10000000000000^1591 ≤ 720955295117^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367615261 10000000000 720955295117 10000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1200691021/2000000000 : ℝ)^2103 ≤ (50943471780977/100000000000000 : ℝ)^1591 := by
    have hnat : (1200691021 : ℕ)^2103*100000000000000^1591 ≤ 50943471780977^1591*2000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200691021 2000000000 50943471780977 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586690051/5000000000 : ℝ), (-1367615261/10000000000 : ℝ), (1200691021/2000000000 : ℝ)] ![(20923487623221/50000000000000 : ℝ), (720955295117/10000000000000 : ℝ), (50943471780977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586690051/5000000000 : ℝ)|^2103 ≤ (20923487623221/50000000000000 : ℝ)^1591
        have hw : |(2586690051/5000000000 : ℝ)|=(2586690051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1367615261/10000000000 : ℝ)|^2103 ≤ (720955295117/10000000000000 : ℝ)^1591
        have hw : |(-1367615261/10000000000 : ℝ)|=(1367615261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1200691021/2000000000 : ℝ)|^2103 ≤ (50943471780977/100000000000000 : ℝ)^1591
        have hw : |(1200691021/2000000000 : ℝ)|=(1200691021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s0_6 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1293345259/2500000000 : ℝ)*x 0 + (3001726859/5000000000 : ℝ)*x 1 + (-683808031/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1293345259/2500000000 : ℝ)^2103 ≤ (41846985232767/100000000000000 : ℝ)^1591 := by
    have hnat : (1293345259 : ℕ)^2103*100000000000000^1591 ≤ 41846985232767^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293345259 2500000000 41846985232767 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3001726859/5000000000 : ℝ)^2103 ≤ (3183966013983/6250000000000 : ℝ)^1591 := by
    have hnat : (3001726859 : ℕ)^2103*6250000000000^1591 ≤ 3183966013983^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3001726859 5000000000 3183966013983 6250000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683808031/5000000000 : ℝ)^2103 ≤ (7209558532607/100000000000000 : ℝ)^1591 := by
    have hnat : (683808031 : ℕ)^2103*100000000000000^1591 ≤ 7209558532607^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683808031 5000000000 7209558532607 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1293345259/2500000000 : ℝ), (3001726859/5000000000 : ℝ), (-683808031/5000000000 : ℝ)] ![(41846985232767/100000000000000 : ℝ), (3183966013983/6250000000000 : ℝ), (7209558532607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1293345259/2500000000 : ℝ)|^2103 ≤ (41846985232767/100000000000000 : ℝ)^1591
        have hw : |(1293345259/2500000000 : ℝ)|=(1293345259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3001726859/5000000000 : ℝ)|^2103 ≤ (3183966013983/6250000000000 : ℝ)^1591
        have hw : |(3001726859/5000000000 : ℝ)|=(3001726859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-683808031/5000000000 : ℝ)|^2103 ≤ (7209558532607/100000000000000 : ℝ)^1591
        have hw : |(-683808031/5000000000 : ℝ)|=(683808031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s0_7 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4204775987/10000000000 : ℝ)*x 0 + (5570451813/10000000000 : ℝ)*x 1 + (1592461827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4204775987/10000000000 : ℝ)^2103 ≤ (31817018876519/100000000000000 : ℝ)^1591 := by
    have hnat : (4204775987 : ℕ)^2103*100000000000000^1591 ≤ 31817018876519^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204775987 10000000000 31817018876519 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5570451813/10000000000 : ℝ)^2103 ≤ (46144014166341/100000000000000 : ℝ)^1591 := by
    have hnat : (5570451813 : ℕ)^2103*100000000000000^1591 ≤ 46144014166341^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5570451813 10000000000 46144014166341 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1592461827/5000000000 : ℝ)^2103 ≤ (2203896693729/10000000000000 : ℝ)^1591 := by
    have hnat : (1592461827 : ℕ)^2103*10000000000000^1591 ≤ 2203896693729^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592461827 5000000000 2203896693729 10000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4204775987/10000000000 : ℝ), (5570451813/10000000000 : ℝ), (1592461827/5000000000 : ℝ)] ![(31817018876519/100000000000000 : ℝ), (46144014166341/100000000000000 : ℝ), (2203896693729/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4204775987/10000000000 : ℝ)|^2103 ≤ (31817018876519/100000000000000 : ℝ)^1591
        have hw : |(4204775987/10000000000 : ℝ)|=(4204775987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5570451813/10000000000 : ℝ)|^2103 ≤ (46144014166341/100000000000000 : ℝ)^1591
        have hw : |(5570451813/10000000000 : ℝ)|=(5570451813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1592461827/5000000000 : ℝ)|^2103 ≤ (2203896693729/10000000000000 : ℝ)^1591
        have hw : |(1592461827/5000000000 : ℝ)|=(1592461827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1219_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (363/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27523/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8411/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8411 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8411*1^2048 ≤ 0^2048*1^8411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8411 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8411/2048 : ℝ) ≤ (72533198964085657/3125000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8411 ≤ (72533198964085657/3125000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8411*3125000000000000000^2048 ≤ 72533198964085657^2048*5^8411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 72533198964085657 3125000000000000000 8411 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (72533198964085657/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8411 := by
      have hnat : (1 : ℕ)^2048*1^8411 ≤ 1^8411*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3197533198964085657/3125000000000000000 : ℝ) ≤ (10056026158301929/10000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (3197533198964085657/3125000000000000000 : ℝ)^2048 ≤ (10056026158301929/10000000000000000 : ℝ)^8411 := by
      have hnat : (3197533198964085657 : ℕ)^2048*10000000000000000^8411 ≤ 10056026158301929^8411*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3197533198964085657 3125000000000000000 10056026158301929 10000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10056026158301929/10000000000000000 : ℝ)) (X := (3197533198964085657/3125000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1635033198964085657/1562500000000000000 : ℝ) ≤ (5056026158301929/5000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (1635033198964085657/1562500000000000000 : ℝ)^2048 ≤ (5056026158301929/5000000000000000 : ℝ)^8411 := by
      have hnat : (1635033198964085657 : ℕ)^2048*5000000000000000^8411 ≤ 5056026158301929^8411*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1635033198964085657 1562500000000000000 5056026158301929 5000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5056026158301929/5000000000000000 : ℝ)) (X := (1635033198964085657/1562500000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(56026158301929/4000000000000000 : ℝ)*(0 : ℝ))^(8411/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(56026158301929/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(72533198964085657/3125000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(56026158301929/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8411/2048 : ℝ) := by
    rw [show (1 : ℝ)+(56026158301929/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10056026158301929/10000000000000000 : ℝ) by norm_num, show 1+(72533198964085657/3125000000000000000 : ℝ)+(0 : ℝ)=(3197533198964085657/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(72533198964085657/3125000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(56026158301929/4000000000000000 : ℝ)*(2/5 : ℝ))^(8411/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(56026158301929/4000000000000000 : ℝ)*(2/5 : ℝ)=(5056026158301929/5000000000000000 : ℝ) by norm_num, show 1+2*(72533198964085657/3125000000000000000 : ℝ)=(1635033198964085657/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(56026158301929/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56026158301929/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(56026158301929/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56026158301929/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(56026158301929/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56026158301929/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1867677681/10000000000 : ℝ)*X 0 0+(377294007/625000000 : ℝ)*X 0 1+(2395066411/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((551245529/1000000000 : ℝ)*X 1 0+(-2580937503/10000000000 : ℝ)*X 1 1+(2395066393/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((172264227/312500000 : ℝ)*X 2 0+(2395066409/5000000000 : ℝ)*X 2 1+(-2580937497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((262177123/625000000 : ℝ)*X 0 0+(3117776603/10000000000 : ℝ)*X 0 1+(1408827197/2500000000 : ℝ)*X 0 2+(262177123/625000000 : ℝ)*X 1 0+(3117776603/10000000000 : ℝ)*X 1 1+(1408827197/2500000000 : ℝ)*X 1 2+(262177123/625000000 : ℝ)*X 2 0+(3117776603/10000000000 : ℝ)*X 2 1+(1408827197/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-468150237/2500000000 : ℝ)*X 0 0+(1205562313/2500000000 : ℝ)*X 0 1+(1200690653/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2586690051/5000000000 : ℝ)*X 1 0+(-1367615261/10000000000 : ℝ)*X 1 1+(1200691021/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1293345259/2500000000 : ℝ)*X 2 0+(3001726859/5000000000 : ℝ)*X 2 1+(-683808031/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4204775987/10000000000 : ℝ)*X 0 0+(5570451813/10000000000 : ℝ)*X 0 1+(1592461827/5000000000 : ℝ)*X 0 2+(4204775987/10000000000 : ℝ)*X 1 0+(5570451813/10000000000 : ℝ)*X 1 1+(1592461827/5000000000 : ℝ)*X 1 2+(4204775987/10000000000 : ℝ)*X 2 0+(5570451813/10000000000 : ℝ)*X 2 1+(1592461827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1289971075130428786249623/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18321583/25000000000000 : ℝ)*(base1) + (1575871887/100000000000000 : ℝ)*(base19) + (1464267489/100000000000000 : ℝ)*(base23) + (13477589/12500000000000 : ℝ)*(base24) + (179617359/50000000000000 : ℝ)*(upper3) + (599714093558571/100000000000000 : ℝ)*(major0) + (599714093558571/100000000000000 : ℝ)*(major1) + (599714093558571/100000000000000 : ℝ)*(major2) + (80220574126119/10000000000000 : ℝ)*(sp0) + (200551896209189/25000000000000 : ℝ)*(sp1) + (401103794310221/50000000000000 : ℝ)*(sp2) + (198607995746963/50000000000000 : ℝ)*(sp3) + (1746366893/50000000000000 : ℝ)*(sp4) + (549326611/20000000000000 : ℝ)*(sp7) + (397218811413313/100000000000000 : ℝ)*(f.failure) + (200552290177161/25000000000000 : ℝ)*(f.sum) + (260614436783459/200000000000000000000000000000 : ℝ)*base65 + (1275359114216541/400000000000000000000000000000 : ℝ)*base68 + (600543387416541/400000000000000000000000000000 : ℝ)*base70 + (752227106583459/400000000000000000000000000000 : ℝ)*base71 + (177672101216541/200000000000000000000000000000 : ℝ)*base74 + (1742579514183459/400000000000000000000000000000 : ℝ)*base75 + (288679872616541/400000000000000000000000000000 : ℝ)*base78 + (1981751204183459/400000000000000000000000000000 : ℝ)*base79 + (176516066983459/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (36878177/10000000000000000000000 : ℝ)*base90 + (36878177/10000000000000000000000 : ℝ)*base92 + (36878177/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (837796771508193516319587/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (210773/625000000000 : ℝ)*(base1) + (565913253/25000000000000 : ℝ)*(base19) + (2439950423/100000000000000 : ℝ)*(base23) + (425760069/100000000000000 : ℝ)*(upper3) + (64958699/50000000000000 : ℝ)*(upper5) + (632893800477401/100000000000000 : ℝ)*(major0) + (632893800477401/100000000000000 : ℝ)*(major1) + (632893800477401/100000000000000 : ℝ)*(major2) + (202566487/4000000000000 : ℝ)*(sp1) + (2711014919/50000000000000 : ℝ)*(sp2) + (105824008216189/12500000000000 : ℝ)*(sp4) + (169316940838129/20000000000000 : ℝ)*(sp5) + (84658417002557/10000000000000 : ℝ)*(sp6) + (83839051191939/20000000000000 : ℝ)*(sp7) + (3353562317467/800000000000 : ℝ)*(f.failure) + (105824004000729/12500000000000 : ℝ)*(f.sum) + (2473618593471/200000000000000000000000000000 : ℝ)*base66 + (3721461124393471/400000000000000000000000000000 : ℝ)*base68 + (936386815206529/400000000000000000000000000000 : ℝ)*base69 + (1275878502793471/400000000000000000000000000000 : ℝ)*base72 + (979999233793471/200000000000000000000000000000 : ℝ)*base74 + (1977135422793471/400000000000000000000000000000 : ℝ)*base76 + (457299012406529/400000000000000000000000000000 : ℝ)*base77 + (1911168212393471/400000000000000000000000000000 : ℝ)*base80 + (366862758406529/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (40443/80000000000000000000 : ℝ)*base90 + (40443/80000000000000000000 : ℝ)*base92 + (40443/80000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1219_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (363/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27523/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1219_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1219_s1_0 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2066756287/10000000000 : ℝ)*x 0 + (2840715641/5000000000 : ℝ)*x 1 + (627246551/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2066756287/10000000000 : ℝ)^2103 ≤ (12443495118203/100000000000000 : ℝ)^1591 := by
    have hnat : (2066756287 : ℕ)^2103*100000000000000^1591 ≤ 12443495118203^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066756287 10000000000 12443495118203 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2840715641/5000000000 : ℝ)^2103 ≤ (47363061237893/100000000000000 : ℝ)^1591 := by
    have hnat : (2840715641 : ℕ)^2103*100000000000000^1591 ≤ 47363061237893^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2840715641 5000000000 47363061237893 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627246551/1250000000 : ℝ)^2103 ≤ (40193443632471/100000000000000 : ℝ)^1591 := by
    have hnat : (627246551 : ℕ)^2103*100000000000000^1591 ≤ 40193443632471^1591*1250000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627246551 1250000000 40193443632471 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2066756287/10000000000 : ℝ), (2840715641/5000000000 : ℝ), (627246551/1250000000 : ℝ)] ![(12443495118203/100000000000000 : ℝ), (47363061237893/100000000000000 : ℝ), (40193443632471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2066756287/10000000000 : ℝ)|^2103 ≤ (12443495118203/100000000000000 : ℝ)^1591
        have hw : |(-2066756287/10000000000 : ℝ)|=(2066756287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2840715641/5000000000 : ℝ)|^2103 ≤ (47363061237893/100000000000000 : ℝ)^1591
        have hw : |(2840715641/5000000000 : ℝ)|=(2840715641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(627246551/1250000000 : ℝ)|^2103 ≤ (40193443632471/100000000000000 : ℝ)^1591
        have hw : |(627246551/1250000000 : ℝ)|=(627246551/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s1_1 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5414912449/10000000000 : ℝ)*x 0 + (-2423423397/10000000000 : ℝ)*x 1 + (1254493099/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5414912449/10000000000 : ℝ)^2103 ≤ (2222431868189/5000000000000 : ℝ)^1591 := by
    have hnat : (5414912449 : ℕ)^2103*5000000000000^1591 ≤ 2222431868189^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414912449 10000000000 2222431868189 5000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2423423397/10000000000 : ℝ)^2103 ≤ (15357919122133/100000000000000 : ℝ)^1591 := by
    have hnat : (2423423397 : ℕ)^2103*100000000000000^1591 ≤ 15357919122133^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2423423397 10000000000 15357919122133 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1254493099/2500000000 : ℝ)^2103 ≤ (2009672175271/5000000000000 : ℝ)^1591 := by
    have hnat : (1254493099 : ℕ)^2103*5000000000000^1591 ≤ 2009672175271^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1254493099 2500000000 2009672175271 5000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5414912449/10000000000 : ℝ), (-2423423397/10000000000 : ℝ), (1254493099/2500000000 : ℝ)] ![(2222431868189/5000000000000 : ℝ), (15357919122133/100000000000000 : ℝ), (2009672175271/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5414912449/10000000000 : ℝ)|^2103 ≤ (2222431868189/5000000000000 : ℝ)^1591
        have hw : |(5414912449/10000000000 : ℝ)|=(5414912449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2423423397/10000000000 : ℝ)|^2103 ≤ (15357919122133/100000000000000 : ℝ)^1591
        have hw : |(-2423423397/10000000000 : ℝ)|=(2423423397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1254493099/2500000000 : ℝ)|^2103 ≤ (2009672175271/5000000000000 : ℝ)^1591
        have hw : |(1254493099/2500000000 : ℝ)|=(1254493099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s1_2 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (84608007/156250000 : ℝ)*x 0 + (1254493103/2500000000 : ℝ)*x 1 + (-2423423377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84608007/156250000 : ℝ)^2103 ≤ (4444863735293/10000000000000 : ℝ)^1591 := by
    have hnat : (84608007 : ℕ)^2103*10000000000000^1591 ≤ 4444863735293^1591*156250000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84608007 156250000 4444863735293 10000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1254493103/2500000000 : ℝ)^2103 ≤ (40193443674821/100000000000000 : ℝ)^1591 := by
    have hnat : (1254493103 : ℕ)^2103*100000000000000^1591 ≤ 40193443674821^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1254493103 2500000000 40193443674821 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2423423377/10000000000 : ℝ)^2103 ≤ (15357918954599/100000000000000 : ℝ)^1591 := by
    have hnat : (2423423377 : ℕ)^2103*100000000000000^1591 ≤ 15357918954599^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2423423377 10000000000 15357918954599 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84608007/156250000 : ℝ), (1254493103/2500000000 : ℝ), (-2423423377/10000000000 : ℝ)] ![(4444863735293/10000000000000 : ℝ), (40193443674821/100000000000000 : ℝ), (15357918954599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84608007/156250000 : ℝ)|^2103 ≤ (4444863735293/10000000000000 : ℝ)^1591
        have hw : |(84608007/156250000 : ℝ)|=(84608007/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1254493103/2500000000 : ℝ)|^2103 ≤ (40193443674821/100000000000000 : ℝ)^1591
        have hw : |(1254493103/2500000000 : ℝ)|=(1254493103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2423423377/10000000000 : ℝ)|^2103 ≤ (15357918954599/100000000000000 : ℝ)^1591
        have hw : |(-2423423377/10000000000 : ℝ)|=(2423423377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s1_3 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4310844909/10000000000 : ℝ)*x 0 + (3691258479/10000000000 : ℝ)*x 1 + (125778937/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310844909/10000000000 : ℝ)^2103 ≤ (4110274913753/12500000000000 : ℝ)^1591 := by
    have hnat : (4310844909 : ℕ)^2103*12500000000000^1591 ≤ 4110274913753^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310844909 10000000000 4110274913753 12500000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3691258479/10000000000 : ℝ)^2103 ≤ (26784700272181/100000000000000 : ℝ)^1591 := by
    have hnat : (3691258479 : ℕ)^2103*100000000000000^1591 ≤ 26784700272181^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3691258479 10000000000 26784700272181 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125778937/250000000 : ℝ)^2103 ≤ (5041637551127/12500000000000 : ℝ)^1591 := by
    have hnat : (125778937 : ℕ)^2103*12500000000000^1591 ≤ 5041637551127^1591*250000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125778937 250000000 5041637551127 12500000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310844909/10000000000 : ℝ), (3691258479/10000000000 : ℝ), (125778937/250000000 : ℝ)] ![(4110274913753/12500000000000 : ℝ), (26784700272181/100000000000000 : ℝ), (5041637551127/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310844909/10000000000 : ℝ)|^2103 ≤ (4110274913753/12500000000000 : ℝ)^1591
        have hw : |(4310844909/10000000000 : ℝ)|=(4310844909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3691258479/10000000000 : ℝ)|^2103 ≤ (26784700272181/100000000000000 : ℝ)^1591
        have hw : |(3691258479/10000000000 : ℝ)|=(3691258479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(125778937/250000000 : ℝ)|^2103 ≤ (5041637551127/12500000000000 : ℝ)^1591
        have hw : |(125778937/250000000 : ℝ)|=(125778937/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s1_4 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2067457143/10000000000 : ℝ)*x 0 + (5026764261/10000000000 : ℝ)*x 1 + (5672472981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2067457143/10000000000 : ℝ)^2103 ≤ (12449073069239/100000000000000 : ℝ)^1591 := by
    have hnat : (2067457143 : ℕ)^2103*100000000000000^1591 ≤ 12449073069239^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067457143 10000000000 12449073069239 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5026764261/10000000000 : ℝ)^2103 ≤ (40286554168797/100000000000000 : ℝ)^1591 := by
    have hnat : (5026764261 : ℕ)^2103*100000000000000^1591 ≤ 40286554168797^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5026764261 10000000000 40286554168797 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5672472981/10000000000 : ℝ)^2103 ≤ (5908046593261/12500000000000 : ℝ)^1591 := by
    have hnat : (5672472981 : ℕ)^2103*12500000000000^1591 ≤ 5908046593261^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5672472981 10000000000 5908046593261 12500000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2067457143/10000000000 : ℝ), (5026764261/10000000000 : ℝ), (5672472981/10000000000 : ℝ)] ![(12449073069239/100000000000000 : ℝ), (40286554168797/100000000000000 : ℝ), (5908046593261/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2067457143/10000000000 : ℝ)|^2103 ≤ (12449073069239/100000000000000 : ℝ)^1591
        have hw : |(-2067457143/10000000000 : ℝ)|=(2067457143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5026764261/10000000000 : ℝ)|^2103 ≤ (40286554168797/100000000000000 : ℝ)^1591
        have hw : |(5026764261/10000000000 : ℝ)|=(5026764261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5672472981/10000000000 : ℝ)|^2103 ≤ (5908046593261/12500000000000 : ℝ)^1591
        have hw : |(5672472981/10000000000 : ℝ)|=(5672472981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s1_5 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2622086187/5000000000 : ℝ)*x 0 + (-1768927637/10000000000 : ℝ)*x 1 + (1418116849/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2622086187/5000000000 : ℝ)^2103 ≤ (42605547369439/100000000000000 : ℝ)^1591 := by
    have hnat : (2622086187 : ℕ)^2103*100000000000000^1591 ≤ 42605547369439^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622086187 5000000000 42605547369439 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1768927637/10000000000 : ℝ)^2103 ≤ (10130141386047/100000000000000 : ℝ)^1591 := by
    have hnat : (1768927637 : ℕ)^2103*100000000000000^1591 ≤ 10130141386047^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768927637 10000000000 10130141386047 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1418116849/2500000000 : ℝ)^2103 ≤ (11816077808741/25000000000000 : ℝ)^1591 := by
    have hnat : (1418116849 : ℕ)^2103*25000000000000^1591 ≤ 11816077808741^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1418116849 2500000000 11816077808741 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2622086187/5000000000 : ℝ), (-1768927637/10000000000 : ℝ), (1418116849/2500000000 : ℝ)] ![(42605547369439/100000000000000 : ℝ), (10130141386047/100000000000000 : ℝ), (11816077808741/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2622086187/5000000000 : ℝ)|^2103 ≤ (42605547369439/100000000000000 : ℝ)^1591
        have hw : |(2622086187/5000000000 : ℝ)|=(2622086187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1768927637/10000000000 : ℝ)|^2103 ≤ (10130141386047/100000000000000 : ℝ)^1591
        have hw : |(-1768927637/10000000000 : ℝ)|=(1768927637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1418116849/2500000000 : ℝ)|^2103 ≤ (11816077808741/25000000000000 : ℝ)^1591
        have hw : |(1418116849/2500000000 : ℝ)|=(1418116849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s1_6 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1311043127/2500000000 : ℝ)*x 0 + (5672467853/10000000000 : ℝ)*x 1 + (-1768926781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311043127/2500000000 : ℝ)^2103 ≤ (21302774404223/50000000000000 : ℝ)^1591 := by
    have hnat : (1311043127 : ℕ)^2103*50000000000000^1591 ≤ 21302774404223^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311043127 2500000000 21302774404223 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5672467853/10000000000 : ℝ)^2103 ≤ (1477009883381/3125000000000 : ℝ)^1591 := by
    have hnat : (5672467853 : ℕ)^2103*3125000000000^1591 ≤ 1477009883381^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5672467853 10000000000 1477009883381 3125000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1768926781/10000000000 : ℝ)^2103 ≤ (5065067453223/50000000000000 : ℝ)^1591 := by
    have hnat : (1768926781 : ℕ)^2103*50000000000000^1591 ≤ 5065067453223^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768926781 10000000000 5065067453223 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1311043127/2500000000 : ℝ), (5672467853/10000000000 : ℝ), (-1768926781/10000000000 : ℝ)] ![(21302774404223/50000000000000 : ℝ), (1477009883381/3125000000000 : ℝ), (5065067453223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1311043127/2500000000 : ℝ)|^2103 ≤ (21302774404223/50000000000000 : ℝ)^1591
        have hw : |(1311043127/2500000000 : ℝ)|=(1311043127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5672467853/10000000000 : ℝ)|^2103 ≤ (1477009883381/3125000000000 : ℝ)^1591
        have hw : |(5672467853/10000000000 : ℝ)|=(5672467853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1768926781/10000000000 : ℝ)|^2103 ≤ (5065067453223/50000000000000 : ℝ)^1591
        have hw : |(-1768926781/10000000000 : ℝ)|=(1768926781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s1_7 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4312265957/10000000000 : ℝ)*x 0 + (1253349173/2500000000 : ℝ)*x 1 + (3709361181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312265957/10000000000 : ℝ)^2103 ≤ (32896527763997/100000000000000 : ℝ)^1591 := by
    have hnat : (4312265957 : ℕ)^2103*100000000000000^1591 ≤ 32896527763997^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312265957 10000000000 32896527763997 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1253349173/2500000000 : ℝ)^2103 ≤ (40145005056957/100000000000000 : ℝ)^1591 := by
    have hnat : (1253349173 : ℕ)^2103*100000000000000^1591 ≤ 40145005056957^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1253349173 2500000000 40145005056957 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3709361181/10000000000 : ℝ)^2103 ≤ (421226049367/1562500000000 : ℝ)^1591 := by
    have hnat : (3709361181 : ℕ)^2103*1562500000000^1591 ≤ 421226049367^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3709361181 10000000000 421226049367 1562500000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312265957/10000000000 : ℝ), (1253349173/2500000000 : ℝ), (3709361181/10000000000 : ℝ)] ![(32896527763997/100000000000000 : ℝ), (40145005056957/100000000000000 : ℝ), (421226049367/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312265957/10000000000 : ℝ)|^2103 ≤ (32896527763997/100000000000000 : ℝ)^1591
        have hw : |(4312265957/10000000000 : ℝ)|=(4312265957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1253349173/2500000000 : ℝ)|^2103 ≤ (40145005056957/100000000000000 : ℝ)^1591
        have hw : |(1253349173/2500000000 : ℝ)|=(1253349173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3709361181/10000000000 : ℝ)|^2103 ≤ (421226049367/1562500000000 : ℝ)^1591
        have hw : |(3709361181/10000000000 : ℝ)|=(3709361181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1219_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27523/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (363/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (6069/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20097/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27523/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (363/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27523/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (363/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27523/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (363/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27523/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (363/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27523/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (363/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27523/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (363/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (363/50000 : ℝ) ^ (8411/2048 : ℝ) ≤ (5126946317/3125000000000000000 : ℝ) := by
    have hpowers : (363/50000 : ℝ)^8411 ≤ (5126946317/3125000000000000000 : ℝ)^2048 := by
      have hnat : (363 : ℕ)^8411*3125000000000000000^2048 ≤ 5126946317^2048*50000^8411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        363 50000 5126946317 3125000000000000000 8411 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (363/50000 : ℝ)) (X := (5126946317/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27523/100000 : ℝ) ^ (8411/2048 : ℝ) ≤ (249941136333441957/50000000000000000000 : ℝ) := by
    have hpowers : (27523/100000 : ℝ)^8411 ≤ (249941136333441957/50000000000000000000 : ℝ)^2048 := by
      have hnat : (27523 : ℕ)^8411*50000000000000000000^2048 ≤ 249941136333441957^2048*100000^8411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27523 100000 249941136333441957 50000000000000000000 8411 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27523/100000 : ℝ)) (X := (249941136333441957/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562500005126946317/1562500000000000000 : ℝ) ≤ (10000000007989527/10000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (1562500005126946317/1562500000000000000 : ℝ)^2048 ≤ (10000000007989527/10000000000000000 : ℝ)^8411 := by
      have hnat : (1562500005126946317 : ℕ)^2048*10000000000000000^8411 ≤ 10000000007989527^8411*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562500005126946317 1562500000000000000 10000000007989527 10000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000007989527/10000000000000000 : ℝ)) (X := (1562500005126946317/1562500000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50249941218364583029/50000000000000000000 : ℝ) ≤ (10012148723377901/10000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (50249941218364583029/50000000000000000000 : ℝ)^2048 ≤ (10012148723377901/10000000000000000 : ℝ)^8411 := by
      have hnat : (50249941218364583029 : ℕ)^2048*10000000000000000^8411 ≤ 10012148723377901^8411*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50249941218364583029 50000000000000000000 10012148723377901 10000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012148723377901/10000000000000000 : ℝ)) (X := (50249941218364583029/50000000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25249941136333441957/25000000000000000000 : ℝ) ≤ (400971897550651/400000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (25249941136333441957/25000000000000000000 : ℝ)^2048 ≤ (400971897550651/400000000000000 : ℝ)^8411 := by
      have hnat : (25249941136333441957 : ℕ)^2048*400000000000000^8411 ≤ 400971897550651^8411*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25249941136333441957 25000000000000000000 400971897550651 400000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400971897550651/400000000000000 : ℝ)) (X := (25249941136333441957/25000000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5126946317/3125000000000000000 : ℝ) ≤ ((267952360279351435971/267970000000000000000 : ℝ)+2*(6074357694187/1339850000000000 : ℝ)*(363/50000 : ℝ))^(8411/2048 : ℝ) := by
    rw [show (267952360279351435971/267970000000000000000 : ℝ)+2*(6074357694187/1339850000000000 : ℝ)*(363/50000 : ℝ)=(10000000007989527/10000000000000000 : ℝ) by norm_num, show 1+2*(5126946317/3125000000000000000 : ℝ)=(1562500005126946317/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(249941136333441957/50000000000000000000 : ℝ)+(5126946317/3125000000000000000 : ℝ) ≤ ((267952360279351435971/267970000000000000000 : ℝ)+(6074357694187/1339850000000000 : ℝ)*((27523/100000 : ℝ)+(363/50000 : ℝ)))^(8411/2048 : ℝ) := by
    rw [show (267952360279351435971/267970000000000000000 : ℝ)+(6074357694187/1339850000000000 : ℝ)*((27523/100000 : ℝ)+(363/50000 : ℝ))=(10012148723377901/10000000000000000 : ℝ) by norm_num, show 1+(249941136333441957/50000000000000000000 : ℝ)+(5126946317/3125000000000000000 : ℝ)=(50249941218364583029/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(249941136333441957/50000000000000000000 : ℝ) ≤ ((267952360279351435971/267970000000000000000 : ℝ)+2*(6074357694187/1339850000000000 : ℝ)*(27523/100000 : ℝ))^(8411/2048 : ℝ) := by
    rw [show (267952360279351435971/267970000000000000000 : ℝ)+2*(6074357694187/1339850000000000 : ℝ)*(27523/100000 : ℝ)=(400971897550651/400000000000000 : ℝ) by norm_num, show 1+2*(249941136333441957/50000000000000000000 : ℝ)=(25249941136333441957/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (267952360279351435971/267970000000000000000 : ℝ)*(X 1 0+X 2 0)+(6074357694187/1339850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (363/50000 : ℝ)) (hi := (27523/100000 : ℝ)) (c := (267952360279351435971/267970000000000000000 : ℝ)) (alpha := (6074357694187/1339850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (267952360279351435971/267970000000000000000 : ℝ)*(X 0 1+X 2 1)+(6074357694187/1339850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (363/50000 : ℝ)) (hi := (27523/100000 : ℝ)) (c := (267952360279351435971/267970000000000000000 : ℝ)) (alpha := (6074357694187/1339850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (267952360279351435971/267970000000000000000 : ℝ)*(X 0 2+X 1 2)+(6074357694187/1339850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (363/50000 : ℝ)) (hi := (27523/100000 : ℝ)) (c := (267952360279351435971/267970000000000000000 : ℝ)) (alpha := (6074357694187/1339850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2066756287/10000000000 : ℝ)*X 0 0+(2840715641/5000000000 : ℝ)*X 0 1+(627246551/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5414912449/10000000000 : ℝ)*X 1 0+(-2423423397/10000000000 : ℝ)*X 1 1+(1254493099/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((84608007/156250000 : ℝ)*X 2 0+(1254493103/2500000000 : ℝ)*X 2 1+(-2423423377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4310844909/10000000000 : ℝ)*X 0 0+(3691258479/10000000000 : ℝ)*X 0 1+(125778937/250000000 : ℝ)*X 0 2+(4310844909/10000000000 : ℝ)*X 1 0+(3691258479/10000000000 : ℝ)*X 1 1+(125778937/250000000 : ℝ)*X 1 2+(4310844909/10000000000 : ℝ)*X 2 0+(3691258479/10000000000 : ℝ)*X 2 1+(125778937/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2067457143/10000000000 : ℝ)*X 0 0+(5026764261/10000000000 : ℝ)*X 0 1+(5672472981/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2622086187/5000000000 : ℝ)*X 1 0+(-1768927637/10000000000 : ℝ)*X 1 1+(1418116849/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1311043127/2500000000 : ℝ)*X 2 0+(5672467853/10000000000 : ℝ)*X 2 1+(-1768926781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4312265957/10000000000 : ℝ)*X 0 0+(1253349173/2500000000 : ℝ)*X 0 1+(3709361181/10000000000 : ℝ)*X 0 2+(4312265957/10000000000 : ℝ)*X 1 0+(1253349173/2500000000 : ℝ)*X 1 1+(3709361181/10000000000 : ℝ)*X 1 2+(4312265957/10000000000 : ℝ)*X 2 0+(1253349173/2500000000 : ℝ)*X 2 1+(3709361181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (59459475737881813329055581981/6699250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3189871/3125000000000 : ℝ)*(base1) + (956968773/50000000000000 : ℝ)*(base19) + (1913659191/100000000000000 : ℝ)*(base23) + (52341441/25000000000000 : ℝ)*(upper3) + (43313621/20000000000000 : ℝ)*(upper5) + (563402223901563/50000000000000 : ℝ)*(major0) + (563402223901563/50000000000000 : ℝ)*(major1) + (563402223901563/50000000000000 : ℝ)*(major2) + (1507262632826981/100000000000000 : ℝ)*(sp0) + (1507271176515347/100000000000000 : ℝ)*(sp1) + (753635588396851/50000000000000 : ℝ)*(sp2) + (746330103009759/100000000000000 : ℝ)*(sp3) + (1319962723/12500000000000 : ℝ)*(sp4) + (5304216317/100000000000000 : ℝ)*(sp7) + (746335509301949/100000000000000 : ℝ)*(f.failure) + (1507273090452893/100000000000000 : ℝ)*(f.sum) + (287902517332739/133985000000000000000000000000 : ℝ)*base65 + (111844539107444022673/13398500000000000000000000000000000 : ℝ)*base67 + (61353781947468977327/13398500000000000000000000000000000 : ℝ)*base70 + (28674385621987977327/13398500000000000000000000000000000 : ℝ)*base72 + (539241742602807/66992500000000000000000000000 : ℝ)*base73 + (47670843433121022673/13398500000000000000000000000000000 : ℝ)*base75 + (14496282213351522673/13398500000000000000000000000000000 : ℝ)*base77 + (22407033252181022673/13398500000000000000000000000000000 : ℝ)*base79 + (167566279514231/133985000000000000000000000000 : ℝ)*base82 + (76950179/10000000000000000000000 : ℝ)*base89 + (76950179/10000000000000000000000 : ℝ)*base91 + (76950179/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28015609321080502770833137887/6699250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61704801/20000000000000 : ℝ)*(base19) + (126881811/25000000000000 : ℝ)*(base23) + (193136227/100000000000000 : ℝ)*(lower2) + (285540023/100000000000000 : ℝ)*(lower3) + (54288933/20000000000000 : ℝ)*(lower4) + (578887849484467/50000000000000 : ℝ)*(major0) + (578887849484467/50000000000000 : ℝ)*(major1) + (578887849484467/50000000000000 : ℝ)*(major2) + (170318909/2500000000000 : ℝ)*(sp0) + (310395497/100000000000000 : ℝ)*(sp2) + (1548695222184269/100000000000000 : ℝ)*(sp4) + (96793857901039/6250000000000 : ℝ)*(sp5) + (48396913031809/3125000000000 : ℝ)*(sp6) + (766849223600483/100000000000000 : ℝ)*(sp7) + (766849223600483/100000000000000 : ℝ)*(f.failure) + (1548702034940629/100000000000000 : ℝ)*(f.sum) + (74185778919247/16748125000000000000000000000 : ℝ)*base65 + (119151223375122862457/13398500000000000000000000000000000 : ℝ)*base67 + (61290668986163362457/13398500000000000000000000000000000 : ℝ)*base69 + (176243080777285862457/13398500000000000000000000000000000 : ℝ)*base71 + (3824078248433/16748125000000000000000000000 : ℝ)*base74 + (102288198707665862457/13398500000000000000000000000000000 : ℝ)*base75 + (110494974718261862457/13398500000000000000000000000000000 : ℝ)*base77 + (268585772467771362457/13398500000000000000000000000000000 : ℝ)*base79 + (114210322416397/66992500000000000000000000000 : ℝ)*base82 + (81895107/10000000000000000000000 : ℝ)*base90 + (81895107/10000000000000000000000 : ℝ)*base92 + (81895107/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1219_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27523/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (363/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6069/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20097/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1219_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1219_s2_0 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1057982671/5000000000 : ℝ)*x 0 + (5496764209/10000000000 : ℝ)*x 1 + (1034255499/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057982671/5000000000 : ℝ)^2103 ≤ (12836609609367/100000000000000 : ℝ)^1591 := by
    have hnat : (1057982671 : ℕ)^2103*100000000000000^1591 ≤ 12836609609367^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057982671 5000000000 12836609609367 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5496764209/10000000000 : ℝ)^2103 ≤ (45338894728803/100000000000000 : ℝ)^1591 := by
    have hnat : (5496764209 : ℕ)^2103*100000000000000^1591 ≤ 45338894728803^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496764209 10000000000 45338894728803 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034255499/2000000000 : ℝ)^2103 ≤ (10456123912921/25000000000000 : ℝ)^1591 := by
    have hnat : (1034255499 : ℕ)^2103*25000000000000^1591 ≤ 10456123912921^1591*2000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034255499 2000000000 10456123912921 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1057982671/5000000000 : ℝ), (5496764209/10000000000 : ℝ), (1034255499/2000000000 : ℝ)] ![(12836609609367/100000000000000 : ℝ), (45338894728803/100000000000000 : ℝ), (10456123912921/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1057982671/5000000000 : ℝ)|^2103 ≤ (12836609609367/100000000000000 : ℝ)^1591
        have hw : |(-1057982671/5000000000 : ℝ)|=(1057982671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5496764209/10000000000 : ℝ)|^2103 ≤ (45338894728803/100000000000000 : ℝ)^1591
        have hw : |(5496764209/10000000000 : ℝ)|=(5496764209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034255499/2000000000 : ℝ)|^2103 ≤ (10456123912921/25000000000000 : ℝ)^1591
        have hw : |(1034255499/2000000000 : ℝ)|=(1034255499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s2_1 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5370626941/10000000000 : ℝ)*x 0 + (-2284702063/10000000000 : ℝ)*x 1 + (5171277427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370626941/10000000000 : ℝ)^2103 ≤ (43968766051457/100000000000000 : ℝ)^1591 := by
    have hnat : (5370626941 : ℕ)^2103*100000000000000^1591 ≤ 43968766051457^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370626941 10000000000 43968766051457 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2284702063/10000000000 : ℝ)^2103 ≤ (3551684752197/25000000000000 : ℝ)^1591 := by
    have hnat : (2284702063 : ℕ)^2103*25000000000000^1591 ≤ 3551684752197^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284702063 10000000000 3551684752197 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5171277427/10000000000 : ℝ)^2103 ≤ (41824494924723/100000000000000 : ℝ)^1591 := by
    have hnat : (5171277427 : ℕ)^2103*100000000000000^1591 ≤ 41824494924723^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171277427 10000000000 41824494924723 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370626941/10000000000 : ℝ), (-2284702063/10000000000 : ℝ), (5171277427/10000000000 : ℝ)] ![(43968766051457/100000000000000 : ℝ), (3551684752197/25000000000000 : ℝ), (41824494924723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370626941/10000000000 : ℝ)|^2103 ≤ (43968766051457/100000000000000 : ℝ)^1591
        have hw : |(5370626941/10000000000 : ℝ)|=(5370626941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2284702063/10000000000 : ℝ)|^2103 ≤ (3551684752197/25000000000000 : ℝ)^1591
        have hw : |(-2284702063/10000000000 : ℝ)|=(2284702063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5171277427/10000000000 : ℝ)|^2103 ≤ (41824494924723/100000000000000 : ℝ)^1591
        have hw : |(5171277427/10000000000 : ℝ)|=(5171277427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s2_2 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2685313371/5000000000 : ℝ)*x 0 + (5171277603/10000000000 : ℝ)*x 1 + (-456940419/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685313371/5000000000 : ℝ)^2103 ≤ (21984381948987/50000000000000 : ℝ)^1591 := by
    have hnat : (2685313371 : ℕ)^2103*50000000000000^1591 ≤ 21984381948987^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685313371 5000000000 21984381948987 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5171277603/10000000000 : ℝ)^2103 ≤ (10456124201567/25000000000000 : ℝ)^1591 := by
    have hnat : (5171277603 : ℕ)^2103*25000000000000^1591 ≤ 10456124201567^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171277603 10000000000 10456124201567 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (456940419/2000000000 : ℝ)^2103 ≤ (2841347854361/20000000000000 : ℝ)^1591 := by
    have hnat : (456940419 : ℕ)^2103*20000000000000^1591 ≤ 2841347854361^1591*2000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456940419 2000000000 2841347854361 20000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685313371/5000000000 : ℝ), (5171277603/10000000000 : ℝ), (-456940419/2000000000 : ℝ)] ![(21984381948987/50000000000000 : ℝ), (10456124201567/25000000000000 : ℝ), (2841347854361/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685313371/5000000000 : ℝ)|^2103 ≤ (21984381948987/50000000000000 : ℝ)^1591
        have hw : |(2685313371/5000000000 : ℝ)|=(2685313371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5171277603/10000000000 : ℝ)|^2103 ≤ (10456124201567/25000000000000 : ℝ)^1591
        have hw : |(5171277603/10000000000 : ℝ)|=(5171277603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-456940419/2000000000 : ℝ)|^2103 ≤ (2841347854361/20000000000000 : ℝ)^1591
        have hw : |(-456940419/2000000000 : ℝ)|=(456940419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s2_3 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (543097867/1250000000 : ℝ)*x 0 + (805643139/2000000000 : ℝ)*x 1 + (1171389423/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543097867/1250000000 : ℝ)^2103 ≤ (33224811622641/100000000000000 : ℝ)^1591 := by
    have hnat : (543097867 : ℕ)^2103*100000000000000^1591 ≤ 33224811622641^1591*1250000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543097867 1250000000 33224811622641 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (805643139/2000000000 : ℝ)^2103 ≤ (375788929419/1250000000000 : ℝ)^1591 := by
    have hnat : (805643139 : ℕ)^2103*1250000000000^1591 ≤ 375788929419^1591*2000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805643139 2000000000 375788929419 1250000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1171389423/2500000000 : ℝ)^2103 ≤ (18356037004353/50000000000000 : ℝ)^1591 := by
    have hnat : (1171389423 : ℕ)^2103*50000000000000^1591 ≤ 18356037004353^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171389423 2500000000 18356037004353 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543097867/1250000000 : ℝ), (805643139/2000000000 : ℝ), (1171389423/2500000000 : ℝ)] ![(33224811622641/100000000000000 : ℝ), (375788929419/1250000000000 : ℝ), (18356037004353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543097867/1250000000 : ℝ)|^2103 ≤ (33224811622641/100000000000000 : ℝ)^1591
        have hw : |(543097867/1250000000 : ℝ)|=(543097867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(805643139/2000000000 : ℝ)|^2103 ≤ (375788929419/1250000000000 : ℝ)^1591
        have hw : |(805643139/2000000000 : ℝ)|=(805643139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1171389423/2500000000 : ℝ)|^2103 ≤ (18356037004353/50000000000000 : ℝ)^1591
        have hw : |(1171389423/2500000000 : ℝ)|=(1171389423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s2_4 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2116048701/10000000000 : ℝ)*x 0 + (5173403643/10000000000 : ℝ)*x 1 + (2747308917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116048701/10000000000 : ℝ)^2103 ≤ (6418639027527/50000000000000 : ℝ)^1591 := by
    have hnat : (2116048701 : ℕ)^2103*50000000000000^1591 ≤ 6418639027527^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116048701 10000000000 6418639027527 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5173403643/10000000000 : ℝ)^2103 ≤ (20923613473449/50000000000000 : ℝ)^1591 := by
    have hnat : (5173403643 : ℕ)^2103*50000000000000^1591 ≤ 20923613473449^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173403643 10000000000 20923613473449 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2747308917/5000000000 : ℝ)^2103 ≤ (45315494978389/100000000000000 : ℝ)^1591 := by
    have hnat : (2747308917 : ℕ)^2103*100000000000000^1591 ≤ 45315494978389^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747308917 5000000000 45315494978389 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2116048701/10000000000 : ℝ), (5173403643/10000000000 : ℝ), (2747308917/5000000000 : ℝ)] ![(6418639027527/50000000000000 : ℝ), (20923613473449/50000000000000 : ℝ), (45315494978389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2116048701/10000000000 : ℝ)|^2103 ≤ (6418639027527/50000000000000 : ℝ)^1591
        have hw : |(-2116048701/10000000000 : ℝ)|=(2116048701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5173403643/10000000000 : ℝ)|^2103 ≤ (20923613473449/50000000000000 : ℝ)^1591
        have hw : |(5173403643/10000000000 : ℝ)|=(5173403643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2747308917/5000000000 : ℝ)|^2103 ≤ (45315494978389/100000000000000 : ℝ)^1591
        have hw : |(2747308917/5000000000 : ℝ)|=(2747308917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s2_5 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5287626197/10000000000 : ℝ)*x 0 + (-3922723/20000000 : ℝ)*x 1 + (1373654467/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287626197/10000000000 : ℝ)^2103 ≤ (43072813007857/100000000000000 : ℝ)^1591 := by
    have hnat : (5287626197 : ℕ)^2103*100000000000000^1591 ≤ 43072813007857^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287626197 10000000000 43072813007857 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3922723/20000000 : ℝ)^2103 ≤ (11611691617617/100000000000000 : ℝ)^1591 := by
    have hnat : (3922723 : ℕ)^2103*100000000000000^1591 ≤ 11611691617617^1591*20000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3922723 20000000 11611691617617 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1373654467/2500000000 : ℝ)^2103 ≤ (45315495349033/100000000000000 : ℝ)^1591 := by
    have hnat : (1373654467 : ℕ)^2103*100000000000000^1591 ≤ 45315495349033^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373654467 2500000000 45315495349033 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287626197/10000000000 : ℝ), (-3922723/20000000 : ℝ), (1373654467/2500000000 : ℝ)] ![(43072813007857/100000000000000 : ℝ), (11611691617617/100000000000000 : ℝ), (45315495349033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287626197/10000000000 : ℝ)|^2103 ≤ (43072813007857/100000000000000 : ℝ)^1591
        have hw : |(5287626197/10000000000 : ℝ)|=(5287626197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3922723/20000000 : ℝ)|^2103 ≤ (11611691617617/100000000000000 : ℝ)^1591
        have hw : |(-3922723/20000000 : ℝ)|=(3922723/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1373654467/2500000000 : ℝ)|^2103 ≤ (45315495349033/100000000000000 : ℝ)^1591
        have hw : |(1373654467/2500000000 : ℝ)|=(1373654467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s2_6 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5287626379/10000000000 : ℝ)*x 0 + (686827239/1250000000 : ℝ)*x 1 + (-1961361189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287626379/10000000000 : ℝ)^2103 ≤ (43072814967527/100000000000000 : ℝ)^1591 := by
    have hnat : (5287626379 : ℕ)^2103*100000000000000^1591 ≤ 43072814967527^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287626379 10000000000 43072814967527 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (686827239/1250000000 : ℝ)^2103 ≤ (4531549582869/10000000000000 : ℝ)^1591 := by
    have hnat : (686827239 : ℕ)^2103*10000000000000^1591 ≤ 4531549582869^1591*1250000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686827239 1250000000 4531549582869 10000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1961361189/10000000000 : ℝ)^2103 ≤ (2902922295979/25000000000000 : ℝ)^1591 := by
    have hnat : (1961361189 : ℕ)^2103*25000000000000^1591 ≤ 2902922295979^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961361189 10000000000 2902922295979 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287626379/10000000000 : ℝ), (686827239/1250000000 : ℝ), (-1961361189/10000000000 : ℝ)] ![(43072814967527/100000000000000 : ℝ), (4531549582869/10000000000000 : ℝ), (2902922295979/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287626379/10000000000 : ℝ)|^2103 ≤ (43072814967527/100000000000000 : ℝ)^1591
        have hw : |(5287626379/10000000000 : ℝ)|=(5287626379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(686827239/1250000000 : ℝ)|^2103 ≤ (4531549582869/10000000000000 : ℝ)^1591
        have hw : |(686827239/1250000000 : ℝ)|=(686827239/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1961361189/10000000000 : ℝ)|^2103 ≤ (2902922295979/25000000000000 : ℝ)^1591
        have hw : |(-1961361189/10000000000 : ℝ)|=(1961361189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s2_7 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4344950767/10000000000 : ℝ)*x 0 + (2340631957/5000000000 : ℝ)*x 1 + (2016275063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4344950767/10000000000 : ℝ)^2103 ≤ (1038328376947/3125000000000 : ℝ)^1591 := by
    have hnat : (4344950767 : ℕ)^2103*3125000000000^1591 ≤ 1038328376947^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4344950767 10000000000 1038328376947 3125000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2340631957/5000000000 : ℝ)^2103 ≤ (2291725729681/6250000000000 : ℝ)^1591 := by
    have hnat : (2340631957 : ℕ)^2103*6250000000000^1591 ≤ 2291725729681^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2340631957 5000000000 2291725729681 6250000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2016275063/5000000000 : ℝ)^2103 ≤ (30105880252517/100000000000000 : ℝ)^1591 := by
    have hnat : (2016275063 : ℕ)^2103*100000000000000^1591 ≤ 30105880252517^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016275063 5000000000 30105880252517 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4344950767/10000000000 : ℝ), (2340631957/5000000000 : ℝ), (2016275063/5000000000 : ℝ)] ![(1038328376947/3125000000000 : ℝ), (2291725729681/6250000000000 : ℝ), (30105880252517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4344950767/10000000000 : ℝ)|^2103 ≤ (1038328376947/3125000000000 : ℝ)^1591
        have hw : |(4344950767/10000000000 : ℝ)|=(4344950767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2340631957/5000000000 : ℝ)|^2103 ≤ (2291725729681/6250000000000 : ℝ)^1591
        have hw : |(2340631957/5000000000 : ℝ)|=(2340631957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2016275063/5000000000 : ℝ)|^2103 ≤ (30105880252517/100000000000000 : ℝ)^1591
        have hw : |(2016275063/5000000000 : ℝ)|=(2016275063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1219_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6069/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1881/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4071/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6069/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6069/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6069/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6069/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6069/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6069/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6069/100000 : ℝ) ^ (8411/2048 : ℝ) ≤ (502704643265437/50000000000000000000 : ℝ) := by
    have hpowers : (6069/100000 : ℝ)^8411 ≤ (502704643265437/50000000000000000000 : ℝ)^2048 := by
      have hnat : (6069 : ℕ)^8411*50000000000000000000^2048 ≤ 502704643265437^2048*100000^8411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6069 100000 502704643265437 50000000000000000000 8411 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6069/100000 : ℝ)) (X := (502704643265437/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20097/100000 : ℝ) ^ (8411/2048 : ℝ) ≤ (3435154360074981/2500000000000000000 : ℝ) := by
    have hpowers : (20097/100000 : ℝ)^8411 ≤ (3435154360074981/2500000000000000000 : ℝ)^2048 := by
      have hnat : (20097 : ℕ)^8411*2500000000000000000^2048 ≤ 3435154360074981^2048*100000^8411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20097 100000 3435154360074981 2500000000000000000 8411 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20097/100000 : ℝ)) (X := (3435154360074981/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000502704643265437/25000000000000000000 : ℝ) ≤ (2500012240295789/2500000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (25000502704643265437/25000000000000000000 : ℝ)^2048 ≤ (2500012240295789/2500000000000000 : ℝ)^8411 := by
      have hnat : (25000502704643265437 : ℕ)^2048*2500000000000000^8411 ≤ 2500012240295789^8411*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000502704643265437 25000000000000000000 2500012240295789 2500000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500012240295789/2500000000000000 : ℝ)) (X := (25000502704643265437/25000000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50069205791844765057/50000000000000000000 : ℝ) ≤ (5001684214926489/5000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (50069205791844765057/50000000000000000000 : ℝ)^2048 ≤ (5001684214926489/5000000000000000 : ℝ)^8411 := by
      have hnat : (50069205791844765057 : ℕ)^2048*5000000000000000^8411 ≤ 5001684214926489^8411*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50069205791844765057 50000000000000000000 5001684214926489 5000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001684214926489/5000000000000000 : ℝ)) (X := (50069205791844765057/50000000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1253435154360074981/1250000000000000000 : ℝ) ≤ (25016719746307/25000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (1253435154360074981/1250000000000000000 : ℝ)^2048 ≤ (25016719746307/25000000000000 : ℝ)^8411 := by
      have hnat : (1253435154360074981 : ℕ)^2048*25000000000000^8411 ≤ 25016719746307^8411*1250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1253435154360074981 1250000000000000000 25016719746307 25000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25016719746307/25000000000000 : ℝ)) (X := (1253435154360074981/1250000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(502704643265437/50000000000000000000 : ℝ) ≤ ((1669528513294797773/1670000000000000000 : ℝ)+2*(1659734334911/701400000000000 : ℝ)*(6069/100000 : ℝ))^(8411/2048 : ℝ) := by
    rw [show (1669528513294797773/1670000000000000000 : ℝ)+2*(1659734334911/701400000000000 : ℝ)*(6069/100000 : ℝ)=(2500012240295789/2500000000000000 : ℝ) by norm_num, show 1+2*(502704643265437/50000000000000000000 : ℝ)=(25000502704643265437/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3435154360074981/2500000000000000000 : ℝ)+(502704643265437/50000000000000000000 : ℝ) ≤ ((1669528513294797773/1670000000000000000 : ℝ)+(1659734334911/701400000000000 : ℝ)*((20097/100000 : ℝ)+(6069/100000 : ℝ)))^(8411/2048 : ℝ) := by
    rw [show (1669528513294797773/1670000000000000000 : ℝ)+(1659734334911/701400000000000 : ℝ)*((20097/100000 : ℝ)+(6069/100000 : ℝ))=(5001684214926489/5000000000000000 : ℝ) by norm_num, show 1+(3435154360074981/2500000000000000000 : ℝ)+(502704643265437/50000000000000000000 : ℝ)=(50069205791844765057/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3435154360074981/2500000000000000000 : ℝ) ≤ ((1669528513294797773/1670000000000000000 : ℝ)+2*(1659734334911/701400000000000 : ℝ)*(20097/100000 : ℝ))^(8411/2048 : ℝ) := by
    rw [show (1669528513294797773/1670000000000000000 : ℝ)+2*(1659734334911/701400000000000 : ℝ)*(20097/100000 : ℝ)=(25016719746307/25000000000000 : ℝ) by norm_num, show 1+2*(3435154360074981/2500000000000000000 : ℝ)=(1253435154360074981/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1669528513294797773/1670000000000000000 : ℝ)*(X 1 0+X 2 0)+(1659734334911/701400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (6069/100000 : ℝ)) (hi := (20097/100000 : ℝ)) (c := (1669528513294797773/1670000000000000000 : ℝ)) (alpha := (1659734334911/701400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1669528513294797773/1670000000000000000 : ℝ)*(X 0 1+X 2 1)+(1659734334911/701400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (6069/100000 : ℝ)) (hi := (20097/100000 : ℝ)) (c := (1669528513294797773/1670000000000000000 : ℝ)) (alpha := (1659734334911/701400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1669528513294797773/1670000000000000000 : ℝ)*(X 0 2+X 1 2)+(1659734334911/701400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (6069/100000 : ℝ)) (hi := (20097/100000 : ℝ)) (c := (1669528513294797773/1670000000000000000 : ℝ)) (alpha := (1659734334911/701400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1057982671/5000000000 : ℝ)*X 0 0+(5496764209/10000000000 : ℝ)*X 0 1+(1034255499/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5370626941/10000000000 : ℝ)*X 1 0+(-2284702063/10000000000 : ℝ)*X 1 1+(5171277427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2685313371/5000000000 : ℝ)*X 2 0+(5171277603/10000000000 : ℝ)*X 2 1+(-456940419/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((543097867/1250000000 : ℝ)*X 0 0+(805643139/2000000000 : ℝ)*X 0 1+(1171389423/2500000000 : ℝ)*X 0 2+(543097867/1250000000 : ℝ)*X 1 0+(805643139/2000000000 : ℝ)*X 1 1+(1171389423/2500000000 : ℝ)*X 1 2+(543097867/1250000000 : ℝ)*X 2 0+(805643139/2000000000 : ℝ)*X 2 1+(1171389423/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2116048701/10000000000 : ℝ)*X 0 0+(5173403643/10000000000 : ℝ)*X 0 1+(2747308917/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287626197/10000000000 : ℝ)*X 1 0+(-3922723/20000000 : ℝ)*X 1 1+(1373654467/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287626379/10000000000 : ℝ)*X 2 0+(686827239/1250000000 : ℝ)*X 2 1+(-1961361189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4344950767/10000000000 : ℝ)*X 0 0+(2340631957/5000000000 : ℝ)*X 0 1+(2016275063/5000000000 : ℝ)*X 0 2+(4344950767/10000000000 : ℝ)*X 1 0+(2340631957/5000000000 : ℝ)*X 1 1+(2016275063/5000000000 : ℝ)*X 1 2+(4344950767/10000000000 : ℝ)*X 2 0+(2340631957/5000000000 : ℝ)*X 2 1+(2016275063/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (90766644717990385774634841/41750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (105096067/25000000000000 : ℝ)*(base19) + (33713827/12500000000000 : ℝ)*(base23) + (9890927/50000000000000 : ℝ)*(lower2) + (95885973/100000000000000 : ℝ)*(upper3) + (9309599/50000000000000 : ℝ)*(upper5) + (1148402881866639/50000000000000 : ℝ)*(major0) + (1148402881866639/50000000000000 : ℝ)*(major1) + (1148402881866639/50000000000000 : ℝ)*(major2) + (1536163227707329/50000000000000 : ℝ)*(sp0) + (384041087673471/12500000000000 : ℝ)*(sp1) + (3072328852061421/100000000000000 : ℝ)*(sp2) + (190159995242449/12500000000000 : ℝ)*(sp3) + (1333178689/50000000000000 : ℝ)*(sp4) + (2371286543/100000000000000 : ℝ)*(sp7) + (190160291653267/12500000000000 : ℝ)*(f.failure) + (768082280443009/25000000000000 : ℝ)*(f.sum) + (1060169773171/208750000000000000000000000 : ℝ)*base65 + (261877581764644947/83500000000000000000000000000000 : ℝ)*base67 + (49735043356355053/83500000000000000000000000000000 : ℝ)*base70 + (268654611645855053/83500000000000000000000000000000 : ℝ)*base72 + (700397012219/835000000000000000000000000 : ℝ)*base73 + (330397706814644947/83500000000000000000000000000000 : ℝ)*base75 + (146783246594855053/83500000000000000000000000000000 : ℝ)*base78 + (369728967199855053/83500000000000000000000000000000 : ℝ)*base80 + (7773852297/26093750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (8161357/1250000000000000000000 : ℝ)*base89 + (8161357/1250000000000000000000 : ℝ)*base91 + (8161357/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32019996962647452806251761/9132812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (105465779/10000000000000 : ℝ)*(base19) + (53764859/4000000000000 : ℝ)*(base23) + (25312139/50000000000000 : ℝ)*(upper2) + (156361861/100000000000000 : ℝ)*(upper3) + (6987637/10000000000000 : ℝ)*(upper5) + (72729668614133/3125000000000 : ℝ)*(major0) + (72729668614133/3125000000000 : ℝ)*(major1) + (72729668614133/3125000000000 : ℝ)*(major2) + (509349537/5000000000000 : ℝ)*(sp1) + (7850936843/50000000000000 : ℝ)*(sp2) + (1556592929611687/50000000000000 : ℝ)*(sp4) + (3113174617574843/100000000000000 : ℝ)*(sp5) + (778292203307053/25000000000000 : ℝ)*(sp6) + (1541512815213161/100000000000000 : ℝ)*(sp7) + (1541512815213161/100000000000000 : ℝ)*(f.failure) + (1556592929611687/50000000000000 : ℝ)*(f.sum) + (10079533621153/17535000000000000000000000000 : ℝ)*base65 + (827768288499516989/109593750000000000000000000000000 : ℝ)*base67 + (819122918905545511/109593750000000000000000000000000 : ℝ)*base70 + (815635245317204489/109593750000000000000000000000000 : ℝ)*base71 + (29548228336709/8767500000000000000000000000 : ℝ)*base73 + (515173448609579489/109593750000000000000000000000000 : ℝ)*base75 + (482533048125235739/109593750000000000000000000000000 : ℝ)*base77 + (1316179792385766989/109593750000000000000000000000000 : ℝ)*base79 + (73716901381/34248046875000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (55775369/10000000000000000000000 : ℝ)*base90 + (55775369/10000000000000000000000 : ℝ)*base92 + (55775369/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1219_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6069/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1881/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4071/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1219_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1219_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1881/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4071/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1219_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1219_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1219_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1881/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4071/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1219_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

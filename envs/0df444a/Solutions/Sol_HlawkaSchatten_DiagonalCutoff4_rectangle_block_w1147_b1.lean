-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1147_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:34:20.197238+00:00
-- url     : https://prove2.me/submissions/8f0e5b01-01a0-45be-985d-8a31f412edb7

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
theorem support_rectangle_w1147_s3_0 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2160747507/10000000000 : ℝ)*x 0 + (678583563/1250000000 : ℝ)*x 1 + (2616275123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160747507/10000000000 : ℝ)^2085 ≤ (13122678650961/100000000000000 : ℝ)^1573 := by
    have hnat : (2160747507 : ℕ)^2085*100000000000000^1573 ≤ 13122678650961^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160747507 10000000000 13122678650961 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678583563/1250000000 : ℝ)^2085 ≤ (44497738440253/100000000000000 : ℝ)^1573 := by
    have hnat : (678583563 : ℕ)^2085*100000000000000^1573 ≤ 44497738440253^1573*1250000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678583563 1250000000 44497738440253 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2616275123/5000000000 : ℝ)^2085 ≤ (21189791443353/50000000000000 : ℝ)^1573 := by
    have hnat : (2616275123 : ℕ)^2085*50000000000000^1573 ≤ 21189791443353^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616275123 5000000000 21189791443353 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2160747507/10000000000 : ℝ), (678583563/1250000000 : ℝ), (2616275123/5000000000 : ℝ)] ![(13122678650961/100000000000000 : ℝ), (44497738440253/100000000000000 : ℝ), (21189791443353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2160747507/10000000000 : ℝ)|^2085 ≤ (13122678650961/100000000000000 : ℝ)^1573
        have hw : |(-2160747507/10000000000 : ℝ)|=(2160747507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678583563/1250000000 : ℝ)|^2085 ≤ (44497738440253/100000000000000 : ℝ)^1573
        have hw : |(678583563/1250000000 : ℝ)|=(678583563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2616275123/5000000000 : ℝ)|^2085 ≤ (21189791443353/50000000000000 : ℝ)^1573
        have hw : |(2616275123/5000000000 : ℝ)|=(2616275123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s3_1 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1338418929/2500000000 : ℝ)*x 0 + (-2260985611/10000000000 : ℝ)*x 1 + (5232550073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338418929/2500000000 : ℝ)^2085 ≤ (43684793916781/100000000000000 : ℝ)^1573 := by
    have hnat : (1338418929 : ℕ)^2085*100000000000000^1573 ≤ 43684793916781^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338418929 2500000000 43684793916781 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2260985611/10000000000 : ℝ)^2085 ≤ (13935625043159/100000000000000 : ℝ)^1573 := by
    have hnat : (2260985611 : ℕ)^2085*100000000000000^1573 ≤ 13935625043159^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260985611 10000000000 13935625043159 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5232550073/10000000000 : ℝ)^2085 ≤ (1324361907171/3125000000000 : ℝ)^1573 := by
    have hnat : (5232550073 : ℕ)^2085*3125000000000^1573 ≤ 1324361907171^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232550073 10000000000 1324361907171 3125000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338418929/2500000000 : ℝ), (-2260985611/10000000000 : ℝ), (5232550073/10000000000 : ℝ)] ![(43684793916781/100000000000000 : ℝ), (13935625043159/100000000000000 : ℝ), (1324361907171/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338418929/2500000000 : ℝ)|^2085 ≤ (43684793916781/100000000000000 : ℝ)^1573
        have hw : |(1338418929/2500000000 : ℝ)|=(1338418929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2260985611/10000000000 : ℝ)|^2085 ≤ (13935625043159/100000000000000 : ℝ)^1573
        have hw : |(-2260985611/10000000000 : ℝ)|=(2260985611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5232550073/10000000000 : ℝ)|^2085 ≤ (1324361907171/3125000000000 : ℝ)^1573
        have hw : |(5232550073/10000000000 : ℝ)|=(5232550073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s3_2 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1338418949/2500000000 : ℝ)*x 0 + (5232550139/10000000000 : ℝ)*x 1 + (-1130492709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338418949/2500000000 : ℝ)^2085 ≤ (43684794782039/100000000000000 : ℝ)^1573 := by
    have hnat : (1338418949 : ℕ)^2085*100000000000000^1573 ≤ 43684794782039^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338418949 2500000000 43684794782039 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5232550139/10000000000 : ℝ)^2085 ≤ (10594895434503/25000000000000 : ℝ)^1573 := by
    have hnat : (5232550139 : ℕ)^2085*25000000000000^1573 ≤ 10594895434503^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232550139 10000000000 10594895434503 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130492709/5000000000 : ℝ)^2085 ≤ (13935623466407/100000000000000 : ℝ)^1573 := by
    have hnat : (1130492709 : ℕ)^2085*100000000000000^1573 ≤ 13935623466407^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130492709 5000000000 13935623466407 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338418949/2500000000 : ℝ), (5232550139/10000000000 : ℝ), (-1130492709/5000000000 : ℝ)] ![(43684794782039/100000000000000 : ℝ), (10594895434503/25000000000000 : ℝ), (13935623466407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338418949/2500000000 : ℝ)|^2085 ≤ (43684794782039/100000000000000 : ℝ)^1573
        have hw : |(1338418949/2500000000 : ℝ)|=(1338418949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5232550139/10000000000 : ℝ)|^2085 ≤ (10594895434503/25000000000000 : ℝ)^1573
        have hw : |(5232550139/10000000000 : ℝ)|=(5232550139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1130492709/5000000000 : ℝ)|^2085 ≤ (13935623466407/100000000000000 : ℝ)^1573
        have hw : |(-1130492709/5000000000 : ℝ)|=(1130492709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s3_3 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (17446973/40000000 : ℝ)*x 0 + (834160953/2000000000 : ℝ)*x 1 + (2280679737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17446973/40000000 : ℝ)^2085 ≤ (4161808633979/12500000000000 : ℝ)^1573 := by
    have hnat : (17446973 : ℕ)^2085*12500000000000^1573 ≤ 4161808633979^1573*40000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17446973 40000000 4161808633979 12500000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834160953/2000000000 : ℝ)^2085 ≤ (31376478705233/100000000000000 : ℝ)^1573 := by
    have hnat : (834160953 : ℕ)^2085*100000000000000^1573 ≤ 31376478705233^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834160953 2000000000 31376478705233 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2280679737/5000000000 : ℝ)^2085 ≤ (17664526105283/50000000000000 : ℝ)^1573 := by
    have hnat : (2280679737 : ℕ)^2085*50000000000000^1573 ≤ 17664526105283^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280679737 5000000000 17664526105283 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17446973/40000000 : ℝ), (834160953/2000000000 : ℝ), (2280679737/5000000000 : ℝ)] ![(4161808633979/12500000000000 : ℝ), (31376478705233/100000000000000 : ℝ), (17664526105283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17446973/40000000 : ℝ)|^2085 ≤ (4161808633979/12500000000000 : ℝ)^1573
        have hw : |(17446973/40000000 : ℝ)|=(17446973/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(834160953/2000000000 : ℝ)|^2085 ≤ (31376478705233/100000000000000 : ℝ)^1573
        have hw : |(834160953/2000000000 : ℝ)|=(834160953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2280679737/5000000000 : ℝ)|^2085 ≤ (17664526105283/50000000000000 : ℝ)^1573
        have hw : |(2280679737/5000000000 : ℝ)|=(2280679737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s3_4 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2160765349/10000000000 : ℝ)*x 0 + (2616654359/5000000000 : ℝ)*x 1 + (339244113/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160765349/10000000000 : ℝ)^2085 ≤ (13122822279231/100000000000000 : ℝ)^1573 := by
    have hnat : (2160765349 : ℕ)^2085*100000000000000^1573 ≤ 13122822279231^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160765349 10000000000 13122822279231 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2616654359/5000000000 : ℝ)^2085 ≤ (847754512473/2000000000000 : ℝ)^1573 := by
    have hnat : (2616654359 : ℕ)^2085*2000000000000^1573 ≤ 847754512473^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616654359 5000000000 847754512473 2000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339244113/625000000 : ℝ)^2085 ≤ (8897890417219/20000000000000 : ℝ)^1573 := by
    have hnat : (339244113 : ℕ)^2085*20000000000000^1573 ≤ 8897890417219^1573*625000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339244113 625000000 8897890417219 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2160765349/10000000000 : ℝ), (2616654359/5000000000 : ℝ), (339244113/625000000 : ℝ)] ![(13122822279231/100000000000000 : ℝ), (847754512473/2000000000000 : ℝ), (8897890417219/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2160765349/10000000000 : ℝ)|^2085 ≤ (13122822279231/100000000000000 : ℝ)^1573
        have hw : |(-2160765349/10000000000 : ℝ)|=(2160765349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2616654359/5000000000 : ℝ)|^2085 ≤ (847754512473/2000000000000 : ℝ)^1573
        have hw : |(2616654359/5000000000 : ℝ)|=(2616654359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339244113/625000000 : ℝ)|^2085 ≤ (8897890417219/20000000000000 : ℝ)^1573
        have hw : |(339244113/625000000 : ℝ)|=(339244113/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s3_5 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (662996481/1250000000 : ℝ)*x 0 + (-2065629807/10000000000 : ℝ)*x 1 + (5427905907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662996481/1250000000 : ℝ)^2085 ≤ (43148024597819/100000000000000 : ℝ)^1573 := by
    have hnat : (662996481 : ℕ)^2085*100000000000000^1573 ≤ 43148024597819^1573*1250000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662996481 1250000000 43148024597819 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065629807/10000000000 : ℝ)^2085 ≤ (12362522228233/100000000000000 : ℝ)^1573 := by
    have hnat : (2065629807 : ℕ)^2085*100000000000000^1573 ≤ 12362522228233^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065629807 10000000000 12362522228233 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427905907/10000000000 : ℝ)^2085 ≤ (22244726580831/50000000000000 : ℝ)^1573 := by
    have hnat : (5427905907 : ℕ)^2085*50000000000000^1573 ≤ 22244726580831^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427905907 10000000000 22244726580831 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662996481/1250000000 : ℝ), (-2065629807/10000000000 : ℝ), (5427905907/10000000000 : ℝ)] ![(43148024597819/100000000000000 : ℝ), (12362522228233/100000000000000 : ℝ), (22244726580831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662996481/1250000000 : ℝ)|^2085 ≤ (43148024597819/100000000000000 : ℝ)^1573
        have hw : |(662996481/1250000000 : ℝ)|=(662996481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2065629807/10000000000 : ℝ)|^2085 ≤ (12362522228233/100000000000000 : ℝ)^1573
        have hw : |(-2065629807/10000000000 : ℝ)|=(2065629807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427905907/10000000000 : ℝ)|^2085 ≤ (22244726580831/50000000000000 : ℝ)^1573
        have hw : |(5427905907/10000000000 : ℝ)|=(5427905907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s3_6 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (331498233/625000000 : ℝ)*x 0 + (5427906103/10000000000 : ℝ)*x 1 + (-20656297/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331498233/625000000 : ℝ)^2085 ≤ (43148023303867/100000000000000 : ℝ)^1573 := by
    have hnat : (331498233 : ℕ)^2085*100000000000000^1573 ≤ 43148023303867^1573*625000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331498233 625000000 43148023303867 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427906103/10000000000 : ℝ)^2085 ≤ (22244727645533/50000000000000 : ℝ)^1573 := by
    have hnat : (5427906103 : ℕ)^2085*50000000000000^1573 ≤ 22244727645533^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427906103 10000000000 22244727645533 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20656297/100000000 : ℝ)^2085 ≤ (3090630344853/25000000000000 : ℝ)^1573 := by
    have hnat : (20656297 : ℕ)^2085*25000000000000^1573 ≤ 3090630344853^1573*100000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20656297 100000000 3090630344853 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331498233/625000000 : ℝ), (5427906103/10000000000 : ℝ), (-20656297/100000000 : ℝ)] ![(43148023303867/100000000000000 : ℝ), (22244727645533/50000000000000 : ℝ), (3090630344853/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331498233/625000000 : ℝ)|^2085 ≤ (43148023303867/100000000000000 : ℝ)^1573
        have hw : |(331498233/625000000 : ℝ)|=(331498233/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427906103/10000000000 : ℝ)|^2085 ≤ (22244727645533/50000000000000 : ℝ)^1573
        have hw : |(5427906103/10000000000 : ℝ)|=(5427906103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-20656297/100000000 : ℝ)|^2085 ≤ (3090630344853/25000000000000 : ℝ)^1573
        have hw : |(-20656297/100000000 : ℝ)|=(20656297/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s3_7 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (436177879/1000000000 : ℝ)*x 0 + (1139962309/2500000000 : ℝ)*x 1 + (521540427/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436177879/1000000000 : ℝ)^2085 ≤ (16647414330803/50000000000000 : ℝ)^1573 := by
    have hnat : (436177879 : ℕ)^2085*50000000000000^1573 ≤ 16647414330803^1573*1000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436177879 1000000000 16647414330803 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1139962309/2500000000 : ℝ)^2085 ≤ (8828387112853/25000000000000 : ℝ)^1573 := by
    have hnat : (1139962309 : ℕ)^2085*25000000000000^1573 ≤ 8828387112853^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139962309 2500000000 8828387112853 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521540427/1250000000 : ℝ)^2085 ≤ (7847905718067/25000000000000 : ℝ)^1573 := by
    have hnat : (521540427 : ℕ)^2085*25000000000000^1573 ≤ 7847905718067^1573*1250000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521540427 1250000000 7847905718067 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436177879/1000000000 : ℝ), (1139962309/2500000000 : ℝ), (521540427/1250000000 : ℝ)] ![(16647414330803/50000000000000 : ℝ), (8828387112853/25000000000000 : ℝ), (7847905718067/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436177879/1000000000 : ℝ)|^2085 ≤ (16647414330803/50000000000000 : ℝ)^1573
        have hw : |(436177879/1000000000 : ℝ)|=(436177879/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1139962309/2500000000 : ℝ)|^2085 ≤ (8828387112853/25000000000000 : ℝ)^1573
        have hw : |(1139962309/2500000000 : ℝ)|=(1139962309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521540427/1250000000 : ℝ)|^2085 ≤ (7847905718067/25000000000000 : ℝ)^1573
        have hw : |(521540427/1250000000 : ℝ)|=(521540427/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1147_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2061/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9093/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (213/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (37/250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2061/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9093/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2061/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9093/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2061/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9093/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2061/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9093/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2061/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9093/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2061/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9093/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9093/100000 : ℝ) ^ (8339/2048 : ℝ) ≤ (5755559294840161/100000000000000000000 : ℝ) := by
    have hpowers : (9093/100000 : ℝ)^8339 ≤ (5755559294840161/100000000000000000000 : ℝ)^2048 := by
      have hnat : (9093 : ℕ)^8339*100000000000000000000^2048 ≤ 5755559294840161^2048*100000^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9093 100000 5755559294840161 100000000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9093/100000 : ℝ)) (X := (5755559294840161/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2061/12500 : ℝ) ^ (8339/2048 : ℝ) ≤ (64935518401602159/100000000000000000000 : ℝ) := by
    have hpowers : (2061/12500 : ℝ)^8339 ≤ (64935518401602159/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2061 : ℕ)^8339*100000000000000000000^2048 ≤ 64935518401602159^2048*12500^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2061 12500 64935518401602159 100000000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2061/12500 : ℝ)) (X := (64935518401602159/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005755559294840161/50000000000000000000 : ℝ) ≤ (10000282692736731/10000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (50005755559294840161/50000000000000000000 : ℝ)^2048 ≤ (10000282692736731/10000000000000000 : ℝ)^8339 := by
      have hnat : (50005755559294840161 : ℕ)^2048*10000000000000000^8339 ≤ 10000282692736731^8339*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005755559294840161 50000000000000000000 10000282692736731 10000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000282692736731/10000000000000000 : ℝ)) (X := (50005755559294840161/50000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1250883638471205529/1250000000000000000 : ℝ) ≤ (312554239394279/312500000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (1250883638471205529/1250000000000000000 : ℝ)^2048 ≤ (312554239394279/312500000000000 : ℝ)^8339 := by
      have hnat : (1250883638471205529 : ℕ)^2048*312500000000000^8339 ≤ 312554239394279^8339*1250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250883638471205529 1250000000000000000 312554239394279 312500000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312554239394279/312500000000000 : ℝ)) (X := (1250883638471205529/1250000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50064935518401602159/50000000000000000000 : ℝ) ≤ (80025509027977/80000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (50064935518401602159/50000000000000000000 : ℝ)^2048 ≤ (80025509027977/80000000000000 : ℝ)^8339 := by
      have hnat : (50064935518401602159 : ℕ)^2048*80000000000000^8339 ≤ 80025509027977^8339*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50064935518401602159 50000000000000000000 80025509027977 80000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80025509027977/80000000000000 : ℝ)) (X := (50064935518401602159/50000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5755559294840161/100000000000000000000 : ℝ) ≤ ((24641888946306287701/24650000000000000000 : ℝ)+2*(1452967880197/739500000000000 : ℝ)*(9093/100000 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (24641888946306287701/24650000000000000000 : ℝ)+2*(1452967880197/739500000000000 : ℝ)*(9093/100000 : ℝ)=(10000282692736731/10000000000000000 : ℝ) by norm_num, show 1+2*(5755559294840161/100000000000000000000 : ℝ)=(50005755559294840161/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(64935518401602159/100000000000000000000 : ℝ)+(5755559294840161/100000000000000000000 : ℝ) ≤ ((24641888946306287701/24650000000000000000 : ℝ)+(1452967880197/739500000000000 : ℝ)*((2061/12500 : ℝ)+(9093/100000 : ℝ)))^(8339/2048 : ℝ) := by
    rw [show (24641888946306287701/24650000000000000000 : ℝ)+(1452967880197/739500000000000 : ℝ)*((2061/12500 : ℝ)+(9093/100000 : ℝ))=(312554239394279/312500000000000 : ℝ) by norm_num, show 1+(64935518401602159/100000000000000000000 : ℝ)+(5755559294840161/100000000000000000000 : ℝ)=(1250883638471205529/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(64935518401602159/100000000000000000000 : ℝ) ≤ ((24641888946306287701/24650000000000000000 : ℝ)+2*(1452967880197/739500000000000 : ℝ)*(2061/12500 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (24641888946306287701/24650000000000000000 : ℝ)+2*(1452967880197/739500000000000 : ℝ)*(2061/12500 : ℝ)=(80025509027977/80000000000000 : ℝ) by norm_num, show 1+2*(64935518401602159/100000000000000000000 : ℝ)=(50064935518401602159/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24641888946306287701/24650000000000000000 : ℝ)*(X 1 0+X 2 0)+(1452967880197/739500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (9093/100000 : ℝ)) (hi := (2061/12500 : ℝ)) (c := (24641888946306287701/24650000000000000000 : ℝ)) (alpha := (1452967880197/739500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24641888946306287701/24650000000000000000 : ℝ)*(X 0 1+X 2 1)+(1452967880197/739500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (9093/100000 : ℝ)) (hi := (2061/12500 : ℝ)) (c := (24641888946306287701/24650000000000000000 : ℝ)) (alpha := (1452967880197/739500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24641888946306287701/24650000000000000000 : ℝ)*(X 0 2+X 1 2)+(1452967880197/739500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (9093/100000 : ℝ)) (hi := (2061/12500 : ℝ)) (c := (24641888946306287701/24650000000000000000 : ℝ)) (alpha := (1452967880197/739500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2160747507/10000000000 : ℝ)*X 0 0+(678583563/1250000000 : ℝ)*X 0 1+(2616275123/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338418929/2500000000 : ℝ)*X 1 0+(-2260985611/10000000000 : ℝ)*X 1 1+(5232550073/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338418949/2500000000 : ℝ)*X 2 0+(5232550139/10000000000 : ℝ)*X 2 1+(-1130492709/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((17446973/40000000 : ℝ)*X 0 0+(834160953/2000000000 : ℝ)*X 0 1+(2280679737/5000000000 : ℝ)*X 0 2+(17446973/40000000 : ℝ)*X 1 0+(834160953/2000000000 : ℝ)*X 1 1+(2280679737/5000000000 : ℝ)*X 1 2+(17446973/40000000 : ℝ)*X 2 0+(834160953/2000000000 : ℝ)*X 2 1+(2280679737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2160765349/10000000000 : ℝ)*X 0 0+(2616654359/5000000000 : ℝ)*X 0 1+(339244113/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((662996481/1250000000 : ℝ)*X 1 0+(-2065629807/10000000000 : ℝ)*X 1 1+(5427905907/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331498233/625000000 : ℝ)*X 2 0+(5427906103/10000000000 : ℝ)*X 2 1+(-20656297/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436177879/1000000000 : ℝ)*X 0 0+(1139962309/2500000000 : ℝ)*X 0 1+(521540427/1250000000 : ℝ)*X 0 2+(436177879/1000000000 : ℝ)*X 1 0+(1139962309/2500000000 : ℝ)*X 1 1+(521540427/1250000000 : ℝ)*X 1 2+(436177879/1000000000 : ℝ)*X 2 0+(1139962309/2500000000 : ℝ)*X 2 1+(521540427/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1775030863533503896416223369/616250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (917670189/100000000000000 : ℝ)*(base19) + (88317563/10000000000000 : ℝ)*(base23) + (59259207/100000000000000 : ℝ)*(lower2) + (592883/10000000000000 : ℝ)*(upper3) + (141487871/100000000000000 : ℝ)*(upper5) + (1914866878225977/50000000000000 : ℝ)*(major0) + (1914866878225977/50000000000000 : ℝ)*(major1) + (765946751290391/20000000000000 : ℝ)*(major2) + (5098975724604843/100000000000000 : ℝ)*(sp0) + (5098992382746191/100000000000000 : ℝ)*(sp1) + (20395969668963/400000000000 : ℝ)*(sp2) + (1280233990441073/50000000000000 : ℝ)*(sp3) + (17575811537/100000000000000 : ℝ)*(sp4) + (6135592889/100000000000000 : ℝ)*(sp7) + (640118529118759/25000000000000 : ℝ)*(f.failure) + (254949665020819/5000000000000 : ℝ)*(f.sum) + (172974227164127/73950000000000000000000000000 : ℝ)*base66 + (9291229976048176631/3697500000000000000000000000000000 : ℝ)*base67 + (1145600237210298909/493000000000000000000000000000000 : ℝ)*base70 + (39405989333176631/3697500000000000000000000000000000 : ℝ)*base71 + (245714418847723/73950000000000000000000000000 : ℝ)*base73 + (1728898543972701091/493000000000000000000000000000000 : ℝ)*base75 + (7691637794788891123/1232500000000000000000000000000000 : ℝ)*base78 + (14335544359056108877/1232500000000000000000000000000000 : ℝ)*base79 + (1639493177977/6162500000000000000000000000 : ℝ)*base82 + (15464483/1250000000000000000000 : ℝ)*base89 + (15464483/1250000000000000000000 : ℝ)*base91 + (2964483/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5265704815161944312287206547/616250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (826461599/50000000000000 : ℝ)*(base19) + (359463793/20000000000000 : ℝ)*(base23) + (3346299/1562500000000 : ℝ)*(upper3) + (51343383/50000000000000 : ℝ)*(lower4) + (169430021/100000000000000 : ℝ)*(upper5) + (1929823136471549/50000000000000 : ℝ)*(major0) + (1929823136471549/50000000000000 : ℝ)*(major1) + (1929823136471549/50000000000000 : ℝ)*(major2) + (1895397751/6250000000000 : ℝ)*(sp1) + (3748182379/10000000000000 : ℝ)*(sp2) + (5138819306780339/100000000000000 : ℝ)*(sp4) + (8222059723989/160000000000 : ℝ)*(sp5) + (321173751727349/6250000000000 : ℝ)*(sp6) + (322559119285089/12500000000000 : ℝ)*(sp7) + (322559119285089/12500000000000 : ℝ)*(f.failure) + (5138819306780339/100000000000000 : ℝ)*(f.sum) + (114976418593469/36975000000000000000000000000 : ℝ)*base66 + (15442012376285656547/3697500000000000000000000000000000 : ℝ)*base67 + (7505588671460656547/3697500000000000000000000000000000 : ℝ)*base69 + (276235762359343453/3697500000000000000000000000000000 : ℝ)*base72 + (181123222432169/36975000000000000000000000000 : ℝ)*base74 + (16884798629161843453/3697500000000000000000000000000000 : ℝ)*base76 + (931549366719343453/3697500000000000000000000000000000 : ℝ)*base78 + (16371597679314343453/3697500000000000000000000000000000 : ℝ)*base80 + (7392044997803/18487500000000000000000000000 : ℝ)*base81 + (2966693/625000000000000000000 : ℝ)*base89 + (2966693/625000000000000000000 : ℝ)*base91 + (2966693/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1147_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2061/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9093/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (213/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (37/250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1147_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1147_s4_0 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1081854983/5000000000 : ℝ)*x 0 + (2700827391/5000000000 : ℝ)*x 1 + (1051525169/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081854983/5000000000 : ℝ)^2085 ≤ (6573265880793/50000000000000 : ℝ)^1573 := by
    have hnat : (1081854983 : ℕ)^2085*50000000000000^1573 ≤ 6573265880793^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081854983 5000000000 6573265880793 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700827391/5000000000 : ℝ)^2085 ≤ (22102238781171/50000000000000 : ℝ)^1573 := by
    have hnat : (2700827391 : ℕ)^2085*50000000000000^1573 ≤ 22102238781171^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700827391 5000000000 22102238781171 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051525169/2000000000 : ℝ)^2085 ≤ (8529798134393/20000000000000 : ℝ)^1573 := by
    have hnat : (1051525169 : ℕ)^2085*20000000000000^1573 ≤ 8529798134393^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051525169 2000000000 8529798134393 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1081854983/5000000000 : ℝ), (2700827391/5000000000 : ℝ), (1051525169/2000000000 : ℝ)] ![(6573265880793/50000000000000 : ℝ), (22102238781171/50000000000000 : ℝ), (8529798134393/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1081854983/5000000000 : ℝ)|^2085 ≤ (6573265880793/50000000000000 : ℝ)^1573
        have hw : |(-1081854983/5000000000 : ℝ)|=(1081854983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700827391/5000000000 : ℝ)|^2085 ≤ (22102238781171/50000000000000 : ℝ)^1573
        have hw : |(2700827391/5000000000 : ℝ)|=(2700827391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051525169/2000000000 : ℝ)|^2085 ≤ (8529798134393/20000000000000 : ℝ)^1573
        have hw : |(1051525169/2000000000 : ℝ)|=(1051525169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s4_1 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673463293/5000000000 : ℝ)*x 0 + (-279612549/1250000000 : ℝ)*x 1 + (2628812881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673463293/5000000000 : ℝ)^2085 ≤ (43611812175209/100000000000000 : ℝ)^1573 := by
    have hnat : (2673463293 : ℕ)^2085*100000000000000^1573 ≤ 43611812175209^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673463293 5000000000 43611812175209 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (279612549/1250000000 : ℝ)^2085 ≤ (13739198034371/100000000000000 : ℝ)^1573 := by
    have hnat : (279612549 : ℕ)^2085*100000000000000^1573 ≤ 13739198034371^1573*1250000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279612549 1250000000 13739198034371 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2628812881/5000000000 : ℝ)^2085 ≤ (8529797955907/20000000000000 : ℝ)^1573 := by
    have hnat : (2628812881 : ℕ)^2085*20000000000000^1573 ≤ 8529797955907^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628812881 5000000000 8529797955907 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673463293/5000000000 : ℝ), (-279612549/1250000000 : ℝ), (2628812881/5000000000 : ℝ)] ![(43611812175209/100000000000000 : ℝ), (13739198034371/100000000000000 : ℝ), (8529797955907/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673463293/5000000000 : ℝ)|^2085 ≤ (43611812175209/100000000000000 : ℝ)^1573
        have hw : |(2673463293/5000000000 : ℝ)|=(2673463293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-279612549/1250000000 : ℝ)|^2085 ≤ (13739198034371/100000000000000 : ℝ)^1573
        have hw : |(-279612549/1250000000 : ℝ)|=(279612549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2628812881/5000000000 : ℝ)|^2085 ≤ (8529797955907/20000000000000 : ℝ)^1573
        have hw : |(2628812881/5000000000 : ℝ)|=(2628812881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s4_2 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267346333/500000000 : ℝ)*x 0 + (1051525167/2000000000 : ℝ)*x 1 + (-1118450099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267346333/500000000 : ℝ)^2085 ≤ (10902953243811/25000000000000 : ℝ)^1573 := by
    have hnat : (267346333 : ℕ)^2085*25000000000000^1573 ≤ 10902953243811^1573*500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267346333 500000000 10902953243811 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051525167/2000000000 : ℝ)^2085 ≤ (10662247641111/25000000000000 : ℝ)^1573 := by
    have hnat : (1051525167 : ℕ)^2085*25000000000000^1573 ≤ 10662247641111^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051525167 2000000000 10662247641111 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1118450099/5000000000 : ℝ)^2085 ≤ (2747839290993/20000000000000 : ℝ)^1573 := by
    have hnat : (1118450099 : ℕ)^2085*20000000000000^1573 ≤ 2747839290993^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118450099 5000000000 2747839290993 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267346333/500000000 : ℝ), (1051525167/2000000000 : ℝ), (-1118450099/5000000000 : ℝ)] ![(10902953243811/25000000000000 : ℝ), (10662247641111/25000000000000 : ℝ), (2747839290993/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267346333/500000000 : ℝ)|^2085 ≤ (10902953243811/25000000000000 : ℝ)^1573
        have hw : |(267346333/500000000 : ℝ)|=(267346333/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051525167/2000000000 : ℝ)|^2085 ≤ (10662247641111/25000000000000 : ℝ)^1573
        have hw : |(1051525167/2000000000 : ℝ)|=(1051525167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1118450099/5000000000 : ℝ)|^2085 ≤ (2747839290993/20000000000000 : ℝ)^1573
        have hw : |(-1118450099/5000000000 : ℝ)|=(1118450099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s4_3 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (272719471/625000000 : ℝ)*x 0 + (4222441917/10000000000 : ℝ)*x 1 + (2254632199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272719471/625000000 : ℝ)^2085 ≤ (33312361549837/100000000000000 : ℝ)^1573 := by
    have hnat : (272719471 : ℕ)^2085*100000000000000^1573 ≤ 33312361549837^1573*625000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272719471 625000000 33312361549837 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4222441917/10000000000 : ℝ)^2085 ≤ (7973103643129/25000000000000 : ℝ)^1573 := by
    have hnat : (4222441917 : ℕ)^2085*25000000000000^1573 ≤ 7973103643129^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222441917 10000000000 7973103643129 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254632199/5000000000 : ℝ)^2085 ≤ (34795223865037/100000000000000 : ℝ)^1573 := by
    have hnat : (2254632199 : ℕ)^2085*100000000000000^1573 ≤ 34795223865037^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254632199 5000000000 34795223865037 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272719471/625000000 : ℝ), (4222441917/10000000000 : ℝ), (2254632199/5000000000 : ℝ)] ![(33312361549837/100000000000000 : ℝ), (7973103643129/25000000000000 : ℝ), (34795223865037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272719471/625000000 : ℝ)|^2085 ≤ (33312361549837/100000000000000 : ℝ)^1573
        have hw : |(272719471/625000000 : ℝ)|=(272719471/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4222441917/10000000000 : ℝ)|^2085 ≤ (7973103643129/25000000000000 : ℝ)^1573
        have hw : |(4222441917/10000000000 : ℝ)|=(4222441917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254632199/5000000000 : ℝ)|^2085 ≤ (34795223865037/100000000000000 : ℝ)^1573
        have hw : |(2254632199/5000000000 : ℝ)|=(2254632199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s4_4 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-540929173/2500000000 : ℝ)*x 0 + (5258036109/10000000000 : ℝ)*x 1 + (2700621553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540929173/2500000000 : ℝ)^2085 ≤ (1643323241257/12500000000000 : ℝ)^1573 := by
    have hnat : (540929173 : ℕ)^2085*12500000000000^1573 ≤ 1643323241257^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540929173 2500000000 1643323241257 12500000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258036109/10000000000 : ℝ)^2085 ≤ (21326700979629/50000000000000 : ℝ)^1573 := by
    have hnat : (5258036109 : ℕ)^2085*50000000000000^1573 ≤ 21326700979629^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258036109 10000000000 21326700979629 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700621553/5000000000 : ℝ)^2085 ≤ (4420001209481/10000000000000 : ℝ)^1573 := by
    have hnat : (2700621553 : ℕ)^2085*10000000000000^1573 ≤ 4420001209481^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700621553 5000000000 4420001209481 10000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-540929173/2500000000 : ℝ), (5258036109/10000000000 : ℝ), (2700621553/5000000000 : ℝ)] ![(1643323241257/12500000000000 : ℝ), (21326700979629/50000000000000 : ℝ), (4420001209481/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-540929173/2500000000 : ℝ)|^2085 ≤ (1643323241257/12500000000000 : ℝ)^1573
        have hw : |(-540929173/2500000000 : ℝ)|=(540929173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258036109/10000000000 : ℝ)|^2085 ≤ (21326700979629/50000000000000 : ℝ)^1573
        have hw : |(5258036109/10000000000 : ℝ)|=(5258036109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700621553/5000000000 : ℝ)|^2085 ≤ (4420001209481/10000000000000 : ℝ)^1573
        have hw : |(2700621553/5000000000 : ℝ)|=(2700621553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s4_5 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (663803047/1250000000 : ℝ)*x 0 + (-2093283537/10000000000 : ℝ)*x 1 + (2700621521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663803047/1250000000 : ℝ)^2085 ≤ (21608807784321/50000000000000 : ℝ)^1573 := by
    have hnat : (663803047 : ℕ)^2085*50000000000000^1573 ≤ 21608807784321^1573*1250000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663803047 1250000000 21608807784321 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2093283537/10000000000 : ℝ)^2085 ≤ (2516474602911/20000000000000 : ℝ)^1573 := by
    have hnat : (2093283537 : ℕ)^2085*20000000000000^1573 ≤ 2516474602911^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093283537 10000000000 2516474602911 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700621521/5000000000 : ℝ)^2085 ≤ (1381250356269/3125000000000 : ℝ)^1573 := by
    have hnat : (2700621521 : ℕ)^2085*3125000000000^1573 ≤ 1381250356269^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700621521 5000000000 1381250356269 3125000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663803047/1250000000 : ℝ), (-2093283537/10000000000 : ℝ), (2700621521/5000000000 : ℝ)] ![(21608807784321/50000000000000 : ℝ), (2516474602911/20000000000000 : ℝ), (1381250356269/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663803047/1250000000 : ℝ)|^2085 ≤ (21608807784321/50000000000000 : ℝ)^1573
        have hw : |(663803047/1250000000 : ℝ)|=(663803047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2093283537/10000000000 : ℝ)|^2085 ≤ (2516474602911/20000000000000 : ℝ)^1573
        have hw : |(-2093283537/10000000000 : ℝ)|=(2093283537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700621521/5000000000 : ℝ)|^2085 ≤ (1381250356269/3125000000000 : ℝ)^1573
        have hw : |(2700621521/5000000000 : ℝ)|=(2700621521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s4_6 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (265521209/500000000 : ℝ)*x 0 + (5401243593/10000000000 : ℝ)*x 1 + (-2093283051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265521209/500000000 : ℝ)^2085 ≤ (864352269087/2000000000000 : ℝ)^1573 := by
    have hnat : (265521209 : ℕ)^2085*2000000000000^1573 ≤ 864352269087^1573*500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265521209 500000000 864352269087 2000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401243593/10000000000 : ℝ)^2085 ≤ (8840003475451/20000000000000 : ℝ)^1573 := by
    have hnat : (5401243593 : ℕ)^2085*20000000000000^1573 ≤ 8840003475451^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401243593 10000000000 8840003475451 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2093283051/10000000000 : ℝ)^2085 ≤ (12582369142441/100000000000000 : ℝ)^1573 := by
    have hnat : (2093283051 : ℕ)^2085*100000000000000^1573 ≤ 12582369142441^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093283051 10000000000 12582369142441 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265521209/500000000 : ℝ), (5401243593/10000000000 : ℝ), (-2093283051/10000000000 : ℝ)] ![(864352269087/2000000000000 : ℝ), (8840003475451/20000000000000 : ℝ), (12582369142441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265521209/500000000 : ℝ)|^2085 ≤ (864352269087/2000000000000 : ℝ)^1573
        have hw : |(265521209/500000000 : ℝ)|=(265521209/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401243593/10000000000 : ℝ)|^2085 ≤ (8840003475451/20000000000000 : ℝ)^1573
        have hw : |(5401243593/10000000000 : ℝ)|=(5401243593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2093283051/10000000000 : ℝ)|^2085 ≤ (12582369142441/100000000000000 : ℝ)^1573
        have hw : |(-2093283051/10000000000 : ℝ)|=(2093283051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s4_7 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4363525653/10000000000 : ℝ)*x 0 + (4508448887/10000000000 : ℝ)*x 1 + (4223260741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363525653/10000000000 : ℝ)^2085 ≤ (16656252201403/50000000000000 : ℝ)^1573 := by
    have hnat : (4363525653 : ℕ)^2085*50000000000000^1573 ≤ 16656252201403^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363525653 10000000000 16656252201403 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508448887/10000000000 : ℝ)^2085 ≤ (17393441526723/50000000000000 : ℝ)^1573 := by
    have hnat : (4508448887 : ℕ)^2085*50000000000000^1573 ≤ 17393441526723^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508448887 10000000000 17393441526723 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4223260741/10000000000 : ℝ)^2085 ≤ (7975153130899/25000000000000 : ℝ)^1573 := by
    have hnat : (4223260741 : ℕ)^2085*25000000000000^1573 ≤ 7975153130899^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223260741 10000000000 7975153130899 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363525653/10000000000 : ℝ), (4508448887/10000000000 : ℝ), (4223260741/10000000000 : ℝ)] ![(16656252201403/50000000000000 : ℝ), (17393441526723/50000000000000 : ℝ), (7975153130899/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363525653/10000000000 : ℝ)|^2085 ≤ (16656252201403/50000000000000 : ℝ)^1573
        have hw : |(4363525653/10000000000 : ℝ)|=(4363525653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508448887/10000000000 : ℝ)|^2085 ≤ (17393441526723/50000000000000 : ℝ)^1573
        have hw : |(4508448887/10000000000 : ℝ)|=(4508448887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4223260741/10000000000 : ℝ)|^2085 ≤ (7975153130899/25000000000000 : ℝ)^1573
        have hw : |(4223260741/10000000000 : ℝ)|=(4223260741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1147_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (37/250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (213/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (2237/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (37/250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (213/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (37/250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (213/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (37/250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (213/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (37/250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (213/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (37/250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (213/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (37/250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (213/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (213/2000 : ℝ) ^ (8339/2048 : ℝ) ≤ (2190857674339441/20000000000000000000 : ℝ) := by
    have hpowers : (213/2000 : ℝ)^8339 ≤ (2190857674339441/20000000000000000000 : ℝ)^2048 := by
      have hnat : (213 : ℕ)^8339*20000000000000000000^2048 ≤ 2190857674339441^2048*2000^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        213 2000 2190857674339441 20000000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (213/2000 : ℝ)) (X := (2190857674339441/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (37/250 : ℝ) ^ (8339/2048 : ℝ) ≤ (20915124582855421/50000000000000000000 : ℝ) := by
    have hpowers : (37/250 : ℝ)^8339 ≤ (20915124582855421/50000000000000000000 : ℝ)^2048 := by
      have hnat : (37 : ℕ)^8339*50000000000000000000^2048 ≤ 20915124582855421^2048*250^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37 250 20915124582855421 50000000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37/250 : ℝ)) (X := (20915124582855421/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002190857674339441/10000000000000000000 : ℝ) ≤ (15625840648191/15625000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (10002190857674339441/10000000000000000000 : ℝ)^2048 ≤ (15625840648191/15625000000000 : ℝ)^8339 := by
      have hnat : (10002190857674339441 : ℕ)^2048*15625000000000^8339 ≤ 15625840648191^8339*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002190857674339441 10000000000000000000 15625840648191 15625000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (15625840648191/15625000000000 : ℝ)) (X := (10002190857674339441/10000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052784537537408047/100000000000000000000 : ℝ) ≤ (10001296093245117/10000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (100052784537537408047/100000000000000000000 : ℝ)^2048 ≤ (10001296093245117/10000000000000000 : ℝ)^8339 := by
      have hnat : (100052784537537408047 : ℕ)^2048*10000000000000000^8339 ≤ 10001296093245117^8339*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052784537537408047 100000000000000000000 10001296093245117 10000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001296093245117/10000000000000000 : ℝ)) (X := (100052784537537408047/100000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25020915124582855421/25000000000000000000 : ℝ) ≤ (5001027085823997/5000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (25020915124582855421/25000000000000000000 : ℝ)^2048 ≤ (5001027085823997/5000000000000000 : ℝ)^8339 := by
      have hnat : (25020915124582855421 : ℕ)^2048*5000000000000000^8339 ≤ 5001027085823997^8339*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25020915124582855421 25000000000000000000 5001027085823997 5000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001027085823997/5000000000000000 : ℝ)) (X := (25020915124582855421/25000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2190857674339441/20000000000000000000 : ℝ) ≤ ((414860856916140159/415000000000000000 : ℝ)+2*(758078402877/415000000000000 : ℝ)*(213/2000 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (414860856916140159/415000000000000000 : ℝ)+2*(758078402877/415000000000000 : ℝ)*(213/2000 : ℝ)=(15625840648191/15625000000000 : ℝ) by norm_num, show 1+2*(2190857674339441/20000000000000000000 : ℝ)=(10002190857674339441/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20915124582855421/50000000000000000000 : ℝ)+(2190857674339441/20000000000000000000 : ℝ) ≤ ((414860856916140159/415000000000000000 : ℝ)+(758078402877/415000000000000 : ℝ)*((37/250 : ℝ)+(213/2000 : ℝ)))^(8339/2048 : ℝ) := by
    rw [show (414860856916140159/415000000000000000 : ℝ)+(758078402877/415000000000000 : ℝ)*((37/250 : ℝ)+(213/2000 : ℝ))=(10001296093245117/10000000000000000 : ℝ) by norm_num, show 1+(20915124582855421/50000000000000000000 : ℝ)+(2190857674339441/20000000000000000000 : ℝ)=(100052784537537408047/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20915124582855421/50000000000000000000 : ℝ) ≤ ((414860856916140159/415000000000000000 : ℝ)+2*(758078402877/415000000000000 : ℝ)*(37/250 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (414860856916140159/415000000000000000 : ℝ)+2*(758078402877/415000000000000 : ℝ)*(37/250 : ℝ)=(5001027085823997/5000000000000000 : ℝ) by norm_num, show 1+2*(20915124582855421/50000000000000000000 : ℝ)=(25020915124582855421/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (414860856916140159/415000000000000000 : ℝ)*(X 1 0+X 2 0)+(758078402877/415000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (213/2000 : ℝ)) (hi := (37/250 : ℝ)) (c := (414860856916140159/415000000000000000 : ℝ)) (alpha := (758078402877/415000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (414860856916140159/415000000000000000 : ℝ)*(X 0 1+X 2 1)+(758078402877/415000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (213/2000 : ℝ)) (hi := (37/250 : ℝ)) (c := (414860856916140159/415000000000000000 : ℝ)) (alpha := (758078402877/415000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (414860856916140159/415000000000000000 : ℝ)*(X 0 2+X 1 2)+(758078402877/415000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (213/2000 : ℝ)) (hi := (37/250 : ℝ)) (c := (414860856916140159/415000000000000000 : ℝ)) (alpha := (758078402877/415000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1081854983/5000000000 : ℝ)*X 0 0+(2700827391/5000000000 : ℝ)*X 0 1+(1051525169/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673463293/5000000000 : ℝ)*X 1 0+(-279612549/1250000000 : ℝ)*X 1 1+(2628812881/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267346333/500000000 : ℝ)*X 2 0+(1051525167/2000000000 : ℝ)*X 2 1+(-1118450099/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((272719471/625000000 : ℝ)*X 0 0+(4222441917/10000000000 : ℝ)*X 0 1+(2254632199/5000000000 : ℝ)*X 0 2+(272719471/625000000 : ℝ)*X 1 0+(4222441917/10000000000 : ℝ)*X 1 1+(2254632199/5000000000 : ℝ)*X 1 2+(272719471/625000000 : ℝ)*X 2 0+(4222441917/10000000000 : ℝ)*X 2 1+(2254632199/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-540929173/2500000000 : ℝ)*X 0 0+(5258036109/10000000000 : ℝ)*X 0 1+(2700621553/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663803047/1250000000 : ℝ)*X 1 0+(-2093283537/10000000000 : ℝ)*X 1 1+(2700621521/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265521209/500000000 : ℝ)*X 2 0+(5401243593/10000000000 : ℝ)*X 2 1+(-2093283051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363525653/10000000000 : ℝ)*X 0 0+(4508448887/10000000000 : ℝ)*X 0 1+(4223260741/10000000000 : ℝ)*X 0 2+(4363525653/10000000000 : ℝ)*X 1 0+(4508448887/10000000000 : ℝ)*X 1 1+(4223260741/10000000000 : ℝ)*X 1 2+(4363525653/10000000000 : ℝ)*X 2 0+(4508448887/10000000000 : ℝ)*X 2 1+(4223260741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19966247862341544156549/4150000000000000000000000000 : ℝ) := by norm_num
    linear_combination (527134629/50000000000000 : ℝ)*(base19) + (988214187/100000000000000 : ℝ)*(base23) + (90581959/100000000000000 : ℝ)*(lower2) + (138925389/100000000000000 : ℝ)*(upper5) + (1042960288970557/20000000000000 : ℝ)*(major0) + (1042960288970557/20000000000000 : ℝ)*(major1) + (2607400722426393/50000000000000 : ℝ)*(major2) + (1388614309808763/20000000000000 : ℝ)*(sp0) + (6943101295124023/100000000000000 : ℝ)*(sp1) + (6943102425179877/100000000000000 : ℝ)*(sp2) + (54476386797593/1562500000000 : ℝ)*(sp3) + (127457401/400000000000 : ℝ)*(sp4) + (1064000783/100000000000000 : ℝ)*(sp5) + (2640223519/25000000000000 : ℝ)*(sp7) + (871624828985007/25000000000000 : ℝ)*(f.failure) + (433943963337129/6250000000000 : ℝ)*(f.sum) + (256328974012767/41500000000000000000000000000 : ℝ)*base65 + (22022549191437037/8300000000000000000000000000000 : ℝ)*base68 + (141568688250211013/20750000000000000000000000000000 : ℝ)*base70 + (77985978214437037/8300000000000000000000000000000 : ℝ)*base72 + (30218867604267/41500000000000000000000000000 : ℝ)*base73 + (430967236582038987/20750000000000000000000000000000 : ℝ)*base75 + (48399566952787563/8300000000000000000000000000000 : ℝ)*base77 + (138083299893487563/8300000000000000000000000000000 : ℝ)*base79 + (4256505093589/4150000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (555541/1250000000000000000000 : ℝ)*base90 + (555541/1250000000000000000000 : ℝ)*base92 + (13055541/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12229356998626979341375359/1037500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (125043717/25000000000000 : ℝ)*(base19) + (13225749/10000000000000 : ℝ)*(base23) + (26792063/10000000000000 : ℝ)*(lower2) + (1447873/781250000000 : ℝ)*(upper3) + (63346769/50000000000000 : ℝ)*(lower4) + (262234360457083/5000000000000 : ℝ)*(major0) + (262234360457083/5000000000000 : ℝ)*(major1) + (5244687209141661/100000000000000 : ℝ)*(major2) + (4531860047/20000000000000 : ℝ)*(sp2) + (4706225291/50000000000000 : ℝ)*(sp3) + (6982893757549117/100000000000000 : ℝ)*(sp4) + (6982893257374249/100000000000000 : ℝ)*(sp5) + (6982870965991391/100000000000000 : ℝ)*(sp6) + (1753235427686271/50000000000000 : ℝ)*(sp7) + (1753240133911563/50000000000000 : ℝ)*(f.failure) + (6982893757549117/100000000000000 : ℝ)*(f.sum) + (343893391583517/41500000000000000000000000000 : ℝ)*base65 + (2933272836843953/2075000000000000000000000000000 : ℝ)*base68 + (268601955727884099/41500000000000000000000000000000 : ℝ)*base69 + (1870652413581047/2075000000000000000000000000000 : ℝ)*base71 + (186787056512017/41500000000000000000000000000 : ℝ)*base73 + (310264448596115901/41500000000000000000000000000000 : ℝ)*base76 + (22043858842237197/2075000000000000000000000000000 : ℝ)*base77 + (14536815572887197/2075000000000000000000000000000 : ℝ)*base79 + (9921614422557/2075000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (40620631/2500000000000000000000 : ℝ)*base89 + (40620631/2500000000000000000000 : ℝ)*base91 + (15620631/2500000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1147_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (37/250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (213/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2237/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1147_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1147_s5_0 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-135271067/625000000 : ℝ)*x 0 + (5394782673/10000000000 : ℝ)*x 1 + (5264086207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135271067/625000000 : ℝ)^2085 ≤ (6575791227027/50000000000000 : ℝ)^1573 := by
    have hnat : (135271067 : ℕ)^2085*50000000000000^1573 ≤ 6575791227027^1573*625000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135271067 625000000 6575791227027 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394782673/10000000000 : ℝ)^2085 ≤ (2758121875633/6250000000000 : ℝ)^1573 := by
    have hnat : (5394782673 : ℕ)^2085*6250000000000^1573 ≤ 2758121875633^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394782673 10000000000 2758121875633 6250000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264086207/10000000000 : ℝ)^2085 ≤ (21359233758403/50000000000000 : ℝ)^1573 := by
    have hnat : (5264086207 : ℕ)^2085*50000000000000^1573 ≤ 21359233758403^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264086207 10000000000 21359233758403 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-135271067/625000000 : ℝ), (5394782673/10000000000 : ℝ), (5264086207/10000000000 : ℝ)] ![(6575791227027/50000000000000 : ℝ), (2758121875633/6250000000000 : ℝ), (21359233758403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-135271067/625000000 : ℝ)|^2085 ≤ (6575791227027/50000000000000 : ℝ)^1573
        have hw : |(-135271067/625000000 : ℝ)|=(135271067/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394782673/10000000000 : ℝ)|^2085 ≤ (2758121875633/6250000000000 : ℝ)^1573
        have hw : |(5394782673/10000000000 : ℝ)|=(5394782673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264086207/10000000000 : ℝ)|^2085 ≤ (21359233758403/50000000000000 : ℝ)^1573
        have hw : |(5264086207/10000000000 : ℝ)|=(5264086207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s5_1 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336300491/2500000000 : ℝ)*x 0 + (-1115326801/5000000000 : ℝ)*x 1 + (1316021559/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336300491/2500000000 : ℝ)^2085 ≤ (43593167776973/100000000000000 : ℝ)^1573 := by
    have hnat : (1336300491 : ℕ)^2085*100000000000000^1573 ≤ 43593167776973^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336300491 2500000000 43593167776973 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115326801/5000000000 : ℝ)^2085 ≤ (684418218421/5000000000000 : ℝ)^1573 := by
    have hnat : (1115326801 : ℕ)^2085*5000000000000^1573 ≤ 684418218421^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115326801 5000000000 684418218421 5000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316021559/2500000000 : ℝ)^2085 ≤ (5339808478593/12500000000000 : ℝ)^1573 := by
    have hnat : (1316021559 : ℕ)^2085*12500000000000^1573 ≤ 5339808478593^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316021559 2500000000 5339808478593 12500000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336300491/2500000000 : ℝ), (-1115326801/5000000000 : ℝ), (1316021559/2500000000 : ℝ)] ![(43593167776973/100000000000000 : ℝ), (684418218421/5000000000000 : ℝ), (5339808478593/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336300491/2500000000 : ℝ)|^2085 ≤ (43593167776973/100000000000000 : ℝ)^1573
        have hw : |(1336300491/2500000000 : ℝ)|=(1336300491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1115326801/5000000000 : ℝ)|^2085 ≤ (684418218421/5000000000000 : ℝ)^1573
        have hw : |(-1115326801/5000000000 : ℝ)|=(1115326801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316021559/2500000000 : ℝ)|^2085 ≤ (5339808478593/12500000000000 : ℝ)^1573
        have hw : |(1316021559/2500000000 : ℝ)|=(1316021559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s5_2 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345201859/10000000000 : ℝ)*x 0 + (2632043177/5000000000 : ℝ)*x 1 + (-1115326793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345201859/10000000000 : ℝ)^2085 ≤ (10898291660477/25000000000000 : ℝ)^1573 := by
    have hnat : (5345201859 : ℕ)^2085*25000000000000^1573 ≤ 10898291660477^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345201859 10000000000 10898291660477 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632043177/5000000000 : ℝ)^2085 ≤ (5339808637251/12500000000000 : ℝ)^1573 := by
    have hnat : (2632043177 : ℕ)^2085*12500000000000^1573 ≤ 5339808637251^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632043177 5000000000 5339808637251 12500000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1115326793/5000000000 : ℝ)^2085 ≤ (6844182119139/50000000000000 : ℝ)^1573 := by
    have hnat : (1115326793 : ℕ)^2085*50000000000000^1573 ≤ 6844182119139^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115326793 5000000000 6844182119139 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345201859/10000000000 : ℝ), (2632043177/5000000000 : ℝ), (-1115326793/5000000000 : ℝ)] ![(10898291660477/25000000000000 : ℝ), (5339808637251/12500000000000 : ℝ), (6844182119139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345201859/10000000000 : ℝ)|^2085 ≤ (10898291660477/25000000000000 : ℝ)^1573
        have hw : |(5345201859/10000000000 : ℝ)|=(5345201859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632043177/5000000000 : ℝ)|^2085 ≤ (5339808637251/12500000000000 : ℝ)^1573
        have hw : |(2632043177/5000000000 : ℝ)|=(2632043177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1115326793/5000000000 : ℝ)|^2085 ≤ (6844182119139/50000000000000 : ℝ)^1573
        have hw : |(-1115326793/5000000000 : ℝ)|=(1115326793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s5_3 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2181938617/5000000000 : ℝ)*x 0 + (4235669779/10000000000 : ℝ)*x 1 + (2247970837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181938617/5000000000 : ℝ)^2085 ≤ (16658031087673/50000000000000 : ℝ)^1573 := by
    have hnat : (2181938617 : ℕ)^2085*50000000000000^1573 ≤ 16658031087673^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181938617 5000000000 16658031087673 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4235669779/10000000000 : ℝ)^2085 ≤ (32024913364613/100000000000000 : ℝ)^1573 := by
    have hnat : (4235669779 : ℕ)^2085*100000000000000^1573 ≤ 32024913364613^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235669779 10000000000 32024913364613 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247970837/5000000000 : ℝ)^2085 ≤ (34659024435803/100000000000000 : ℝ)^1573 := by
    have hnat : (2247970837 : ℕ)^2085*100000000000000^1573 ≤ 34659024435803^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247970837 5000000000 34659024435803 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181938617/5000000000 : ℝ), (4235669779/10000000000 : ℝ), (2247970837/5000000000 : ℝ)] ![(16658031087673/50000000000000 : ℝ), (32024913364613/100000000000000 : ℝ), (34659024435803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181938617/5000000000 : ℝ)|^2085 ≤ (16658031087673/50000000000000 : ℝ)^1573
        have hw : |(2181938617/5000000000 : ℝ)|=(2181938617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4235669779/10000000000 : ℝ)|^2085 ≤ (32024913364613/100000000000000 : ℝ)^1573
        have hw : |(4235669779/10000000000 : ℝ)|=(4235669779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247970837/5000000000 : ℝ)|^2085 ≤ (34659024435803/100000000000000 : ℝ)^1573
        have hw : |(2247970837/5000000000 : ℝ)|=(2247970837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s5_4 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1082171087/5000000000 : ℝ)*x 0 + (5264424149/10000000000 : ℝ)*x 1 + (5394443621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082171087/5000000000 : ℝ)^2085 ≤ (13151623547359/100000000000000 : ℝ)^1573 := by
    have hnat : (1082171087 : ℕ)^2085*100000000000000^1573 ≤ 13151623547359^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082171087 5000000000 13151623547359 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264424149/10000000000 : ℝ)^2085 ≤ (42722102619761/100000000000000 : ℝ)^1573 := by
    have hnat : (5264424149 : ℕ)^2085*100000000000000^1573 ≤ 42722102619761^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264424149 10000000000 42722102619761 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394443621/10000000000 : ℝ)^2085 ≤ (344736514171/781250000000 : ℝ)^1573 := by
    have hnat : (5394443621 : ℕ)^2085*781250000000^1573 ≤ 344736514171^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394443621 10000000000 344736514171 781250000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1082171087/5000000000 : ℝ), (5264424149/10000000000 : ℝ), (5394443621/10000000000 : ℝ)] ![(13151623547359/100000000000000 : ℝ), (42722102619761/100000000000000 : ℝ), (344736514171/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1082171087/5000000000 : ℝ)|^2085 ≤ (13151623547359/100000000000000 : ℝ)^1573
        have hw : |(-1082171087/5000000000 : ℝ)|=(1082171087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264424149/10000000000 : ℝ)|^2085 ≤ (42722102619761/100000000000000 : ℝ)^1573
        have hw : |(5264424149/10000000000 : ℝ)|=(5264424149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394443621/10000000000 : ℝ)|^2085 ≤ (344736514171/781250000000 : ℝ)^1573
        have hw : |(5394443621/10000000000 : ℝ)|=(5394443621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s5_5 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312077863/10000000000 : ℝ)*x 0 + (-1050147907/5000000000 : ℝ)*x 1 + (5394443689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312077863/10000000000 : ℝ)^2085 ≤ (43235452974751/100000000000000 : ℝ)^1573 := by
    have hnat : (5312077863 : ℕ)^2085*100000000000000^1573 ≤ 43235452974751^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312077863 10000000000 43235452974751 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050147907/5000000000 : ℝ)^2085 ≤ (12638272450497/100000000000000 : ℝ)^1573 := by
    have hnat : (1050147907 : ℕ)^2085*100000000000000^1573 ≤ 12638272450497^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050147907 5000000000 12638272450497 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394443689/10000000000 : ℝ)^2085 ≤ (1765050982047/4000000000000 : ℝ)^1573 := by
    have hnat : (5394443689 : ℕ)^2085*4000000000000^1573 ≤ 1765050982047^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394443689 10000000000 1765050982047 4000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312077863/10000000000 : ℝ), (-1050147907/5000000000 : ℝ), (5394443689/10000000000 : ℝ)] ![(43235452974751/100000000000000 : ℝ), (12638272450497/100000000000000 : ℝ), (1765050982047/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312077863/10000000000 : ℝ)|^2085 ≤ (43235452974751/100000000000000 : ℝ)^1573
        have hw : |(5312077863/10000000000 : ℝ)|=(5312077863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1050147907/5000000000 : ℝ)|^2085 ≤ (12638272450497/100000000000000 : ℝ)^1573
        have hw : |(-1050147907/5000000000 : ℝ)|=(1050147907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394443689/10000000000 : ℝ)|^2085 ≤ (1765050982047/4000000000000 : ℝ)^1573
        have hw : |(5394443689/10000000000 : ℝ)|=(5394443689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s5_6 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328019389/2500000000 : ℝ)*x 0 + (53944439/100000000 : ℝ)*x 1 + (-420059189/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328019389/2500000000 : ℝ)^2085 ≤ (43235449662743/100000000000000 : ℝ)^1573 := by
    have hnat : (1328019389 : ℕ)^2085*100000000000000^1573 ≤ 43235449662743^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328019389 2500000000 43235449662743 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53944439/100000000 : ℝ)^2085 ≤ (8825255367787/20000000000000 : ℝ)^1573 := by
    have hnat : (53944439 : ℕ)^2085*20000000000000^1573 ≤ 8825255367787^1573*100000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53944439 100000000 8825255367787 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420059189/2000000000 : ℝ)^2085 ≤ (1579784186919/12500000000000 : ℝ)^1573 := by
    have hnat : (420059189 : ℕ)^2085*12500000000000^1573 ≤ 1579784186919^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420059189 2000000000 1579784186919 12500000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328019389/2500000000 : ℝ), (53944439/100000000 : ℝ), (-420059189/2000000000 : ℝ)] ![(43235449662743/100000000000000 : ℝ), (8825255367787/20000000000000 : ℝ), (1579784186919/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328019389/2500000000 : ℝ)|^2085 ≤ (43235449662743/100000000000000 : ℝ)^1573
        have hw : |(1328019389/2500000000 : ℝ)|=(1328019389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53944439/100000000 : ℝ)|^2085 ≤ (8825255367787/20000000000000 : ℝ)^1573
        have hw : |(53944439/100000000 : ℝ)|=(53944439/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-420059189/2000000000 : ℝ)|^2085 ≤ (1579784186919/12500000000000 : ℝ)^1573
        have hw : |(-420059189/2000000000 : ℝ)|=(420059189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s5_7 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (174555517/400000000 : ℝ)*x 0 + (899053843/2000000000 : ℝ)*x 1 + (4236344589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174555517/400000000 : ℝ)^2085 ≤ (1665808518141/5000000000000 : ℝ)^1573 := by
    have hnat : (174555517 : ℕ)^2085*5000000000000^1573 ≤ 1665808518141^1573*400000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174555517 400000000 1665808518141 5000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899053843/2000000000 : ℝ)^2085 ≤ (34652153304609/100000000000000 : ℝ)^1573 := by
    have hnat : (899053843 : ℕ)^2085*100000000000000^1573 ≤ 34652153304609^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899053843 2000000000 34652153304609 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4236344589/10000000000 : ℝ)^2085 ≤ (16015838155741/50000000000000 : ℝ)^1573 := by
    have hnat : (4236344589 : ℕ)^2085*50000000000000^1573 ≤ 16015838155741^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236344589 10000000000 16015838155741 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174555517/400000000 : ℝ), (899053843/2000000000 : ℝ), (4236344589/10000000000 : ℝ)] ![(1665808518141/5000000000000 : ℝ), (34652153304609/100000000000000 : ℝ), (16015838155741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174555517/400000000 : ℝ)|^2085 ≤ (1665808518141/5000000000000 : ℝ)^1573
        have hw : |(174555517/400000000 : ℝ)|=(174555517/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899053843/2000000000 : ℝ)|^2085 ≤ (34652153304609/100000000000000 : ℝ)^1573
        have hw : |(899053843/2000000000 : ℝ)|=(899053843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4236344589/10000000000 : ℝ)|^2085 ≤ (16015838155741/50000000000000 : ℝ)^1573
        have hw : |(4236344589/10000000000 : ℝ)|=(4236344589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1147_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2237/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11323/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14091/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2237/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2237/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2237/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2237/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2237/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2237/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2237/20000 : ℝ) ^ (8339/2048 : ℝ) ≤ (6686942308967903/50000000000000000000 : ℝ) := by
    have hpowers : (2237/20000 : ℝ)^8339 ≤ (6686942308967903/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2237 : ℕ)^8339*50000000000000000000^2048 ≤ 6686942308967903^2048*20000^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2237 20000 6686942308967903 50000000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2237/20000 : ℝ)) (X := (6686942308967903/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8339/2048 : ℝ) ≤ (4462416956085771/12500000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8339 ≤ (4462416956085771/12500000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8339*12500000000000000000^2048 ≤ 4462416956085771^2048*20000^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 4462416956085771 12500000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (4462416956085771/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006686942308967903/25000000000000000000 : ℝ) ≤ (10000656840213091/10000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (25006686942308967903/25000000000000000000 : ℝ)^2048 ≤ (10000656840213091/10000000000000000 : ℝ)^8339 := by
      have hnat : (25006686942308967903 : ℕ)^2048*10000000000000000^8339 ≤ 10000656840213091^8339*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006686942308967903 25000000000000000000 10000656840213091 10000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000656840213091/10000000000000000 : ℝ)) (X := (25006686942308967903/25000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024536610133310987/50000000000000000000 : ℝ) ≤ (2500301245224061/2500000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (50024536610133310987/50000000000000000000 : ℝ)^2048 ≤ (2500301245224061/2500000000000000 : ℝ)^8339 := by
      have hnat : (50024536610133310987 : ℕ)^2048*2500000000000000^8339 ≤ 2500301245224061^8339*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024536610133310987 50000000000000000000 2500301245224061 2500000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500301245224061/2500000000000000 : ℝ)) (X := (50024536610133310987/50000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254462416956085771/6250000000000000000 : ℝ) ≤ (10001753121579397/10000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (6254462416956085771/6250000000000000000 : ℝ)^2048 ≤ (10001753121579397/10000000000000000 : ℝ)^8339 := by
      have hnat : (6254462416956085771 : ℕ)^2048*10000000000000000^8339 ≤ 10001753121579397^8339*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254462416956085771 6250000000000000000 10001753121579397 10000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001753121579397/10000000000000000 : ℝ)) (X := (6254462416956085771/6250000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6686942308967903/50000000000000000000 : ℝ) ≤ ((1524487072778389747/1525000000000000000 : ℝ)+2*(548140683153/305000000000000 : ℝ)*(2237/20000 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (1524487072778389747/1525000000000000000 : ℝ)+2*(548140683153/305000000000000 : ℝ)*(2237/20000 : ℝ)=(10000656840213091/10000000000000000 : ℝ) by norm_num, show 1+2*(6686942308967903/50000000000000000000 : ℝ)=(25006686942308967903/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4462416956085771/12500000000000000000 : ℝ)+(6686942308967903/50000000000000000000 : ℝ) ≤ ((1524487072778389747/1525000000000000000 : ℝ)+(548140683153/305000000000000 : ℝ)*((2847/20000 : ℝ)+(2237/20000 : ℝ)))^(8339/2048 : ℝ) := by
    rw [show (1524487072778389747/1525000000000000000 : ℝ)+(548140683153/305000000000000 : ℝ)*((2847/20000 : ℝ)+(2237/20000 : ℝ))=(2500301245224061/2500000000000000 : ℝ) by norm_num, show 1+(4462416956085771/12500000000000000000 : ℝ)+(6686942308967903/50000000000000000000 : ℝ)=(50024536610133310987/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4462416956085771/12500000000000000000 : ℝ) ≤ ((1524487072778389747/1525000000000000000 : ℝ)+2*(548140683153/305000000000000 : ℝ)*(2847/20000 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (1524487072778389747/1525000000000000000 : ℝ)+2*(548140683153/305000000000000 : ℝ)*(2847/20000 : ℝ)=(10001753121579397/10000000000000000 : ℝ) by norm_num, show 1+2*(4462416956085771/12500000000000000000 : ℝ)=(6254462416956085771/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1524487072778389747/1525000000000000000 : ℝ)*(X 1 0+X 2 0)+(548140683153/305000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (2237/20000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1524487072778389747/1525000000000000000 : ℝ)) (alpha := (548140683153/305000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1524487072778389747/1525000000000000000 : ℝ)*(X 0 1+X 2 1)+(548140683153/305000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (2237/20000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1524487072778389747/1525000000000000000 : ℝ)) (alpha := (548140683153/305000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1524487072778389747/1525000000000000000 : ℝ)*(X 0 2+X 1 2)+(548140683153/305000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (2237/20000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1524487072778389747/1525000000000000000 : ℝ)) (alpha := (548140683153/305000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-135271067/625000000 : ℝ)*X 0 0+(5394782673/10000000000 : ℝ)*X 0 1+(5264086207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336300491/2500000000 : ℝ)*X 1 0+(-1115326801/5000000000 : ℝ)*X 1 1+(1316021559/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345201859/10000000000 : ℝ)*X 2 0+(2632043177/5000000000 : ℝ)*X 2 1+(-1115326793/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2181938617/5000000000 : ℝ)*X 0 0+(4235669779/10000000000 : ℝ)*X 0 1+(2247970837/5000000000 : ℝ)*X 0 2+(2181938617/5000000000 : ℝ)*X 1 0+(4235669779/10000000000 : ℝ)*X 1 1+(2247970837/5000000000 : ℝ)*X 1 2+(2181938617/5000000000 : ℝ)*X 2 0+(4235669779/10000000000 : ℝ)*X 2 1+(2247970837/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1082171087/5000000000 : ℝ)*X 0 0+(5264424149/10000000000 : ℝ)*X 0 1+(5394443621/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312077863/10000000000 : ℝ)*X 1 0+(-1050147907/5000000000 : ℝ)*X 1 1+(5394443689/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328019389/2500000000 : ℝ)*X 2 0+(53944439/100000000 : ℝ)*X 2 1+(-420059189/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174555517/400000000 : ℝ)*X 0 0+(899053843/2000000000 : ℝ)*X 0 1+(4236344589/10000000000 : ℝ)*X 0 2+(174555517/400000000 : ℝ)*X 1 0+(899053843/2000000000 : ℝ)*X 1 1+(4236344589/10000000000 : ℝ)*X 1 2+(174555517/400000000 : ℝ)*X 2 0+(899053843/2000000000 : ℝ)*X 2 1+(4236344589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29743597678555215072891/15250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (580141979/100000000000000 : ℝ)*(base19) + (358590727/100000000000000 : ℝ)*(base23) + (96837739/100000000000000 : ℝ)*(upper3) + (1190139/3125000000000 : ℝ)*(upper4) + (21370677/50000000000000 : ℝ)*(upper5) + (5746748642118149/100000000000000 : ℝ)*(major0) + (5746748642118149/100000000000000 : ℝ)*(major1) + (114934972842363/2000000000000 : ℝ)*(major2) + (1912833646171683/25000000000000 : ℝ)*(sp0) + (7651349354758091/100000000000000 : ℝ)*(sp1) + (7651349576309343/100000000000000 : ℝ)*(sp2) + (240133829239497/6250000000000 : ℝ)*(sp3) + (15350213337/100000000000000 : ℝ)*(sp4) + (6016490937/100000000000000 : ℝ)*(sp7) + (384214728432289/10000000000000 : ℝ)*(f.failure) + (765134993490007/10000000000000 : ℝ)*(f.sum) + (105874189265247/30500000000000000000000000000 : ℝ)*base65 + (81783448901031697/152500000000000000000000000000000 : ℝ)*base68 + (26092128947731861/3050000000000000000000000000000 : ℝ)*base69 + (978007019586468303/152500000000000000000000000000000 : ℝ)*base71 + (11717832699753/30500000000000000000000000000 : ℝ)*base74 + (71010283911018139/3050000000000000000000000000000 : ℝ)*base76 + (700068184438203303/152500000000000000000000000000000 : ℝ)*base77 + (1249278827199296697/152500000000000000000000000000000 : ℝ)*base80 + (65806454186953/15250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (766907/500000000000000000000 : ℝ)*base90 + (766907/500000000000000000000 : ℝ)*base92 + (5766907/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (130514363042583317156957919/19062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (90925901/5000000000000 : ℝ)*(base19) + (224141337/12500000000000 : ℝ)*(base23) + (20548993/10000000000000 : ℝ)*(upper3) + (201950987/100000000000000 : ℝ)*(lower4) + (41261303/100000000000000 : ℝ)*(upper5) + (2888316216765241/50000000000000 : ℝ)*(major0) + (2888316216765241/50000000000000 : ℝ)*(major1) + (2888316216765241/50000000000000 : ℝ)*(major2) + (52497076811/100000000000000 : ℝ)*(sp1) + (58740191011/100000000000000 : ℝ)*(sp2) + (7691137721654151/100000000000000 : ℝ)*(sp4) + (192277085151483/2500000000000 : ℝ)*(sp5) + (1922769297083111/25000000000000 : ℝ)*(sp6) + (482765864648121/12500000000000 : ℝ)*(sp7) + (482765864648121/12500000000000 : ℝ)*(f.failure) + (7691137721654151/100000000000000 : ℝ)*(f.sum) + (15180194650877/7625000000000000000000000000 : ℝ)*base66 + (707223806325999027/76250000000000000000000000000000 : ℝ)*base67 + (374666575645999027/76250000000000000000000000000000 : ℝ)*base69 + (204511464519749027/76250000000000000000000000000000 : ℝ)*base71 + (25522769752377/7625000000000000000000000000 : ℝ)*base74 + (1463258537639749027/76250000000000000000000000000000 : ℝ)*base75 + (768881455408499027/76250000000000000000000000000000 : ℝ)*base77 + (308118372042750973/76250000000000000000000000000000 : ℝ)*base80 + (23159269150877/7625000000000000000000000000 : ℝ)*base82 + (2661923/625000000000000000000 : ℝ)*base90 + (2661923/625000000000000000000 : ℝ)*base92 + (2661923/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1147_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2237/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1147_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1147_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2061/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9093/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1147_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1147_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1147_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2061/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9093/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1147_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

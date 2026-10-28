-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1146_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:33:36.218616+00:00
-- url     : https://prove2.me/submissions/45d9e915-c030-4e4c-abfa-f82255954a21

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
theorem support_rectangle_w1146_s0_0 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1890545439/10000000000 : ℝ)*x 0 + (6053406121/10000000000 : ℝ)*x 1 + (298811123/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1890545439/10000000000 : ℝ)^8339 ≤ (2198437295651/20000000000000 : ℝ)^6291 := by
    have hnat : (1890545439 : ℕ)^8339*20000000000000^6291 ≤ 2198437295651^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1890545439 10000000000 2198437295651 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6053406121/10000000000 : ℝ)^8339 ≤ (25704021104789/50000000000000 : ℝ)^6291 := by
    have hnat : (6053406121 : ℕ)^8339*50000000000000^6291 ≤ 25704021104789^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6053406121 10000000000 25704021104789 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (298811123/625000000 : ℝ)^8339 ≤ (37599771303669/100000000000000 : ℝ)^6291 := by
    have hnat : (298811123 : ℕ)^8339*100000000000000^6291 ≤ 37599771303669^6291*625000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298811123 625000000 37599771303669 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1890545439/10000000000 : ℝ), (6053406121/10000000000 : ℝ), (298811123/625000000 : ℝ)] ![(2198437295651/20000000000000 : ℝ), (25704021104789/50000000000000 : ℝ), (37599771303669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1890545439/10000000000 : ℝ)|^8339 ≤ (2198437295651/20000000000000 : ℝ)^6291
        have hw : |(-1890545439/10000000000 : ℝ)|=(1890545439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6053406121/10000000000 : ℝ)|^8339 ≤ (25704021104789/50000000000000 : ℝ)^6291
        have hw : |(6053406121/10000000000 : ℝ)|=(6053406121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(298811123/625000000 : ℝ)|^8339 ≤ (37599771303669/100000000000000 : ℝ)^6291
        have hw : |(298811123/625000000 : ℝ)|=(298811123/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s0_1 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1379142057/2500000000 : ℝ)*x 0 + (-1310327977/5000000000 : ℝ)*x 1 + (478097801/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1379142057/2500000000 : ℝ)^8339 ≤ (9090772085451/20000000000000 : ℝ)^6291 := by
    have hnat : (1379142057 : ℕ)^8339*20000000000000^6291 ≤ 9090772085451^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379142057 2500000000 9090772085451 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310327977/5000000000 : ℝ)^8339 ≤ (3389273562739/20000000000000 : ℝ)^6291 := by
    have hnat : (1310327977 : ℕ)^8339*20000000000000^6291 ≤ 3389273562739^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310327977 5000000000 3389273562739 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (478097801/1000000000 : ℝ)^8339 ≤ (18799885870753/50000000000000 : ℝ)^6291 := by
    have hnat : (478097801 : ℕ)^8339*50000000000000^6291 ≤ 18799885870753^6291*1000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478097801 1000000000 18799885870753 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1379142057/2500000000 : ℝ), (-1310327977/5000000000 : ℝ), (478097801/1000000000 : ℝ)] ![(9090772085451/20000000000000 : ℝ), (3389273562739/20000000000000 : ℝ), (18799885870753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1379142057/2500000000 : ℝ)|^8339 ≤ (9090772085451/20000000000000 : ℝ)^6291
        have hw : |(1379142057/2500000000 : ℝ)|=(1379142057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1310327977/5000000000 : ℝ)|^8339 ≤ (3389273562739/20000000000000 : ℝ)^6291
        have hw : |(-1310327977/5000000000 : ℝ)|=(1310327977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(478097801/1000000000 : ℝ)|^8339 ≤ (18799885870753/50000000000000 : ℝ)^6291
        have hw : |(478097801/1000000000 : ℝ)|=(478097801/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s0_2 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5516568493/10000000000 : ℝ)*x 0 + (597622237/1250000000 : ℝ)*x 1 + (-655163939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516568493/10000000000 : ℝ)^8339 ≤ (5681732915193/12500000000000 : ℝ)^6291 := by
    have hnat : (5516568493 : ℕ)^8339*12500000000000^6291 ≤ 5681732915193^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516568493 10000000000 5681732915193 12500000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597622237/1250000000 : ℝ)^8339 ≤ (9399942638273/25000000000000 : ℝ)^6291 := by
    have hnat : (597622237 : ℕ)^8339*25000000000000^6291 ≤ 9399942638273^6291*1250000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597622237 1250000000 9399942638273 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655163939/2500000000 : ℝ)^8339 ≤ (8473183058261/50000000000000 : ℝ)^6291 := by
    have hnat : (655163939 : ℕ)^8339*50000000000000^6291 ≤ 8473183058261^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655163939 2500000000 8473183058261 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516568493/10000000000 : ℝ), (597622237/1250000000 : ℝ), (-655163939/2500000000 : ℝ)] ![(5681732915193/12500000000000 : ℝ), (9399942638273/25000000000000 : ℝ), (8473183058261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516568493/10000000000 : ℝ)|^8339 ≤ (5681732915193/12500000000000 : ℝ)^6291
        have hw : |(5516568493/10000000000 : ℝ)|=(5516568493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(597622237/1250000000 : ℝ)|^8339 ≤ (9399942638273/25000000000000 : ℝ)^6291
        have hw : |(597622237/1250000000 : ℝ)|=(597622237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-655163939/2500000000 : ℝ)|^8339 ≤ (8473183058261/50000000000000 : ℝ)^6291
        have hw : |(-655163939/2500000000 : ℝ)|=(655163939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s0_3 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4200667527/10000000000 : ℝ)*x 0 + (3120893797/10000000000 : ℝ)*x 1 + (5654343117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4200667527/10000000000 : ℝ)^8339 ≤ (30930840907/97656250000 : ℝ)^6291 := by
    have hnat : (4200667527 : ℕ)^8339*97656250000^6291 ≤ 30930840907^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4200667527 10000000000 30930840907 97656250000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3120893797/10000000000 : ℝ)^8339 ≤ (4272423827501/20000000000000 : ℝ)^6291 := by
    have hnat : (3120893797 : ℕ)^8339*20000000000000^6291 ≤ 4272423827501^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3120893797 10000000000 4272423827501 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5654343117/10000000000 : ℝ)^8339 ≤ (2935293734539/6250000000000 : ℝ)^6291 := by
    have hnat : (5654343117 : ℕ)^8339*6250000000000^6291 ≤ 2935293734539^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5654343117 10000000000 2935293734539 6250000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4200667527/10000000000 : ℝ), (3120893797/10000000000 : ℝ), (5654343117/10000000000 : ℝ)] ![(30930840907/97656250000 : ℝ), (4272423827501/20000000000000 : ℝ), (2935293734539/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4200667527/10000000000 : ℝ)|^8339 ≤ (30930840907/97656250000 : ℝ)^6291
        have hw : |(4200667527/10000000000 : ℝ)|=(4200667527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3120893797/10000000000 : ℝ)|^8339 ≤ (4272423827501/20000000000000 : ℝ)^6291
        have hw : |(3120893797/10000000000 : ℝ)|=(3120893797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5654343117/10000000000 : ℝ)|^8339 ≤ (2935293734539/6250000000000 : ℝ)^6291
        have hw : |(5654343117/10000000000 : ℝ)|=(5654343117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s0_4 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-236959901/1250000000 : ℝ)*x 0 + (4813801041/10000000000 : ℝ)*x 1 + (6019428759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (236959901/1250000000 : ℝ)^8339 ≤ (11031770451203/100000000000000 : ℝ)^6291 := by
    have hnat : (236959901 : ℕ)^8339*100000000000000^6291 ≤ 11031770451203^6291*1250000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236959901 1250000000 11031770451203 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4813801041/10000000000 : ℝ)^8339 ≤ (4742790391517/12500000000000 : ℝ)^6291 := by
    have hnat : (4813801041 : ℕ)^8339*12500000000000^6291 ≤ 4742790391517^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4813801041 10000000000 4742790391517 12500000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6019428759/10000000000 : ℝ)^8339 ≤ (51025906405049/100000000000000 : ℝ)^6291 := by
    have hnat : (6019428759 : ℕ)^8339*100000000000000^6291 ≤ 51025906405049^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6019428759 10000000000 51025906405049 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-236959901/1250000000 : ℝ), (4813801041/10000000000 : ℝ), (6019428759/10000000000 : ℝ)] ![(11031770451203/100000000000000 : ℝ), (4742790391517/12500000000000 : ℝ), (51025906405049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-236959901/1250000000 : ℝ)|^8339 ≤ (11031770451203/100000000000000 : ℝ)^6291
        have hw : |(-236959901/1250000000 : ℝ)|=(236959901/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4813801041/10000000000 : ℝ)|^8339 ≤ (4742790391517/12500000000000 : ℝ)^6291
        have hw : |(4813801041/10000000000 : ℝ)|=(4813801041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6019428759/10000000000 : ℝ)|^8339 ≤ (51025906405049/100000000000000 : ℝ)^6291
        have hw : |(6019428759/10000000000 : ℝ)|=(6019428759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s0_5 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2585400727/5000000000 : ℝ)*x 0 + (-345551301/2500000000 : ℝ)*x 1 + (6019428611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585400727/5000000000 : ℝ)^8339 ≤ (41716534204337/100000000000000 : ℝ)^6291 := by
    have hnat : (2585400727 : ℕ)^8339*100000000000000^6291 ≤ 41716534204337^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585400727 5000000000 41716534204337 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (345551301/2500000000 : ℝ)^8339 ≤ (290302441567/4000000000000 : ℝ)^6291 := by
    have hnat : (345551301 : ℕ)^8339*4000000000000^6291 ≤ 290302441567^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345551301 2500000000 290302441567 4000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6019428611/10000000000 : ℝ)^8339 ≤ (12756476185513/25000000000000 : ℝ)^6291 := by
    have hnat : (6019428611 : ℕ)^8339*25000000000000^6291 ≤ 12756476185513^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6019428611 10000000000 12756476185513 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585400727/5000000000 : ℝ), (-345551301/2500000000 : ℝ), (6019428611/10000000000 : ℝ)] ![(41716534204337/100000000000000 : ℝ), (290302441567/4000000000000 : ℝ), (12756476185513/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585400727/5000000000 : ℝ)|^8339 ≤ (41716534204337/100000000000000 : ℝ)^6291
        have hw : |(2585400727/5000000000 : ℝ)|=(2585400727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-345551301/2500000000 : ℝ)|^8339 ≤ (290302441567/4000000000000 : ℝ)^6291
        have hw : |(-345551301/2500000000 : ℝ)|=(345551301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6019428611/10000000000 : ℝ)|^8339 ≤ (12756476185513/25000000000000 : ℝ)^6291
        have hw : |(6019428611/10000000000 : ℝ)|=(6019428611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s0_6 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5170801451/10000000000 : ℝ)*x 0 + (1203885729/2000000000 : ℝ)*x 1 + (-1382205153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5170801451/10000000000 : ℝ)^8339 ≤ (20858267086127/50000000000000 : ℝ)^6291 := by
    have hnat : (5170801451 : ℕ)^8339*50000000000000^6291 ≤ 20858267086127^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170801451 10000000000 20858267086127 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1203885729/2000000000 : ℝ)^8339 ≤ (12756476281023/25000000000000 : ℝ)^6291 := by
    have hnat : (1203885729 : ℕ)^8339*25000000000000^6291 ≤ 12756476281023^6291*2000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203885729 2000000000 12756476281023 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1382205153/10000000000 : ℝ)^8339 ≤ (1814390171053/25000000000000 : ℝ)^6291 := by
    have hnat : (1382205153 : ℕ)^8339*25000000000000^6291 ≤ 1814390171053^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382205153 10000000000 1814390171053 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5170801451/10000000000 : ℝ), (1203885729/2000000000 : ℝ), (-1382205153/10000000000 : ℝ)] ![(20858267086127/50000000000000 : ℝ), (12756476281023/25000000000000 : ℝ), (1814390171053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5170801451/10000000000 : ℝ)|^8339 ≤ (20858267086127/50000000000000 : ℝ)^6291
        have hw : |(5170801451/10000000000 : ℝ)|=(5170801451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1203885729/2000000000 : ℝ)|^8339 ≤ (12756476281023/25000000000000 : ℝ)^6291
        have hw : |(1203885729/2000000000 : ℝ)|=(1203885729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1382205153/10000000000 : ℝ)|^8339 ≤ (1814390171053/25000000000000 : ℝ)^6291
        have hw : |(-1382205153/10000000000 : ℝ)|=(1382205153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s0_7 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4210889289/10000000000 : ℝ)*x 0 + (5588991021/10000000000 : ℝ)*x 1 + (1594272117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4210889289/10000000000 : ℝ)^8339 ≤ (15887692241239/50000000000000 : ℝ)^6291 := by
    have hnat : (4210889289 : ℕ)^8339*50000000000000^6291 ≤ 15887692241239^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4210889289 10000000000 15887692241239 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5588991021/10000000000 : ℝ)^8339 ≤ (46246536371627/100000000000000 : ℝ)^6291 := by
    have hnat : (5588991021 : ℕ)^8339*100000000000000^6291 ≤ 46246536371627^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5588991021 10000000000 46246536371627 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1594272117/5000000000 : ℝ)^8339 ≤ (10989039568477/50000000000000 : ℝ)^6291 := by
    have hnat : (1594272117 : ℕ)^8339*50000000000000^6291 ≤ 10989039568477^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1594272117 5000000000 10989039568477 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4210889289/10000000000 : ℝ), (5588991021/10000000000 : ℝ), (1594272117/5000000000 : ℝ)] ![(15887692241239/50000000000000 : ℝ), (46246536371627/100000000000000 : ℝ), (10989039568477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4210889289/10000000000 : ℝ)|^8339 ≤ (15887692241239/50000000000000 : ℝ)^6291
        have hw : |(4210889289/10000000000 : ℝ)|=(4210889289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5588991021/10000000000 : ℝ)|^8339 ≤ (46246536371627/100000000000000 : ℝ)^6291
        have hw : |(5588991021/10000000000 : ℝ)|=(5588991021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1594272117/5000000000 : ℝ)|^8339 ≤ (10989039568477/50000000000000 : ℝ)^6291
        have hw : |(1594272117/5000000000 : ℝ)|=(1594272117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1146_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (43/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (139/500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4169/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4169 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4169*1^1024 ≤ 0^1024*1^4169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4169 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4169/1024 : ℝ) ≤ (599530392203078321/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4169 ≤ (599530392203078321/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4169*25000000000000000000^1024 ≤ 599530392203078321^1024*5^4169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 599530392203078321 25000000000000000000 4169 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (599530392203078321/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4169 := by
      have hnat : (1 : ℕ)^1024*1^4169 ≤ 1^4169*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25599530392203078321/25000000000000000000 : ℝ) ≤ (2514594448652747/2500000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (25599530392203078321/25000000000000000000 : ℝ)^1024 ≤ (2514594448652747/2500000000000000 : ℝ)^4169 := by
      have hnat : (25599530392203078321 : ℕ)^1024*2500000000000000^4169 ≤ 2514594448652747^4169*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25599530392203078321 25000000000000000000 2514594448652747 2500000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514594448652747/2500000000000000 : ℝ)) (X := (25599530392203078321/25000000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (13099530392203078321/12500000000000000000 : ℝ) ≤ (1264594448652747/1250000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (13099530392203078321/12500000000000000000 : ℝ)^1024 ≤ (1264594448652747/1250000000000000 : ℝ)^4169 := by
      have hnat : (13099530392203078321 : ℕ)^1024*1250000000000000^4169 ≤ 1264594448652747^4169*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13099530392203078321 12500000000000000000 1264594448652747 1250000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1264594448652747/1250000000000000 : ℝ)) (X := (13099530392203078321/12500000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14594448652747/1000000000000000 : ℝ)*(0 : ℝ))^(4169/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14594448652747/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(599530392203078321/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14594448652747/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4169/1024 : ℝ) := by
    rw [show (1 : ℝ)+(14594448652747/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2514594448652747/2500000000000000 : ℝ) by norm_num, show 1+(599530392203078321/25000000000000000000 : ℝ)+(0 : ℝ)=(25599530392203078321/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(599530392203078321/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14594448652747/1000000000000000 : ℝ)*(2/5 : ℝ))^(4169/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14594448652747/1000000000000000 : ℝ)*(2/5 : ℝ)=(1264594448652747/1250000000000000 : ℝ) by norm_num, show 1+2*(599530392203078321/25000000000000000000 : ℝ)=(13099530392203078321/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14594448652747/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14594448652747/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14594448652747/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14594448652747/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14594448652747/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14594448652747/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1890545439/10000000000 : ℝ)*X 0 0+(6053406121/10000000000 : ℝ)*X 0 1+(298811123/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1379142057/2500000000 : ℝ)*X 1 0+(-1310327977/5000000000 : ℝ)*X 1 1+(478097801/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5516568493/10000000000 : ℝ)*X 2 0+(597622237/1250000000 : ℝ)*X 2 1+(-655163939/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4200667527/10000000000 : ℝ)*X 0 0+(3120893797/10000000000 : ℝ)*X 0 1+(5654343117/10000000000 : ℝ)*X 0 2+(4200667527/10000000000 : ℝ)*X 1 0+(3120893797/10000000000 : ℝ)*X 1 1+(5654343117/10000000000 : ℝ)*X 1 2+(4200667527/10000000000 : ℝ)*X 2 0+(3120893797/10000000000 : ℝ)*X 2 1+(5654343117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-236959901/1250000000 : ℝ)*X 0 0+(4813801041/10000000000 : ℝ)*X 0 1+(6019428759/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2585400727/5000000000 : ℝ)*X 1 0+(-345551301/2500000000 : ℝ)*X 1 1+(6019428611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5170801451/10000000000 : ℝ)*X 2 0+(1203885729/2000000000 : ℝ)*X 2 1+(-1382205153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4210889289/10000000000 : ℝ)*X 0 0+(5588991021/10000000000 : ℝ)*X 0 1+(1594272117/5000000000 : ℝ)*X 0 2+(4210889289/10000000000 : ℝ)*X 1 0+(5588991021/10000000000 : ℝ)*X 1 1+(1594272117/5000000000 : ℝ)*X 1 2+(4210889289/10000000000 : ℝ)*X 2 0+(5588991021/10000000000 : ℝ)*X 2 1+(1594272117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12925137516539570473647/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41046801/100000000000000 : ℝ)*(base1) + (516159879/50000000000000 : ℝ)*(base19) + (979527157/100000000000000 : ℝ)*(base23) + (90545139/100000000000000 : ℝ)*(base24) + (60371631/25000000000000 : ℝ)*(upper3) + (147578308455317/25000000000000 : ℝ)*(major0) + (147578308455317/25000000000000 : ℝ)*(major1) + (147578308455317/25000000000000 : ℝ)*(major2) + (157180481998793/20000000000000 : ℝ)*(sp0) + (392951802633471/50000000000000 : ℝ)*(sp1) + (157180713502881/20000000000000 : ℝ)*(sp2) + (78943962866113/20000000000000 : ℝ)*(sp3) + (141789971/6250000000000 : ℝ)*(sp4) + (1836810333/100000000000000 : ℝ)*(sp7) + (197360846093849/50000000000000 : ℝ)*(f.failure) + (7859046375867/1000000000000 : ℝ)*(f.sum) + (35148737056701/12500000000000000000000000000 : ℝ)*base66 + (37698247830799/25000000000000000000000000000 : ℝ)*base67 + (139861200469201/25000000000000000000000000000 : ℝ)*base70 + (29840820394201/25000000000000000000000000000 : ℝ)*base72 + (31627609069201/12500000000000000000000000000 : ℝ)*base74 + (25109637630799/25000000000000000000000000000 : ℝ)*base75 + (11108892619201/25000000000000000000000000000 : ℝ)*base78 + (77601130644201/25000000000000000000000000000 : ℝ)*base80 + (46774149281701/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2969609/5000000000000000000000 : ℝ)*base90 + (2969609/5000000000000000000000 : ℝ)*base92 + (2969609/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (177160673803842910317453/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (87132713/100000000000000 : ℝ)*(base1) + (437399987/25000000000000 : ℝ)*(base19) + (69941377/4000000000000 : ℝ)*(base23) + (95449367/50000000000000 : ℝ)*(upper3) + (102652547/50000000000000 : ℝ)*(upper5) + (623016420400533/100000000000000 : ℝ)*(major0) + (623016420400533/100000000000000 : ℝ)*(major1) + (623016420400533/100000000000000 : ℝ)*(major2) + (889856521/25000000000000 : ℝ)*(sp1) + (3550685411/100000000000000 : ℝ)*(sp2) + (103680441145889/12500000000000 : ℝ)*(sp4) + (829438133008367/100000000000000 : ℝ)*(sp5) + (829438142814563/100000000000000 : ℝ)*(sp6) + (10414726885493/2500000000000 : ℝ)*(sp7) + (416589162552433/100000000000000 : ℝ)*(f.failure) + (829443442034399/100000000000000 : ℝ)*(f.sum) + (170618485849/50000000000000000000000000000 : ℝ)*base66 + (32081800485849/100000000000000000000000000000 : ℝ)*base68 + (445158878085849/100000000000000000000000000000 : ℝ)*base70 + (166007585714151/100000000000000000000000000000 : ℝ)*base71 + (81886435085849/50000000000000000000000000000 : ℝ)*base74 + (119158415014151/100000000000000000000000000000 : ℝ)*base75 + (158501409114151/100000000000000000000000000000 : ℝ)*base77 + (20171319614151/100000000000000000000000000000 : ℝ)*base79 + (200165810535849/50000000000000000000000000000 : ℝ)*base82 + (15120353/10000000000000000000000 : ℝ)*base90 + (15120353/10000000000000000000000 : ℝ)*base92 + (15120353/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1146_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (43/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (139/500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1146_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1146_s1_0 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-104745883/500000000 : ℝ)*x 0 + (5700445851/10000000000 : ℝ)*x 1 + (1250775267/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104745883/500000000 : ℝ)^8339 ≤ (6297187829087/50000000000000 : ℝ)^6291 := by
    have hnat : (104745883 : ℕ)^8339*50000000000000^6291 ≤ 6297187829087^6291*500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104745883 500000000 6297187829087 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5700445851/10000000000 : ℝ)^8339 ≤ (23736479510783/50000000000000 : ℝ)^6291 := by
    have hnat : (5700445851 : ℕ)^8339*50000000000000^6291 ≤ 23736479510783^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5700445851 10000000000 23736479510783 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1250775267/2500000000 : ℝ)^8339 ≤ (39932665312617/100000000000000 : ℝ)^6291 := by
    have hnat : (1250775267 : ℕ)^8339*100000000000000^6291 ≤ 39932665312617^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250775267 2500000000 39932665312617 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104745883/500000000 : ℝ), (5700445851/10000000000 : ℝ), (1250775267/2500000000 : ℝ)] ![(6297187829087/50000000000000 : ℝ), (23736479510783/50000000000000 : ℝ), (39932665312617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104745883/500000000 : ℝ)|^8339 ≤ (6297187829087/50000000000000 : ℝ)^6291
        have hw : |(-104745883/500000000 : ℝ)|=(104745883/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5700445851/10000000000 : ℝ)|^8339 ≤ (23736479510783/50000000000000 : ℝ)^6291
        have hw : |(5700445851/10000000000 : ℝ)|=(5700445851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1250775267/2500000000 : ℝ)|^8339 ≤ (39932665312617/100000000000000 : ℝ)^6291
        have hw : |(1250775267/2500000000 : ℝ)|=(1250775267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s1_1 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (42335191/78125000 : ℝ)*x 0 + (-154447939/625000000 : ℝ)*x 1 + (5003100299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42335191/78125000 : ℝ)^8339 ≤ (44390277729663/100000000000000 : ℝ)^6291 := by
    have hnat : (42335191 : ℕ)^8339*100000000000000^6291 ≤ 44390277729663^6291*78125000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42335191 78125000 44390277729663 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (154447939/625000000 : ℝ)^8339 ≤ (15677065073197/100000000000000 : ℝ)^6291 := by
    have hnat : (154447939 : ℕ)^8339*100000000000000^6291 ≤ 15677065073197^6291*625000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154447939 625000000 15677065073197 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5003100299/10000000000 : ℝ)^8339 ≤ (19966328588321/50000000000000 : ℝ)^6291 := by
    have hnat : (5003100299 : ℕ)^8339*50000000000000^6291 ≤ 19966328588321^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5003100299 10000000000 19966328588321 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42335191/78125000 : ℝ), (-154447939/625000000 : ℝ), (5003100299/10000000000 : ℝ)] ![(44390277729663/100000000000000 : ℝ), (15677065073197/100000000000000 : ℝ), (19966328588321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42335191/78125000 : ℝ)|^8339 ≤ (44390277729663/100000000000000 : ℝ)^6291
        have hw : |(42335191/78125000 : ℝ)|=(42335191/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-154447939/625000000 : ℝ)|^8339 ≤ (15677065073197/100000000000000 : ℝ)^6291
        have hw : |(-154447939/625000000 : ℝ)|=(154447939/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5003100299/10000000000 : ℝ)|^8339 ≤ (19966328588321/50000000000000 : ℝ)^6291
        have hw : |(5003100299/10000000000 : ℝ)|=(5003100299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s1_2 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5418906441/10000000000 : ℝ)*x 0 + (5003098527/10000000000 : ℝ)*x 1 + (-2471166681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5418906441/10000000000 : ℝ)^8339 ≤ (5548787421337/12500000000000 : ℝ)^6291 := by
    have hnat : (5418906441 : ℕ)^8339*12500000000000^6291 ≤ 5548787421337^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418906441 10000000000 5548787421337 12500000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5003098527/10000000000 : ℝ)^8339 ≤ (19966319214493/50000000000000 : ℝ)^6291 := by
    have hnat : (5003098527 : ℕ)^8339*50000000000000^6291 ≤ 19966319214493^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5003098527 10000000000 19966319214493 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2471166681/10000000000 : ℝ)^8339 ≤ (7838531094413/50000000000000 : ℝ)^6291 := by
    have hnat : (2471166681 : ℕ)^8339*50000000000000^6291 ≤ 7838531094413^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2471166681 10000000000 7838531094413 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5418906441/10000000000 : ℝ), (5003098527/10000000000 : ℝ), (-2471166681/10000000000 : ℝ)] ![(5548787421337/12500000000000 : ℝ), (19966319214493/50000000000000 : ℝ), (7838531094413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5418906441/10000000000 : ℝ)|^8339 ≤ (5548787421337/12500000000000 : ℝ)^6291
        have hw : |(5418906441/10000000000 : ℝ)|=(5418906441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5003098527/10000000000 : ℝ)|^8339 ≤ (19966319214493/50000000000000 : ℝ)^6291
        have hw : |(5003098527/10000000000 : ℝ)|=(5003098527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2471166681/10000000000 : ℝ)|^8339 ≤ (7838531094413/50000000000000 : ℝ)^6291
        have hw : |(-2471166681/10000000000 : ℝ)|=(2471166681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s1_3 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2158549299/5000000000 : ℝ)*x 0 + (735556197/2000000000 : ℝ)*x 1 + (1266553993/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158549299/5000000000 : ℝ)^8339 ≤ (2052630427759/6250000000000 : ℝ)^6291 := by
    have hnat : (2158549299 : ℕ)^8339*6250000000000^6291 ≤ 2052630427759^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158549299 5000000000 2052630427759 6250000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (735556197/2000000000 : ℝ)^8339 ≤ (6639032119727/25000000000000 : ℝ)^6291 := by
    have hnat : (735556197 : ℕ)^8339*25000000000000^6291 ≤ 6639032119727^6291*2000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735556197 2000000000 6639032119727 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1266553993/2500000000 : ℝ)^8339 ≤ (8120356932917/20000000000000 : ℝ)^6291 := by
    have hnat : (1266553993 : ℕ)^8339*20000000000000^6291 ≤ 8120356932917^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1266553993 2500000000 8120356932917 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158549299/5000000000 : ℝ), (735556197/2000000000 : ℝ), (1266553993/2500000000 : ℝ)] ![(2052630427759/6250000000000 : ℝ), (6639032119727/25000000000000 : ℝ), (8120356932917/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158549299/5000000000 : ℝ)|^8339 ≤ (2052630427759/6250000000000 : ℝ)^6291
        have hw : |(2158549299/5000000000 : ℝ)|=(2158549299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(735556197/2000000000 : ℝ)|^8339 ≤ (6639032119727/25000000000000 : ℝ)^6291
        have hw : |(735556197/2000000000 : ℝ)|=(735556197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1266553993/2500000000 : ℝ)|^8339 ≤ (8120356932917/20000000000000 : ℝ)^6291
        have hw : |(1266553993/2500000000 : ℝ)|=(1266553993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s1_4 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-419144581/2000000000 : ℝ)*x 0 + (40100867/80000000 : ℝ)*x 1 + (1422686777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419144581/2000000000 : ℝ)^8339 ≤ (2520158611841/20000000000000 : ℝ)^6291 := by
    have hnat : (419144581 : ℕ)^8339*20000000000000^6291 ≤ 2520158611841^6291*2000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419144581 2000000000 2520158611841 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40100867/80000000 : ℝ)^8339 ≤ (20016641587153/50000000000000 : ℝ)^6291 := by
    have hnat : (40100867 : ℕ)^8339*50000000000000^6291 ≤ 20016641587153^6291*80000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40100867 80000000 20016641587153 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1422686777/2500000000 : ℝ)^8339 ≤ (1480185117449/3125000000000 : ℝ)^6291 := by
    have hnat : (1422686777 : ℕ)^8339*3125000000000^6291 ≤ 1480185117449^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1422686777 2500000000 1480185117449 3125000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-419144581/2000000000 : ℝ), (40100867/80000000 : ℝ), (1422686777/2500000000 : ℝ)] ![(2520158611841/20000000000000 : ℝ), (20016641587153/50000000000000 : ℝ), (1480185117449/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-419144581/2000000000 : ℝ)|^8339 ≤ (2520158611841/20000000000000 : ℝ)^6291
        have hw : |(-419144581/2000000000 : ℝ)|=(419144581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40100867/80000000 : ℝ)|^8339 ≤ (20016641587153/50000000000000 : ℝ)^6291
        have hw : |(40100867/80000000 : ℝ)|=(40100867/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1422686777/2500000000 : ℝ)|^8339 ≤ (1480185117449/3125000000000 : ℝ)^6291
        have hw : |(1422686777/2500000000 : ℝ)|=(1422686777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s1_5 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1310020419/2500000000 : ℝ)*x 0 + (-1783516033/10000000000 : ℝ)*x 1 + (711343849/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1310020419/2500000000 : ℝ)^8339 ≤ (42459035471187/100000000000000 : ℝ)^6291 := by
    have hnat : (1310020419 : ℕ)^8339*100000000000000^6291 ≤ 42459035471187^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310020419 2500000000 42459035471187 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1783516033/10000000000 : ℝ)^8339 ≤ (10175000105997/100000000000000 : ℝ)^6291 := by
    have hnat : (1783516033 : ℕ)^8339*100000000000000^6291 ≤ 10175000105997^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783516033 10000000000 10175000105997 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (711343849/1250000000 : ℝ)^8339 ≤ (47365964403701/100000000000000 : ℝ)^6291 := by
    have hnat : (711343849 : ℕ)^8339*100000000000000^6291 ≤ 47365964403701^6291*1250000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711343849 1250000000 47365964403701 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1310020419/2500000000 : ℝ), (-1783516033/10000000000 : ℝ), (711343849/1250000000 : ℝ)] ![(42459035471187/100000000000000 : ℝ), (10175000105997/100000000000000 : ℝ), (47365964403701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1310020419/2500000000 : ℝ)|^8339 ≤ (42459035471187/100000000000000 : ℝ)^6291
        have hw : |(1310020419/2500000000 : ℝ)|=(1310020419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1783516033/10000000000 : ℝ)|^8339 ≤ (10175000105997/100000000000000 : ℝ)^6291
        have hw : |(-1783516033/10000000000 : ℝ)|=(1783516033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(711343849/1250000000 : ℝ)|^8339 ≤ (47365964403701/100000000000000 : ℝ)^6291
        have hw : |(711343849/1250000000 : ℝ)|=(711343849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s1_6 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5240080277/10000000000 : ℝ)*x 0 + (5690752643/10000000000 : ℝ)*x 1 + (-1783515319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5240080277/10000000000 : ℝ)^8339 ≤ (10614755111291/25000000000000 : ℝ)^6291 := by
    have hnat : (5240080277 : ℕ)^8339*25000000000000^6291 ≤ 10614755111291^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240080277 10000000000 10614755111291 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5690752643/10000000000 : ℝ)^8339 ≤ (47365984825667/100000000000000 : ℝ)^6291 := by
    have hnat : (5690752643 : ℕ)^8339*100000000000000^6291 ≤ 47365984825667^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5690752643 10000000000 47365984825667 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1783515319/10000000000 : ℝ)^8339 ≤ (5087497353271/50000000000000 : ℝ)^6291 := by
    have hnat : (1783515319 : ℕ)^8339*50000000000000^6291 ≤ 5087497353271^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783515319 10000000000 5087497353271 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5240080277/10000000000 : ℝ), (5690752643/10000000000 : ℝ), (-1783515319/10000000000 : ℝ)] ![(10614755111291/25000000000000 : ℝ), (47365984825667/100000000000000 : ℝ), (5087497353271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5240080277/10000000000 : ℝ)|^8339 ≤ (10614755111291/25000000000000 : ℝ)^6291
        have hw : |(5240080277/10000000000 : ℝ)|=(5240080277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5690752643/10000000000 : ℝ)|^8339 ≤ (47365984825667/100000000000000 : ℝ)^6291
        have hw : |(5690752643/10000000000 : ℝ)|=(5690752643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1783515319/10000000000 : ℝ)|^8339 ≤ (5087497353271/50000000000000 : ℝ)^6291
        have hw : |(-1783515319/10000000000 : ℝ)|=(1783515319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s1_7 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (539836403/1250000000 : ℝ)*x 0 + (5047286837/10000000000 : ℝ)*x 1 + (3697083079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539836403/1250000000 : ℝ)^8339 ≤ (16429073928753/50000000000000 : ℝ)^6291 := by
    have hnat : (539836403 : ℕ)^8339*50000000000000^6291 ≤ 16429073928753^6291*1250000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539836403 1250000000 16429073928753 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5047286837/10000000000 : ℝ)^8339 ≤ (40400818912819/100000000000000 : ℝ)^6291 := by
    have hnat : (5047286837 : ℕ)^8339*100000000000000^6291 ≤ 40400818912819^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5047286837 10000000000 40400818912819 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3697083079/10000000000 : ℝ)^8339 ≤ (26741033211111/100000000000000 : ℝ)^6291 := by
    have hnat : (3697083079 : ℕ)^8339*100000000000000^6291 ≤ 26741033211111^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3697083079 10000000000 26741033211111 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539836403/1250000000 : ℝ), (5047286837/10000000000 : ℝ), (3697083079/10000000000 : ℝ)] ![(16429073928753/50000000000000 : ℝ), (40400818912819/100000000000000 : ℝ), (26741033211111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539836403/1250000000 : ℝ)|^8339 ≤ (16429073928753/50000000000000 : ℝ)^6291
        have hw : |(539836403/1250000000 : ℝ)|=(539836403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5047286837/10000000000 : ℝ)|^8339 ≤ (40400818912819/100000000000000 : ℝ)^6291
        have hw : |(5047286837/10000000000 : ℝ)|=(5047286837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3697083079/10000000000 : ℝ)|^8339 ≤ (26741033211111/100000000000000 : ℝ)^6291
        have hw : |(3697083079/10000000000 : ℝ)|=(3697083079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s1_8 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1494971/2500000000 : ℝ)*x 0 + (5490340633/10000000000 : ℝ)*x 1 + (3177355547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1494971/2500000000 : ℝ)^8339 ≤ (13344523/250000000000 : ℝ)^6291 := by
    have hnat : (1494971 : ℕ)^8339*250000000000^6291 ≤ 13344523^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1494971 2500000000 13344523 250000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490340633/10000000000 : ℝ)^8339 ≤ (45167628576631/100000000000000 : ℝ)^6291 := by
    have hnat : (5490340633 : ℕ)^8339*100000000000000^6291 ≤ 45167628576631^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490340633 10000000000 45167628576631 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3177355547/5000000000 : ℝ)^8339 ≤ (2193081344083/4000000000000 : ℝ)^6291 := by
    have hnat : (3177355547 : ℕ)^8339*4000000000000^6291 ≤ 2193081344083^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3177355547 5000000000 2193081344083 4000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1494971/2500000000 : ℝ), (5490340633/10000000000 : ℝ), (3177355547/5000000000 : ℝ)] ![(13344523/250000000000 : ℝ), (45167628576631/100000000000000 : ℝ), (2193081344083/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1494971/2500000000 : ℝ)|^8339 ≤ (13344523/250000000000 : ℝ)^6291
        have hw : |(1494971/2500000000 : ℝ)|=(1494971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490340633/10000000000 : ℝ)|^8339 ≤ (45167628576631/100000000000000 : ℝ)^6291
        have hw : |(5490340633/10000000000 : ℝ)|=(5490340633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3177355547/5000000000 : ℝ)|^8339 ≤ (2193081344083/4000000000000 : ℝ)^6291
        have hw : |(3177355547/5000000000 : ℝ)|=(3177355547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s1_9 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (980677441/10000000000 : ℝ)*x 0 + (-881382159/2000000000 : ℝ)*x 1 + (6942142953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (980677441/10000000000 : ℝ)^8339 ≤ (920986255601/20000000000000 : ℝ)^6291 := by
    have hnat : (980677441 : ℕ)^8339*20000000000000^6291 ≤ 920986255601^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980677441 10000000000 920986255601 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (881382159/2000000000 : ℝ)^8339 ≤ (6750161228523/20000000000000 : ℝ)^6291 := by
    have hnat : (881382159 : ℕ)^8339*20000000000000^6291 ≤ 6750161228523^6291*2000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881382159 2000000000 6750161228523 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6942142953/10000000000 : ℝ)^8339 ≤ (30822131279759/50000000000000 : ℝ)^6291 := by
    have hnat : (6942142953 : ℕ)^8339*50000000000000^6291 ≤ 30822131279759^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6942142953 10000000000 30822131279759 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(980677441/10000000000 : ℝ), (-881382159/2000000000 : ℝ), (6942142953/10000000000 : ℝ)] ![(920986255601/20000000000000 : ℝ), (6750161228523/20000000000000 : ℝ), (30822131279759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(980677441/10000000000 : ℝ)|^8339 ≤ (920986255601/20000000000000 : ℝ)^6291
        have hw : |(980677441/10000000000 : ℝ)|=(980677441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-881382159/2000000000 : ℝ)|^8339 ≤ (6750161228523/20000000000000 : ℝ)^6291
        have hw : |(-881382159/2000000000 : ℝ)|=(881382159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6942142953/10000000000 : ℝ)|^8339 ≤ (30822131279759/50000000000000 : ℝ)^6291
        have hw : |(6942142953/10000000000 : ℝ)|=(6942142953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s1_10 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (980669553/10000000000 : ℝ)*x 0 + (1735531087/2500000000 : ℝ)*x 1 + (-4406937203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (980669553/10000000000 : ℝ)^8339 ≤ (4604882180707/100000000000000 : ℝ)^6291 := by
    have hnat : (980669553 : ℕ)^8339*100000000000000^6291 ≤ 4604882180707^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980669553 10000000000 4604882180707 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1735531087/2500000000 : ℝ)^8339 ≤ (2465761742809/4000000000000 : ℝ)^6291 := by
    have hnat : (1735531087 : ℕ)^8339*4000000000000^6291 ≤ 2465761742809^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1735531087 2500000000 2465761742809 4000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4406937203/10000000000 : ℝ)^8339 ≤ (16875537116153/50000000000000 : ℝ)^6291 := by
    have hnat : (4406937203 : ℕ)^8339*50000000000000^6291 ≤ 16875537116153^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4406937203 10000000000 16875537116153 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(980669553/10000000000 : ℝ), (1735531087/2500000000 : ℝ), (-4406937203/10000000000 : ℝ)] ![(4604882180707/100000000000000 : ℝ), (2465761742809/4000000000000 : ℝ), (16875537116153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(980669553/10000000000 : ℝ)|^8339 ≤ (4604882180707/100000000000000 : ℝ)^6291
        have hw : |(980669553/10000000000 : ℝ)|=(980669553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1735531087/2500000000 : ℝ)|^8339 ≤ (2465761742809/4000000000000 : ℝ)^6291
        have hw : |(1735531087/2500000000 : ℝ)|=(1735531087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4406937203/10000000000 : ℝ)|^8339 ≤ (16875537116153/50000000000000 : ℝ)^6291
        have hw : |(-4406937203/10000000000 : ℝ)|=(4406937203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s1_11 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (957732039/5000000000 : ℝ)*x 0 + (5811012073/10000000000 : ℝ)*x 1 + (5020609609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (957732039/5000000000 : ℝ)^8339 ≤ (11184647856479/100000000000000 : ℝ)^6291 := by
    have hnat : (957732039 : ℕ)^8339*100000000000000^6291 ≤ 11184647856479^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957732039 5000000000 11184647856479 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5811012073/10000000000 : ℝ)^8339 ≤ (24348671013937/50000000000000 : ℝ)^6291 := by
    have hnat : (5811012073 : ℕ)^8339*50000000000000^6291 ≤ 24348671013937^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5811012073 10000000000 24348671013937 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5020609609/10000000000 : ℝ)^8339 ≤ (20059005052799/50000000000000 : ℝ)^6291 := by
    have hnat : (5020609609 : ℕ)^8339*50000000000000^6291 ≤ 20059005052799^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5020609609 10000000000 20059005052799 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(957732039/5000000000 : ℝ), (5811012073/10000000000 : ℝ), (5020609609/10000000000 : ℝ)] ![(11184647856479/100000000000000 : ℝ), (24348671013937/50000000000000 : ℝ), (20059005052799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(957732039/5000000000 : ℝ)|^8339 ≤ (11184647856479/100000000000000 : ℝ)^6291
        have hw : |(957732039/5000000000 : ℝ)|=(957732039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5811012073/10000000000 : ℝ)|^8339 ≤ (24348671013937/50000000000000 : ℝ)^6291
        have hw : |(5811012073/10000000000 : ℝ)|=(5811012073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5020609609/10000000000 : ℝ)|^8339 ≤ (20059005052799/50000000000000 : ℝ)^6291
        have hw : |(5020609609/10000000000 : ℝ)|=(5020609609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1146_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (139/500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (43/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (709/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20419/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (139/500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (43/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (139/500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (43/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (139/500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (43/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (139/500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (43/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (139/500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (43/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (139/500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (43/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (43/10000 : ℝ) ^ (4169/1024 : ℝ) ≤ (5795701583/25000000000000000000 : ℝ) := by
    have hpowers : (43/10000 : ℝ)^4169 ≤ (5795701583/25000000000000000000 : ℝ)^1024 := by
      have hnat : (43 : ℕ)^4169*25000000000000000000^1024 ≤ 5795701583^1024*10000^4169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43 10000 5795701583 25000000000000000000 4169 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43/10000 : ℝ)) (X := (5795701583/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (139/500 : ℝ) ^ (4169/1024 : ℝ) ≤ (545187209465809703/100000000000000000000 : ℝ) := by
    have hpowers : (139/500 : ℝ)^4169 ≤ (545187209465809703/100000000000000000000 : ℝ)^1024 := by
      have hnat : (139 : ℕ)^4169*100000000000000000000^1024 ≤ 545187209465809703^1024*500^4169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        139 500 545187209465809703 100000000000000000000 4169 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (139/500 : ℝ)) (X := (545187209465809703/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000005795701583/12500000000000000000 : ℝ) ≤ (2500000000284711/2500000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (12500000005795701583/12500000000000000000 : ℝ)^1024 ≤ (2500000000284711/2500000000000000 : ℝ)^4169 := by
      have hnat : (12500000005795701583 : ℕ)^1024*2500000000000000^4169 ≤ 2500000000284711^4169*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000005795701583 12500000000000000000 2500000000284711 2500000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000000284711/2500000000000000 : ℝ)) (X := (12500000005795701583/12500000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20109037446529723207/20000000000000000000 : ℝ) ≤ (500668178641233/500000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (20109037446529723207/20000000000000000000 : ℝ)^1024 ≤ (500668178641233/500000000000000 : ℝ)^4169 := by
      have hnat : (20109037446529723207 : ℕ)^1024*500000000000000^4169 ≤ 500668178641233^4169*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20109037446529723207 20000000000000000000 500668178641233 500000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500668178641233/500000000000000 : ℝ)) (X := (20109037446529723207/20000000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50545187209465809703/50000000000000000000 : ℝ) ≤ (2506681786127619/2500000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (50545187209465809703/50000000000000000000 : ℝ)^1024 ≤ (2506681786127619/2500000000000000 : ℝ)^4169 := by
      have hnat : (50545187209465809703 : ℕ)^1024*2500000000000000^4169 ≤ 2506681786127619^4169*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50545187209465809703 50000000000000000000 2506681786127619 2500000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506681786127619/2500000000000000 : ℝ)) (X := (50545187209465809703/50000000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5795701583/25000000000000000000 : ℝ) ≤ ((6842212683988008963/6842500000000000000 : ℝ)+2*(1670446460727/342125000000000 : ℝ)*(43/10000 : ℝ))^(4169/1024 : ℝ) := by
    rw [show (6842212683988008963/6842500000000000000 : ℝ)+2*(1670446460727/342125000000000 : ℝ)*(43/10000 : ℝ)=(2500000000284711/2500000000000000 : ℝ) by norm_num, show 1+2*(5795701583/25000000000000000000 : ℝ)=(12500000005795701583/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(545187209465809703/100000000000000000000 : ℝ)+(5795701583/25000000000000000000 : ℝ) ≤ ((6842212683988008963/6842500000000000000 : ℝ)+(1670446460727/342125000000000 : ℝ)*((139/500 : ℝ)+(43/10000 : ℝ)))^(4169/1024 : ℝ) := by
    rw [show (6842212683988008963/6842500000000000000 : ℝ)+(1670446460727/342125000000000 : ℝ)*((139/500 : ℝ)+(43/10000 : ℝ))=(500668178641233/500000000000000 : ℝ) by norm_num, show 1+(545187209465809703/100000000000000000000 : ℝ)+(5795701583/25000000000000000000 : ℝ)=(20109037446529723207/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(545187209465809703/100000000000000000000 : ℝ) ≤ ((6842212683988008963/6842500000000000000 : ℝ)+2*(1670446460727/342125000000000 : ℝ)*(139/500 : ℝ))^(4169/1024 : ℝ) := by
    rw [show (6842212683988008963/6842500000000000000 : ℝ)+2*(1670446460727/342125000000000 : ℝ)*(139/500 : ℝ)=(2506681786127619/2500000000000000 : ℝ) by norm_num, show 1+2*(545187209465809703/100000000000000000000 : ℝ)=(50545187209465809703/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6842212683988008963/6842500000000000000 : ℝ)*(X 1 0+X 2 0)+(1670446460727/342125000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (43/10000 : ℝ)) (hi := (139/500 : ℝ)) (c := (6842212683988008963/6842500000000000000 : ℝ)) (alpha := (1670446460727/342125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6842212683988008963/6842500000000000000 : ℝ)*(X 0 1+X 2 1)+(1670446460727/342125000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (43/10000 : ℝ)) (hi := (139/500 : ℝ)) (c := (6842212683988008963/6842500000000000000 : ℝ)) (alpha := (1670446460727/342125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6842212683988008963/6842500000000000000 : ℝ)*(X 0 2+X 1 2)+(1670446460727/342125000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (43/10000 : ℝ)) (hi := (139/500 : ℝ)) (c := (6842212683988008963/6842500000000000000 : ℝ)) (alpha := (1670446460727/342125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-104745883/500000000 : ℝ)*X 0 0+(5700445851/10000000000 : ℝ)*X 0 1+(1250775267/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((42335191/78125000 : ℝ)*X 1 0+(-154447939/625000000 : ℝ)*X 1 1+(5003100299/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5418906441/10000000000 : ℝ)*X 2 0+(5003098527/10000000000 : ℝ)*X 2 1+(-2471166681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2158549299/5000000000 : ℝ)*X 0 0+(735556197/2000000000 : ℝ)*X 0 1+(1266553993/2500000000 : ℝ)*X 0 2+(2158549299/5000000000 : ℝ)*X 1 0+(735556197/2000000000 : ℝ)*X 1 1+(1266553993/2500000000 : ℝ)*X 1 2+(2158549299/5000000000 : ℝ)*X 2 0+(735556197/2000000000 : ℝ)*X 2 1+(1266553993/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-419144581/2000000000 : ℝ)*X 0 0+(40100867/80000000 : ℝ)*X 0 1+(1422686777/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1310020419/2500000000 : ℝ)*X 1 0+(-1783516033/10000000000 : ℝ)*X 1 1+(711343849/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5240080277/10000000000 : ℝ)*X 2 0+(5690752643/10000000000 : ℝ)*X 2 1+(-1783515319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((539836403/1250000000 : ℝ)*X 0 0+(5047286837/10000000000 : ℝ)*X 0 1+(3697083079/10000000000 : ℝ)*X 0 2+(539836403/1250000000 : ℝ)*X 1 0+(5047286837/10000000000 : ℝ)*X 1 1+(3697083079/10000000000 : ℝ)*X 1 2+(539836403/1250000000 : ℝ)*X 2 0+(5047286837/10000000000 : ℝ)*X 2 1+(3697083079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((1494971/2500000000 : ℝ)*X 0 0+(5490340633/10000000000 : ℝ)*X 0 1+(3177355547/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((980677441/10000000000 : ℝ)*X 1 0+(-881382159/2000000000 : ℝ)*X 1 1+(6942142953/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((980669553/10000000000 : ℝ)*X 2 0+(1735531087/2500000000 : ℝ)*X 2 1+(-4406937203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((957732039/5000000000 : ℝ)*X 0 0+(5811012073/10000000000 : ℝ)*X 0 1+(5020609609/10000000000 : ℝ)*X 0 2+(957732039/5000000000 : ℝ)*X 1 0+(5811012073/10000000000 : ℝ)*X 1 1+(5020609609/10000000000 : ℝ)*X 1 2+(957732039/5000000000 : ℝ)*X 2 0+(5811012073/10000000000 : ℝ)*X 2 1+(5020609609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (104751178269927069578372853/17106250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (164571401/100000000000000 : ℝ)*(lower2) + (53856280371941/5000000000000 : ℝ)*(major0) + (53856280371941/5000000000000 : ℝ)*(major1) + (53856280371941/5000000000000 : ℝ)*(major2) + (11203219589717/781250000000 : ℝ)*(sp0) + (1434011458684309/100000000000000 : ℝ)*(sp1) + (22406402515511/1562500000000 : ℝ)*(sp2) + (720235100138357/100000000000000 : ℝ)*(sp3) + (181434319/6250000000000 : ℝ)*(sp4) + (1513527531/50000000000000 : ℝ)*(sp5) + (4511414159/100000000000000 : ℝ)*(sp6) + (524693509/100000000000000 : ℝ)*(sp9) + (738026017/100000000000000 : ℝ)*(sp10) + (900187671/100000000000000 : ℝ)*(sp11) + (720236000326027/100000000000000 : ℝ)*(f.failure) + (17925187630411/1250000000000 : ℝ)*(f.sum) + (353077423101/106914062500000000000000000 : ℝ)*base66 + (101605528504497183/34212500000000000000000000000000 : ℝ)*base67 + (73038787605209683/34212500000000000000000000000000 : ℝ)*base69 + (238775975335484683/34212500000000000000000000000000 : ℝ)*base71 + (28393300495323/13685000000000000000000000000 : ℝ)*base74 + (30603464723159683/34212500000000000000000000000000 : ℝ)*base75 + (108931734135297183/34212500000000000000000000000000 : ℝ)*base77 + (10873233185184683/34212500000000000000000000000000 : ℝ)*base79 + (29719822250483/13685000000000000000000000000 : ℝ)*base82 + (88668507/10000000000000000000000 : ℝ)*base90 + (88668507/10000000000000000000000 : ℝ)*base92 + (88668507/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2026964397332258056224032829/342125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1107627485026539/100000000000000 : ℝ)*(major0) + (1107627485026539/100000000000000 : ℝ)*(major1) + (1107627485026539/100000000000000 : ℝ)*(major2) + (76381359/1562500000000 : ℝ)*(sp1) + (7991816089/100000000000000 : ℝ)*(sp2) + (30688869/3125000000000 : ℝ)*(sp3) + (147461941576159/10000000000000 : ℝ)*(sp4) + (737308988683331/50000000000000 : ℝ)*(sp5) + (737307614000093/50000000000000 : ℝ)*(sp6) + (370314434172393/50000000000000 : ℝ)*(sp7) + (1911996717/50000000000000 : ℝ)*(sp8) + (373981387/100000000000000 : ℝ)*(sp9) + (19938749/100000000000000 : ℝ)*(sp10) + (336484351/20000000000000 : ℝ)*(sp11) + (740631532810349/100000000000000 : ℝ)*(f.failure) + (92163952484689/6250000000000 : ℝ)*(f.sum) + (6681601316839/8553125000000000000000000000 : ℝ)*base65 + (1820154104573679057/684250000000000000000000000000000 : ℝ)*base67 + (4462714650352679057/684250000000000000000000000000000 : ℝ)*base69 + (94733695349320943/684250000000000000000000000000000 : ℝ)*base72 + (73085092089531/34212500000000000000000000000 : ℝ)*base73 + (390300709835070943/684250000000000000000000000000000 : ℝ)*base76 + (4623331167471429057/684250000000000000000000000000000 : ℝ)*base77 + (1913463100474429057/684250000000000000000000000000000 : ℝ)*base79 + (66280226231463/68425000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6353891/10000000000000000000000 : ℝ)*base89 + (6353891/10000000000000000000000 : ℝ)*base91 + (6353891/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1146_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (139/500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (43/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (709/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20419/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1146_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1146_s2_0 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-429587803/2000000000 : ℝ)*x 0 + (2755023569/5000000000 : ℝ)*x 1 + (5159780361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429587803/2000000000 : ℝ)^8339 ≤ (13018633858179/100000000000000 : ℝ)^6291 := by
    have hnat : (429587803 : ℕ)^8339*100000000000000^6291 ≤ 13018633858179^6291*2000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429587803 2000000000 13018633858179 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2755023569/5000000000 : ℝ)^8339 ≤ (5672831473857/12500000000000 : ℝ)^6291 := by
    have hnat : (2755023569 : ℕ)^8339*12500000000000^6291 ≤ 5672831473857^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755023569 5000000000 5672831473857 12500000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5159780361/10000000000 : ℝ)^8339 ≤ (5199839291639/12500000000000 : ℝ)^6291 := by
    have hnat : (5159780361 : ℕ)^8339*12500000000000^6291 ≤ 5199839291639^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5159780361 10000000000 5199839291639 12500000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-429587803/2000000000 : ℝ), (2755023569/5000000000 : ℝ), (5159780361/10000000000 : ℝ)] ![(13018633858179/100000000000000 : ℝ), (5672831473857/12500000000000 : ℝ), (5199839291639/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-429587803/2000000000 : ℝ)|^8339 ≤ (13018633858179/100000000000000 : ℝ)^6291
        have hw : |(-429587803/2000000000 : ℝ)|=(429587803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2755023569/5000000000 : ℝ)|^8339 ≤ (5672831473857/12500000000000 : ℝ)^6291
        have hw : |(2755023569/5000000000 : ℝ)|=(2755023569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5159780361/10000000000 : ℝ)|^8339 ≤ (5199839291639/12500000000000 : ℝ)^6291
        have hw : |(5159780361/10000000000 : ℝ)|=(5159780361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s2_1 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2686845923/5000000000 : ℝ)*x 0 + (-2330014331/10000000000 : ℝ)*x 1 + (322486407/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686845923/5000000000 : ℝ)^8339 ≤ (43900003759573/100000000000000 : ℝ)^6291 := by
    have hnat : (2686845923 : ℕ)^8339*100000000000000^6291 ≤ 43900003759573^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686845923 5000000000 43900003759573 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2330014331/10000000000 : ℝ)^8339 ≤ (7250629454809/50000000000000 : ℝ)^6291 := by
    have hnat : (2330014331 : ℕ)^8339*50000000000000^6291 ≤ 7250629454809^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2330014331 10000000000 7250629454809 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (322486407/625000000 : ℝ)^8339 ≤ (10399684330043/25000000000000 : ℝ)^6291 := by
    have hnat : (322486407 : ℕ)^8339*25000000000000^6291 ≤ 10399684330043^6291*625000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322486407 625000000 10399684330043 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686845923/5000000000 : ℝ), (-2330014331/10000000000 : ℝ), (322486407/625000000 : ℝ)] ![(43900003759573/100000000000000 : ℝ), (7250629454809/50000000000000 : ℝ), (10399684330043/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686845923/5000000000 : ℝ)|^8339 ≤ (43900003759573/100000000000000 : ℝ)^6291
        have hw : |(2686845923/5000000000 : ℝ)|=(2686845923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2330014331/10000000000 : ℝ)|^8339 ≤ (7250629454809/50000000000000 : ℝ)^6291
        have hw : |(-2330014331/10000000000 : ℝ)|=(2330014331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(322486407/625000000 : ℝ)|^8339 ≤ (10399684330043/25000000000000 : ℝ)^6291
        have hw : |(322486407/625000000 : ℝ)|=(322486407/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s2_2 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1343422973/2500000000 : ℝ)*x 0 + (1031956457/2000000000 : ℝ)*x 1 + (-2330014563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343422973/2500000000 : ℝ)^8339 ≤ (8780000851541/20000000000000 : ℝ)^6291 := by
    have hnat : (1343422973 : ℕ)^8339*20000000000000^6291 ≤ 8780000851541^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343422973 2500000000 8780000851541 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031956457/2000000000 : ℝ)^8339 ≤ (20799367447147/50000000000000 : ℝ)^6291 := by
    have hnat : (1031956457 : ℕ)^8339*50000000000000^6291 ≤ 20799367447147^6291*2000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031956457 2000000000 20799367447147 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2330014563/10000000000 : ℝ)^8339 ≤ (7250630411781/50000000000000 : ℝ)^6291 := by
    have hnat : (2330014563 : ℕ)^8339*50000000000000^6291 ≤ 7250630411781^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2330014563 10000000000 7250630411781 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343422973/2500000000 : ℝ), (1031956457/2000000000 : ℝ), (-2330014563/10000000000 : ℝ)] ![(8780000851541/20000000000000 : ℝ), (20799367447147/50000000000000 : ℝ), (7250630411781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343422973/2500000000 : ℝ)|^8339 ≤ (8780000851541/20000000000000 : ℝ)^6291
        have hw : |(1343422973/2500000000 : ℝ)|=(1343422973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031956457/2000000000 : ℝ)|^8339 ≤ (20799367447147/50000000000000 : ℝ)^6291
        have hw : |(1031956457/2000000000 : ℝ)|=(1031956457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2330014563/10000000000 : ℝ)|^8339 ≤ (7250630411781/50000000000000 : ℝ)^6291
        have hw : |(-2330014563/10000000000 : ℝ)|=(2330014563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s2_3 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4353482423/10000000000 : ℝ)*x 0 + (4018614291/10000000000 : ℝ)*x 1 + (2358001471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353482423/10000000000 : ℝ)^8339 ≤ (16604741945853/50000000000000 : ℝ)^6291 := by
    have hnat : (4353482423 : ℕ)^8339*50000000000000^6291 ≤ 16604741945853^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353482423 10000000000 16604741945853 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4018614291/10000000000 : ℝ)^8339 ≤ (7466646425241/25000000000000 : ℝ)^6291 := by
    have hnat : (4018614291 : ℕ)^8339*25000000000000^6291 ≤ 7466646425241^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4018614291 10000000000 7466646425241 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2358001471/5000000000 : ℝ)^8339 ≤ (4615491299713/12500000000000 : ℝ)^6291 := by
    have hnat : (2358001471 : ℕ)^8339*12500000000000^6291 ≤ 4615491299713^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2358001471 5000000000 4615491299713 12500000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353482423/10000000000 : ℝ), (4018614291/10000000000 : ℝ), (2358001471/5000000000 : ℝ)] ![(16604741945853/50000000000000 : ℝ), (7466646425241/25000000000000 : ℝ), (4615491299713/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353482423/10000000000 : ℝ)|^8339 ≤ (16604741945853/50000000000000 : ℝ)^6291
        have hw : |(4353482423/10000000000 : ℝ)|=(4353482423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4018614291/10000000000 : ℝ)|^8339 ≤ (7466646425241/25000000000000 : ℝ)^6291
        have hw : |(4018614291/10000000000 : ℝ)|=(4018614291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2358001471/5000000000 : ℝ)|^8339 ≤ (4615491299713/12500000000000 : ℝ)^6291
        have hw : |(2358001471/5000000000 : ℝ)|=(2358001471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s2_4 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1074020283/5000000000 : ℝ)*x 0 + (258109453/500000000 : ℝ)*x 1 + (5507614309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074020283/5000000000 : ℝ)^8339 ≤ (13019449736327/100000000000000 : ℝ)^6291 := by
    have hnat : (1074020283 : ℕ)^8339*100000000000000^6291 ≤ 13019449736327^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074020283 5000000000 13019449736327 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258109453/500000000 : ℝ)^8339 ≤ (8324891458951/20000000000000 : ℝ)^6291 := by
    have hnat : (258109453 : ℕ)^8339*20000000000000^6291 ≤ 8324891458951^6291*500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258109453 500000000 8324891458951 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5507614309/10000000000 : ℝ)^8339 ≤ (11339023236053/25000000000000 : ℝ)^6291 := by
    have hnat : (5507614309 : ℕ)^8339*25000000000000^6291 ≤ 11339023236053^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507614309 10000000000 11339023236053 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1074020283/5000000000 : ℝ), (258109453/500000000 : ℝ), (5507614309/10000000000 : ℝ)] ![(13019449736327/100000000000000 : ℝ), (8324891458951/20000000000000 : ℝ), (11339023236053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1074020283/5000000000 : ℝ)|^8339 ≤ (13019449736327/100000000000000 : ℝ)^6291
        have hw : |(-1074020283/5000000000 : ℝ)|=(1074020283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258109453/500000000 : ℝ)|^8339 ≤ (8324891458951/20000000000000 : ℝ)^6291
        have hw : |(258109453/500000000 : ℝ)|=(258109453/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5507614309/10000000000 : ℝ)|^8339 ≤ (11339023236053/25000000000000 : ℝ)^6291
        have hw : |(5507614309/10000000000 : ℝ)|=(5507614309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s2_5 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1321199067/2500000000 : ℝ)*x 0 + (-495545091/2500000000 : ℝ)*x 1 + (5507615023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321199067/2500000000 : ℝ)^8339 ≤ (5367495048561/12500000000000 : ℝ)^6291 := by
    have hnat : (1321199067 : ℕ)^8339*12500000000000^6291 ≤ 5367495048561^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321199067 2500000000 5367495048561 12500000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (495545091/2500000000 : ℝ)^8339 ≤ (11703938858897/100000000000000 : ℝ)^6291 := by
    have hnat : (495545091 : ℕ)^8339*100000000000000^6291 ≤ 11703938858897^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495545091 2500000000 11703938858897 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5507615023/10000000000 : ℝ)^8339 ≤ (2834756296143/6250000000000 : ℝ)^6291 := by
    have hnat : (5507615023 : ℕ)^8339*6250000000000^6291 ≤ 2834756296143^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507615023 10000000000 2834756296143 6250000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321199067/2500000000 : ℝ), (-495545091/2500000000 : ℝ), (5507615023/10000000000 : ℝ)] ![(5367495048561/12500000000000 : ℝ), (11703938858897/100000000000000 : ℝ), (2834756296143/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321199067/2500000000 : ℝ)|^8339 ≤ (5367495048561/12500000000000 : ℝ)^6291
        have hw : |(1321199067/2500000000 : ℝ)|=(1321199067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-495545091/2500000000 : ℝ)|^8339 ≤ (11703938858897/100000000000000 : ℝ)^6291
        have hw : |(-495545091/2500000000 : ℝ)|=(495545091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5507615023/10000000000 : ℝ)|^8339 ≤ (2834756296143/6250000000000 : ℝ)^6291
        have hw : |(5507615023/10000000000 : ℝ)|=(5507615023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s2_6 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5284794693/10000000000 : ℝ)*x 0 + (5507614789/10000000000 : ℝ)*x 1 + (-991091429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284794693/10000000000 : ℝ)^8339 ≤ (5367492928159/12500000000000 : ℝ)^6291 := by
    have hnat : (5284794693 : ℕ)^8339*12500000000000^6291 ≤ 5367492928159^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284794693 10000000000 5367492928159 12500000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5507614789/10000000000 : ℝ)^8339 ≤ (45356098183927/100000000000000 : ℝ)^6291 := by
    have hnat : (5507614789 : ℕ)^8339*100000000000000^6291 ≤ 45356098183927^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507614789 10000000000 45356098183927 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (991091429/5000000000 : ℝ)^8339 ≤ (2925989594723/25000000000000 : ℝ)^6291 := by
    have hnat : (991091429 : ℕ)^8339*25000000000000^6291 ≤ 2925989594723^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991091429 5000000000 2925989594723 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284794693/10000000000 : ℝ), (5507614789/10000000000 : ℝ), (-991091429/5000000000 : ℝ)] ![(5367492928159/12500000000000 : ℝ), (45356098183927/100000000000000 : ℝ), (2925989594723/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284794693/10000000000 : ℝ)|^8339 ≤ (5367492928159/12500000000000 : ℝ)^6291
        have hw : |(5284794693/10000000000 : ℝ)|=(5284794693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5507614789/10000000000 : ℝ)|^8339 ≤ (45356098183927/100000000000000 : ℝ)^6291
        have hw : |(5507614789/10000000000 : ℝ)|=(5507614789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-991091429/5000000000 : ℝ)|^8339 ≤ (2925989594723/25000000000000 : ℝ)^6291
        have hw : |(-991091429/5000000000 : ℝ)|=(991091429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s2_7 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870736719/2000000000 : ℝ)*x 0 + (4711208981/10000000000 : ℝ)*x 1 + (502932043/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870736719/2000000000 : ℝ)^8339 ≤ (1037859939893/3125000000000 : ℝ)^6291 := by
    have hnat : (870736719 : ℕ)^8339*3125000000000^6291 ≤ 1037859939893^6291*2000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870736719 2000000000 1037859939893 3125000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4711208981/10000000000 : ℝ)^8339 ≤ (3687418524601/10000000000000 : ℝ)^6291 := by
    have hnat : (4711208981 : ℕ)^8339*10000000000000^6291 ≤ 3687418524601^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4711208981 10000000000 3687418524601 10000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502932043/1250000000 : ℝ)^8339 ≤ (5982859333737/20000000000000 : ℝ)^6291 := by
    have hnat : (502932043 : ℕ)^8339*20000000000000^6291 ≤ 5982859333737^6291*1250000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502932043 1250000000 5982859333737 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870736719/2000000000 : ℝ), (4711208981/10000000000 : ℝ), (502932043/1250000000 : ℝ)] ![(1037859939893/3125000000000 : ℝ), (3687418524601/10000000000000 : ℝ), (5982859333737/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870736719/2000000000 : ℝ)|^8339 ≤ (1037859939893/3125000000000 : ℝ)^6291
        have hw : |(870736719/2000000000 : ℝ)|=(870736719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4711208981/10000000000 : ℝ)|^8339 ≤ (3687418524601/10000000000000 : ℝ)^6291
        have hw : |(4711208981/10000000000 : ℝ)|=(4711208981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(502932043/1250000000 : ℝ)|^8339 ≤ (5982859333737/20000000000000 : ℝ)^6291
        have hw : |(502932043/1250000000 : ℝ)|=(502932043/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1146_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20419/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (709/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (284/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16491/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20419/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (709/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20419/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (709/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20419/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (709/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20419/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (709/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20419/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (709/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20419/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (709/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (709/12500 : ℝ) ^ (4169/1024 : ℝ) ≤ (105441099360813/12500000000000000000 : ℝ) := by
    have hpowers : (709/12500 : ℝ)^4169 ≤ (105441099360813/12500000000000000000 : ℝ)^1024 := by
      have hnat : (709 : ℕ)^4169*12500000000000000000^1024 ≤ 105441099360813^1024*12500^4169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        709 12500 105441099360813 12500000000000000000 4169 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (709/12500 : ℝ)) (X := (105441099360813/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20419/100000 : ℝ) ^ (4169/1024 : ℝ) ≤ (15522114427613623/10000000000000000000 : ℝ) := by
    have hpowers : (20419/100000 : ℝ)^4169 ≤ (15522114427613623/10000000000000000000 : ℝ)^1024 := by
      have hnat : (20419 : ℕ)^4169*10000000000000000000^1024 ≤ 15522114427613623^1024*100000^4169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20419 100000 15522114427613623 10000000000000000000 4169 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20419/100000 : ℝ)) (X := (15522114427613623/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250105441099360813/6250000000000000000 : ℝ) ≤ (10000041437658407/10000000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (6250105441099360813/6250000000000000000 : ℝ)^1024 ≤ (10000041437658407/10000000000000000 : ℝ)^4169 := by
      have hnat : (6250105441099360813 : ℕ)^1024*10000000000000000^4169 ≤ 10000041437658407^4169*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250105441099360813 6250000000000000000 10000041437658407 10000000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000041437658407/10000000000000000 : ℝ)) (X := (6250105441099360813/6250000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50078032336535511367/50000000000000000000 : ℝ) ≤ (2500957761077917/2500000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (50078032336535511367/50000000000000000000 : ℝ)^1024 ≤ (2500957761077917/2500000000000000 : ℝ)^4169 := by
      have hnat : (50078032336535511367 : ℕ)^1024*2500000000000000^4169 ≤ 2500957761077917^4169*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50078032336535511367 50000000000000000000 2500957761077917 2500000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500957761077917/2500000000000000 : ℝ)) (X := (50078032336535511367/50000000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5015522114427613623/5000000000000000000 : ℝ) ≤ (10007620650964929/10000000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (5015522114427613623/5000000000000000000 : ℝ)^1024 ≤ (10007620650964929/10000000000000000 : ℝ)^4169 := by
      have hnat : (5015522114427613623 : ℕ)^1024*10000000000000000^4169 ≤ 10007620650964929^4169*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5015522114427613623 5000000000000000000 10007620650964929 10000000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007620650964929/10000000000000000 : ℝ)) (X := (5015522114427613623/5000000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(105441099360813/12500000000000000000 : ℝ) ≤ ((29485524356654787049/29494000000000000000 : ℝ)+2*(3789606653261/1474700000000000 : ℝ)*(709/12500 : ℝ))^(4169/1024 : ℝ) := by
    rw [show (29485524356654787049/29494000000000000000 : ℝ)+2*(3789606653261/1474700000000000 : ℝ)*(709/12500 : ℝ)=(10000041437658407/10000000000000000 : ℝ) by norm_num, show 1+2*(105441099360813/12500000000000000000 : ℝ)=(6250105441099360813/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15522114427613623/10000000000000000000 : ℝ)+(105441099360813/12500000000000000000 : ℝ) ≤ ((29485524356654787049/29494000000000000000 : ℝ)+(3789606653261/1474700000000000 : ℝ)*((20419/100000 : ℝ)+(709/12500 : ℝ)))^(4169/1024 : ℝ) := by
    rw [show (29485524356654787049/29494000000000000000 : ℝ)+(3789606653261/1474700000000000 : ℝ)*((20419/100000 : ℝ)+(709/12500 : ℝ))=(2500957761077917/2500000000000000 : ℝ) by norm_num, show 1+(15522114427613623/10000000000000000000 : ℝ)+(105441099360813/12500000000000000000 : ℝ)=(50078032336535511367/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15522114427613623/10000000000000000000 : ℝ) ≤ ((29485524356654787049/29494000000000000000 : ℝ)+2*(3789606653261/1474700000000000 : ℝ)*(20419/100000 : ℝ))^(4169/1024 : ℝ) := by
    rw [show (29485524356654787049/29494000000000000000 : ℝ)+2*(3789606653261/1474700000000000 : ℝ)*(20419/100000 : ℝ)=(10007620650964929/10000000000000000 : ℝ) by norm_num, show 1+2*(15522114427613623/10000000000000000000 : ℝ)=(5015522114427613623/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29485524356654787049/29494000000000000000 : ℝ)*(X 1 0+X 2 0)+(3789606653261/1474700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (709/12500 : ℝ)) (hi := (20419/100000 : ℝ)) (c := (29485524356654787049/29494000000000000000 : ℝ)) (alpha := (3789606653261/1474700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29485524356654787049/29494000000000000000 : ℝ)*(X 0 1+X 2 1)+(3789606653261/1474700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (709/12500 : ℝ)) (hi := (20419/100000 : ℝ)) (c := (29485524356654787049/29494000000000000000 : ℝ)) (alpha := (3789606653261/1474700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29485524356654787049/29494000000000000000 : ℝ)*(X 0 2+X 1 2)+(3789606653261/1474700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (709/12500 : ℝ)) (hi := (20419/100000 : ℝ)) (c := (29485524356654787049/29494000000000000000 : ℝ)) (alpha := (3789606653261/1474700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-429587803/2000000000 : ℝ)*X 0 0+(2755023569/5000000000 : ℝ)*X 0 1+(5159780361/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2686845923/5000000000 : ℝ)*X 1 0+(-2330014331/10000000000 : ℝ)*X 1 1+(322486407/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1343422973/2500000000 : ℝ)*X 2 0+(1031956457/2000000000 : ℝ)*X 2 1+(-2330014563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4353482423/10000000000 : ℝ)*X 0 0+(4018614291/10000000000 : ℝ)*X 0 1+(2358001471/5000000000 : ℝ)*X 0 2+(4353482423/10000000000 : ℝ)*X 1 0+(4018614291/10000000000 : ℝ)*X 1 1+(2358001471/5000000000 : ℝ)*X 1 2+(4353482423/10000000000 : ℝ)*X 2 0+(4018614291/10000000000 : ℝ)*X 2 1+(2358001471/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1074020283/5000000000 : ℝ)*X 0 0+(258109453/500000000 : ℝ)*X 0 1+(5507614309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1321199067/2500000000 : ℝ)*X 1 0+(-495545091/2500000000 : ℝ)*X 1 1+(5507615023/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5284794693/10000000000 : ℝ)*X 2 0+(5507614789/10000000000 : ℝ)*X 2 1+(-991091429/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((870736719/2000000000 : ℝ)*X 0 0+(4711208981/10000000000 : ℝ)*X 0 1+(502932043/1250000000 : ℝ)*X 0 2+(870736719/2000000000 : ℝ)*X 1 0+(4711208981/10000000000 : ℝ)*X 1 1+(502932043/1250000000 : ℝ)*X 1 2+(870736719/2000000000 : ℝ)*X 2 0+(4711208981/10000000000 : ℝ)*X 2 1+(502932043/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3092574730946510463604430391/294940000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1233730893/100000000000000 : ℝ)*(base19) + (924848681/100000000000000 : ℝ)*(base23) + (403032381/100000000000000 : ℝ)*(upper3) + (179116861/100000000000000 : ℝ)*(upper4) + (6019121/100000000000000 : ℝ)*(upper5) + (428895518403147/20000000000000 : ℝ)*(major0) + (428895518403147/20000000000000 : ℝ)*(major1) + (428895518403147/20000000000000 : ℝ)*(major2) + (285499487541619/10000000000000 : ℝ)*(sp0) + (571003375580969/20000000000000 : ℝ)*(sp1) + (178438574174191/6250000000000 : ℝ)*(sp2) + (716963385465129/50000000000000 : ℝ)*(sp3) + (23236219547/100000000000000 : ℝ)*(sp4) + (1990390181/20000000000000 : ℝ)*(sp7) + (358484180720291/25000000000000 : ℝ)*(f.failure) + (1427509055817869/50000000000000 : ℝ)*(f.sum) + (72313142693/921687500000000000000000000 : ℝ)*base65 + (815205599284543203/589880000000000000000000000000000 : ℝ)*base67 + (3771838680710063203/589880000000000000000000000000000 : ℝ)*base69 + (3770541233751263203/589880000000000000000000000000000 : ℝ)*base71 + (21876314727069/14747000000000000000000000000 : ℝ)*base74 + (5338815463856696797/589880000000000000000000000000000 : ℝ)*base76 + (4232207228101103203/589880000000000000000000000000000 : ℝ)*base77 + (403594381565056797/589880000000000000000000000000000 : ℝ)*base80 + (53659992390851/14747000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (31041869/2500000000000000000000 : ℝ)*base89 + (31041869/2500000000000000000000 : ℝ)*base91 + (31041869/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8570919616308923702917729887/737350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (523654919/25000000000000 : ℝ)*(base19) + (753917557/50000000000000 : ℝ)*(base23) + (161367641/50000000000000 : ℝ)*(upper2) + (1170599/781250000000 : ℝ)*(upper3) + (336629591/100000000000000 : ℝ)*(upper5) + (1087246002031421/50000000000000 : ℝ)*(major0) + (1087246002031421/50000000000000 : ℝ)*(major1) + (1087246002031421/50000000000000 : ℝ)*(major2) + (14343807343/50000000000000 : ℝ)*(sp1) + (2197480083/25000000000000 : ℝ)*(sp2) + (2894977316353119/100000000000000 : ℝ)*(sp4) + (723736633529689/25000000000000 : ℝ)*(sp5) + (1447483509298837/50000000000000 : ℝ)*(sp6) + (363501576076889/25000000000000 : ℝ)*(sp7) + (363501576076889/25000000000000 : ℝ)*(f.failure) + (2894977316353119/100000000000000 : ℝ)*(f.sum) + (71723837034313/18433750000000000000000000000 : ℝ)*base65 + (3368629507587713371/1474700000000000000000000000000000 : ℝ)*base68 + (7518695531675013371/1474700000000000000000000000000000 : ℝ)*base70 + (2267735523074686629/1474700000000000000000000000000000 : ℝ)*base71 + (26729454833263/18433750000000000000000000000 : ℝ)*base73 + (3500760064904686629/1474700000000000000000000000000000 : ℝ)*base75 + (2932114576596713371/1474700000000000000000000000000000 : ℝ)*base78 + (7762706482557913371/1474700000000000000000000000000000 : ℝ)*base80 + (20127745059301/36867500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (19197751/2500000000000000000000 : ℝ)*base89 + (19197751/2500000000000000000000 : ℝ)*base91 + (19197751/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1146_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20419/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (709/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (284/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16491/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1146_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1146_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (284/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16491/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1146_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1146_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1146_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (284/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16491/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1146_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

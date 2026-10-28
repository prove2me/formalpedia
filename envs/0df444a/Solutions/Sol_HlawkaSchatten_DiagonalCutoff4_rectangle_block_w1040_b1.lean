-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1040_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:46:34.715205+00:00
-- url     : https://prove2.me/submissions/d2f4e6e8-08a6-48be-ae3e-c2f54030732a

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
theorem support_rectangle_w1040_s3_0 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-442305401/2000000000 : ℝ)*x 0 + (2720308881/5000000000 : ℝ)*x 1 + (5221494057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442305401/2000000000 : ℝ)^8233 ≤ (6709255523071/50000000000000 : ℝ)^6185 := by
    have hnat : (442305401 : ℕ)^8233*50000000000000^6185 ≤ 6709255523071^6185*2000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442305401 2000000000 6709255523071 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720308881/5000000000 : ℝ)^8233 ≤ (5559363744693/12500000000000 : ℝ)^6185 := by
    have hnat : (2720308881 : ℕ)^8233*12500000000000^6185 ≤ 5559363744693^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720308881 5000000000 5559363744693 12500000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5221494057/10000000000 : ℝ)^8233 ≤ (21053289493837/50000000000000 : ℝ)^6185 := by
    have hnat : (5221494057 : ℕ)^8233*50000000000000^6185 ≤ 21053289493837^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221494057 10000000000 21053289493837 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-442305401/2000000000 : ℝ), (2720308881/5000000000 : ℝ), (5221494057/10000000000 : ℝ)] ![(6709255523071/50000000000000 : ℝ), (5559363744693/12500000000000 : ℝ), (21053289493837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-442305401/2000000000 : ℝ)|^8233 ≤ (6709255523071/50000000000000 : ℝ)^6185
        have hw : |(-442305401/2000000000 : ℝ)|=(442305401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720308881/5000000000 : ℝ)|^8233 ≤ (5559363744693/12500000000000 : ℝ)^6185
        have hw : |(2720308881/5000000000 : ℝ)|=(2720308881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5221494057/10000000000 : ℝ)|^8233 ≤ (21053289493837/50000000000000 : ℝ)^6185
        have hw : |(5221494057/10000000000 : ℝ)|=(5221494057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s3_1 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1071273377/2000000000 : ℝ)*x 0 + (-2323810061/10000000000 : ℝ)*x 1 + (5221494253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071273377/2000000000 : ℝ)^8233 ≤ (5445062500463/12500000000000 : ℝ)^6185 := by
    have hnat : (1071273377 : ℕ)^8233*12500000000000^6185 ≤ 5445062500463^6185*2000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071273377 2000000000 5445062500463 12500000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2323810061/10000000000 : ℝ)^8233 ≤ (3583229721611/25000000000000 : ℝ)^6185 := by
    have hnat : (2323810061 : ℕ)^8233*25000000000000^6185 ≤ 3583229721611^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2323810061 10000000000 3583229721611 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5221494253/10000000000 : ℝ)^8233 ≤ (10526645272899/25000000000000 : ℝ)^6185 := by
    have hnat : (5221494253 : ℕ)^8233*25000000000000^6185 ≤ 10526645272899^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221494253 10000000000 10526645272899 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071273377/2000000000 : ℝ), (-2323810061/10000000000 : ℝ), (5221494253/10000000000 : ℝ)] ![(5445062500463/12500000000000 : ℝ), (3583229721611/25000000000000 : ℝ), (10526645272899/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071273377/2000000000 : ℝ)|^8233 ≤ (5445062500463/12500000000000 : ℝ)^6185
        have hw : |(1071273377/2000000000 : ℝ)|=(1071273377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2323810061/10000000000 : ℝ)|^8233 ≤ (3583229721611/25000000000000 : ℝ)^6185
        have hw : |(-2323810061/10000000000 : ℝ)|=(2323810061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5221494253/10000000000 : ℝ)|^8233 ≤ (10526645272899/25000000000000 : ℝ)^6185
        have hw : |(5221494253/10000000000 : ℝ)|=(5221494253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s3_2 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2678183469/5000000000 : ℝ)*x 0 + (5221494429/10000000000 : ℝ)*x 1 + (-1161904881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678183469/5000000000 : ℝ)^8233 ≤ (21780250288723/50000000000000 : ℝ)^6185 := by
    have hnat : (2678183469 : ℕ)^8233*50000000000000^6185 ≤ 21780250288723^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678183469 5000000000 21780250288723 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221494429/10000000000 : ℝ)^8233 ≤ (1315830718151/3125000000000 : ℝ)^6185 := by
    have hnat : (5221494429 : ℕ)^8233*3125000000000^6185 ≤ 1315830718151^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221494429 10000000000 1315830718151 3125000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1161904881/5000000000 : ℝ)^8233 ≤ (14332916431601/100000000000000 : ℝ)^6185 := by
    have hnat : (1161904881 : ℕ)^8233*100000000000000^6185 ≤ 14332916431601^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1161904881 5000000000 14332916431601 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678183469/5000000000 : ℝ), (5221494429/10000000000 : ℝ), (-1161904881/5000000000 : ℝ)] ![(21780250288723/50000000000000 : ℝ), (1315830718151/3125000000000 : ℝ), (14332916431601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678183469/5000000000 : ℝ)|^8233 ≤ (21780250288723/50000000000000 : ℝ)^6185
        have hw : |(2678183469/5000000000 : ℝ)|=(2678183469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221494429/10000000000 : ℝ)|^8233 ≤ (1315830718151/3125000000000 : ℝ)^6185
        have hw : |(5221494429/10000000000 : ℝ)|=(5221494429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1161904881/5000000000 : ℝ)|^8233 ≤ (14332916431601/100000000000000 : ℝ)^6185
        have hw : |(-1161904881/5000000000 : ℝ)|=(1161904881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s3_3 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4376229953/10000000000 : ℝ)*x 0 + (4167918087/10000000000 : ℝ)*x 1 + (4595153301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376229953/10000000000 : ℝ)^8233 ≤ (33285868090939/100000000000000 : ℝ)^6185 := by
    have hnat : (4376229953 : ℕ)^8233*100000000000000^6185 ≤ 33285868090939^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376229953 10000000000 33285868090939 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4167918087/10000000000 : ℝ)^8233 ≤ (15596796854343/50000000000000 : ℝ)^6185 := by
    have hnat : (4167918087 : ℕ)^8233*50000000000000^6185 ≤ 15596796854343^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167918087 10000000000 15596796854343 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4595153301/10000000000 : ℝ)^8233 ≤ (7104107637183/20000000000000 : ℝ)^6185 := by
    have hnat : (4595153301 : ℕ)^8233*20000000000000^6185 ≤ 7104107637183^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4595153301 10000000000 7104107637183 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376229953/10000000000 : ℝ), (4167918087/10000000000 : ℝ), (4595153301/10000000000 : ℝ)] ![(33285868090939/100000000000000 : ℝ), (15596796854343/50000000000000 : ℝ), (7104107637183/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376229953/10000000000 : ℝ)|^8233 ≤ (33285868090939/100000000000000 : ℝ)^6185
        have hw : |(4376229953/10000000000 : ℝ)|=(4376229953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4167918087/10000000000 : ℝ)|^8233 ≤ (15596796854343/50000000000000 : ℝ)^6185
        have hw : |(4167918087/10000000000 : ℝ)|=(4167918087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4595153301/10000000000 : ℝ)|^8233 ≤ (7104107637183/20000000000000 : ℝ)^6185
        have hw : |(4595153301/10000000000 : ℝ)|=(4595153301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s3_4 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1105775641/5000000000 : ℝ)*x 0 + (522241017/1000000000 : ℝ)*x 1 + (2719847981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1105775641/5000000000 : ℝ)^8233 ≤ (6709353561491/50000000000000 : ℝ)^6185 := by
    have hnat : (1105775641 : ℕ)^8233*50000000000000^6185 ≤ 6709353561491^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105775641 5000000000 6709353561491 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522241017/1000000000 : ℝ)^8233 ≤ (21058206550877/50000000000000 : ℝ)^6185 := by
    have hnat : (522241017 : ℕ)^8233*50000000000000^6185 ≤ 21058206550877^6185*1000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522241017 1000000000 21058206550877 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719847981/5000000000 : ℝ)^8233 ≤ (44464879752883/100000000000000 : ℝ)^6185 := by
    have hnat : (2719847981 : ℕ)^8233*100000000000000^6185 ≤ 44464879752883^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719847981 5000000000 44464879752883 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1105775641/5000000000 : ℝ), (522241017/1000000000 : ℝ), (2719847981/5000000000 : ℝ)] ![(6709353561491/50000000000000 : ℝ), (21058206550877/50000000000000 : ℝ), (44464879752883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1105775641/5000000000 : ℝ)|^8233 ≤ (6709353561491/50000000000000 : ℝ)^6185
        have hw : |(-1105775641/5000000000 : ℝ)|=(1105775641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522241017/1000000000 : ℝ)|^8233 ≤ (21058206550877/50000000000000 : ℝ)^6185
        have hw : |(522241017/1000000000 : ℝ)|=(522241017/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719847981/5000000000 : ℝ)|^8233 ≤ (44464879752883/100000000000000 : ℝ)^6185
        have hw : |(2719847981/5000000000 : ℝ)|=(2719847981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s3_5 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1325320787/2500000000 : ℝ)*x 0 + (-2105607663/10000000000 : ℝ)*x 1 + (543969647/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325320787/2500000000 : ℝ)^8233 ≤ (42965218237077/100000000000000 : ℝ)^6185 := by
    have hnat : (1325320787 : ℕ)^8233*100000000000000^6185 ≤ 42965218237077^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325320787 2500000000 42965218237077 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2105607663/10000000000 : ℝ)^8233 ≤ (12569896457867/100000000000000 : ℝ)^6185 := by
    have hnat : (2105607663 : ℕ)^8233*100000000000000^6185 ≤ 12569896457867^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105607663 10000000000 12569896457867 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543969647/1000000000 : ℝ)^8233 ≤ (4446488528033/10000000000000 : ℝ)^6185 := by
    have hnat : (543969647 : ℕ)^8233*10000000000000^6185 ≤ 4446488528033^6185*1000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543969647 1000000000 4446488528033 10000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325320787/2500000000 : ℝ), (-2105607663/10000000000 : ℝ), (543969647/1000000000 : ℝ)] ![(42965218237077/100000000000000 : ℝ), (12569896457867/100000000000000 : ℝ), (4446488528033/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325320787/2500000000 : ℝ)|^8233 ≤ (42965218237077/100000000000000 : ℝ)^6185
        have hw : |(1325320787/2500000000 : ℝ)|=(1325320787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2105607663/10000000000 : ℝ)|^8233 ≤ (12569896457867/100000000000000 : ℝ)^6185
        have hw : |(-2105607663/10000000000 : ℝ)|=(2105607663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543969647/1000000000 : ℝ)|^8233 ≤ (4446488528033/10000000000000 : ℝ)^6185
        have hw : |(543969647/1000000000 : ℝ)|=(543969647/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s3_6 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5301283/10000000 : ℝ)*x 0 + (1359924061/2500000000 : ℝ)*x 1 + (-84224327/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301283/10000000 : ℝ)^8233 ≤ (10741304160101/25000000000000 : ℝ)^6185 := by
    have hnat : (5301283 : ℕ)^8233*25000000000000^6185 ≤ 10741304160101^6185*10000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301283 10000000 10741304160101 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359924061/2500000000 : ℝ)^8233 ≤ (44464882821269/100000000000000 : ℝ)^6185 := by
    have hnat : (1359924061 : ℕ)^8233*100000000000000^6185 ≤ 44464882821269^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359924061 2500000000 44464882821269 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84224327/400000000 : ℝ)^8233 ≤ (2513980105289/20000000000000 : ℝ)^6185 := by
    have hnat : (84224327 : ℕ)^8233*20000000000000^6185 ≤ 2513980105289^6185*400000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84224327 400000000 2513980105289 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301283/10000000 : ℝ), (1359924061/2500000000 : ℝ), (-84224327/400000000 : ℝ)] ![(10741304160101/25000000000000 : ℝ), (44464882821269/100000000000000 : ℝ), (2513980105289/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301283/10000000 : ℝ)|^8233 ≤ (10741304160101/25000000000000 : ℝ)^6185
        have hw : |(5301283/10000000 : ℝ)|=(5301283/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359924061/2500000000 : ℝ)|^8233 ≤ (44464882821269/100000000000000 : ℝ)^6185
        have hw : |(1359924061/2500000000 : ℝ)|=(1359924061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-84224327/400000000 : ℝ)|^8233 ≤ (2513980105289/20000000000000 : ℝ)^6185
        have hw : |(-84224327/400000000 : ℝ)|=(84224327/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s3_7 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2188138269/5000000000 : ℝ)*x 0 + (2296684287/5000000000 : ℝ)*x 1 + (833942767/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188138269/5000000000 : ℝ)^8233 ≤ (33286339746577/100000000000000 : ℝ)^6185 := by
    have hnat : (2188138269 : ℕ)^8233*100000000000000^6185 ≤ 33286339746577^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188138269 5000000000 33286339746577 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2296684287/5000000000 : ℝ)^8233 ≤ (56803480421/160000000000 : ℝ)^6185 := by
    have hnat : (2296684287 : ℕ)^8233*160000000000^6185 ≤ 56803480421^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296684287 5000000000 56803480421 160000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (833942767/2000000000 : ℝ)^8233 ≤ (7802871243069/25000000000000 : ℝ)^6185 := by
    have hnat : (833942767 : ℕ)^8233*25000000000000^6185 ≤ 7802871243069^6185*2000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833942767 2000000000 7802871243069 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188138269/5000000000 : ℝ), (2296684287/5000000000 : ℝ), (833942767/2000000000 : ℝ)] ![(33286339746577/100000000000000 : ℝ), (56803480421/160000000000 : ℝ), (7802871243069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188138269/5000000000 : ℝ)|^8233 ≤ (33286339746577/100000000000000 : ℝ)^6185
        have hw : |(2188138269/5000000000 : ℝ)|=(2188138269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2296684287/5000000000 : ℝ)|^8233 ≤ (56803480421/160000000000 : ℝ)^6185
        have hw : |(2296684287/5000000000 : ℝ)|=(2296684287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(833942767/2000000000 : ℝ)|^8233 ≤ (7802871243069/25000000000000 : ℝ)^6185
        have hw : |(833942767/2000000000 : ℝ)|=(833942767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1040_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16827/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1073/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2577/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (467/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16827/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1073/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16827/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1073/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16827/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1073/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16827/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1073/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16827/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1073/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16827/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1073/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1073/12500 : ℝ) ^ (1029/256 : ℝ) ≤ (5175263452832053/100000000000000000000 : ℝ) := by
    have hpowers : (1073/12500 : ℝ)^1029 ≤ (5175263452832053/100000000000000000000 : ℝ)^256 := by
      have hnat : (1073 : ℕ)^1029*100000000000000000000^256 ≤ 5175263452832053^256*12500^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1073 12500 5175263452832053 100000000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1073/12500 : ℝ)) (X := (5175263452832053/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hpowhi : (16827/100000 : ℝ) ^ (1029/256 : ℝ) ≤ (3871504126590603/5000000000000000000 : ℝ) := by
    have hpowers : (16827/100000 : ℝ)^1029 ≤ (3871504126590603/5000000000000000000 : ℝ)^256 := by
      have hnat : (16827 : ℕ)^1029*5000000000000000000^256 ≤ 3871504126590603^256*100000^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16827 100000 3871504126590603 5000000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16827/100000 : ℝ)) (X := (3871504126590603/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005175263452832053/50000000000000000000 : ℝ) ≤ (2500064373952367/2500000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (50005175263452832053/50000000000000000000 : ℝ)^256 ≤ (2500064373952367/2500000000000000 : ℝ)^1029 := by
      have hnat : (50005175263452832053 : ℕ)^256*2500000000000000^1029 ≤ 2500064373952367^1029*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005175263452832053 50000000000000000000 2500064373952367 2500000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500064373952367/2500000000000000 : ℝ)) (X := (50005175263452832053/50000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100082605345984644113/100000000000000000000 : ℝ) ≤ (10002054461654669/10000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (100082605345984644113/100000000000000000000 : ℝ)^256 ≤ (10002054461654669/10000000000000000 : ℝ)^1029 := by
      have hnat : (100082605345984644113 : ℕ)^256*10000000000000000^1029 ≤ 10002054461654669^1029*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100082605345984644113 100000000000000000000 10002054461654669 10000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002054461654669/10000000000000000 : ℝ)) (X := (100082605345984644113/100000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (2503871504126590603/2500000000000000000 : ℝ) ≤ (1000385142749987/1000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (2503871504126590603/2500000000000000000 : ℝ)^256 ≤ (1000385142749987/1000000000000000 : ℝ)^1029 := by
      have hnat : (2503871504126590603 : ℕ)^256*1000000000000000^1029 ≤ 1000385142749987^1029*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2503871504126590603 2500000000000000000 1000385142749987 1000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000385142749987/1000000000000000 : ℝ)) (X := (2503871504126590603/2500000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5175263452832053/100000000000000000000 : ℝ) ≤ ((20600318057081758489/20607500000000000000 : ℝ)+2*(1796965845201/824300000000000 : ℝ)*(1073/12500 : ℝ))^(1029/256 : ℝ) := by
    rw [show (20600318057081758489/20607500000000000000 : ℝ)+2*(1796965845201/824300000000000 : ℝ)*(1073/12500 : ℝ)=(2500064373952367/2500000000000000 : ℝ) by norm_num, show 1+2*(5175263452832053/100000000000000000000 : ℝ)=(50005175263452832053/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3871504126590603/5000000000000000000 : ℝ)+(5175263452832053/100000000000000000000 : ℝ) ≤ ((20600318057081758489/20607500000000000000 : ℝ)+(1796965845201/824300000000000 : ℝ)*((16827/100000 : ℝ)+(1073/12500 : ℝ)))^(1029/256 : ℝ) := by
    rw [show (20600318057081758489/20607500000000000000 : ℝ)+(1796965845201/824300000000000 : ℝ)*((16827/100000 : ℝ)+(1073/12500 : ℝ))=(10002054461654669/10000000000000000 : ℝ) by norm_num, show 1+(3871504126590603/5000000000000000000 : ℝ)+(5175263452832053/100000000000000000000 : ℝ)=(100082605345984644113/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3871504126590603/5000000000000000000 : ℝ) ≤ ((20600318057081758489/20607500000000000000 : ℝ)+2*(1796965845201/824300000000000 : ℝ)*(16827/100000 : ℝ))^(1029/256 : ℝ) := by
    rw [show (20600318057081758489/20607500000000000000 : ℝ)+2*(1796965845201/824300000000000 : ℝ)*(16827/100000 : ℝ)=(1000385142749987/1000000000000000 : ℝ) by norm_num, show 1+2*(3871504126590603/5000000000000000000 : ℝ)=(2503871504126590603/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20600318057081758489/20607500000000000000 : ℝ)*(X 1 0+X 2 0)+(1796965845201/824300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (1073/12500 : ℝ)) (hi := (16827/100000 : ℝ)) (c := (20600318057081758489/20607500000000000000 : ℝ)) (alpha := (1796965845201/824300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20600318057081758489/20607500000000000000 : ℝ)*(X 0 1+X 2 1)+(1796965845201/824300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (1073/12500 : ℝ)) (hi := (16827/100000 : ℝ)) (c := (20600318057081758489/20607500000000000000 : ℝ)) (alpha := (1796965845201/824300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20600318057081758489/20607500000000000000 : ℝ)*(X 0 2+X 1 2)+(1796965845201/824300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (1073/12500 : ℝ)) (hi := (16827/100000 : ℝ)) (c := (20600318057081758489/20607500000000000000 : ℝ)) (alpha := (1796965845201/824300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-442305401/2000000000 : ℝ)*X 0 0+(2720308881/5000000000 : ℝ)*X 0 1+(5221494057/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071273377/2000000000 : ℝ)*X 1 0+(-2323810061/10000000000 : ℝ)*X 1 1+(5221494253/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2678183469/5000000000 : ℝ)*X 2 0+(5221494429/10000000000 : ℝ)*X 2 1+(-1161904881/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4376229953/10000000000 : ℝ)*X 0 0+(4167918087/10000000000 : ℝ)*X 0 1+(4595153301/10000000000 : ℝ)*X 0 2+(4376229953/10000000000 : ℝ)*X 1 0+(4167918087/10000000000 : ℝ)*X 1 1+(4595153301/10000000000 : ℝ)*X 1 2+(4376229953/10000000000 : ℝ)*X 2 0+(4167918087/10000000000 : ℝ)*X 2 1+(4595153301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1105775641/5000000000 : ℝ)*X 0 0+(522241017/1000000000 : ℝ)*X 0 1+(2719847981/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325320787/2500000000 : ℝ)*X 1 0+(-2105607663/10000000000 : ℝ)*X 1 1+(543969647/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301283/10000000 : ℝ)*X 2 0+(1359924061/2500000000 : ℝ)*X 2 1+(-84224327/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2188138269/5000000000 : ℝ)*X 0 0+(2296684287/5000000000 : ℝ)*X 0 1+(833942767/2000000000 : ℝ)*X 0 2+(2188138269/5000000000 : ℝ)*X 1 0+(2296684287/5000000000 : ℝ)*X 1 1+(833942767/2000000000 : ℝ)*X 1 2+(2188138269/5000000000 : ℝ)*X 2 0+(2296684287/5000000000 : ℝ)*X 2 1+(833942767/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (453935065103450359786097031/51518750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2152517349/100000000000000 : ℝ)*(base19) + (935499131/50000000000000 : ℝ)*(base23) + (174979633/100000000000000 : ℝ)*(lower2) + (162263547/100000000000000 : ℝ)*(upper3) + (200560697/100000000000000 : ℝ)*(upper5) + (345219115502857/10000000000000 : ℝ)*(major0) + (345219115502857/10000000000000 : ℝ)*(major1) + (345219115502857/10000000000000 : ℝ)*(major2) + (4563671431820607/100000000000000 : ℝ)*(sp0) + (142616033789211/3125000000000 : ℝ)*(sp1) + (4563713362773839/100000000000000 : ℝ)*(sp2) + (585162111873943/25000000000000 : ℝ)*(sp3) + (43801951493/100000000000000 : ℝ)*(sp4) + (9167543543/50000000000000 : ℝ)*(sp7) + (1170333391291429/50000000000000 : ℝ)*(f.failure) + (4563715233772101/100000000000000 : ℝ)*(f.sum) + (1869956495991/329720000000000000000000000 : ℝ)*base66 + (37536887247528073/206075000000000000000000000000000 : ℝ)*base67 + (1339598452209403073/206075000000000000000000000000000 : ℝ)*base69 + (715680762866871927/206075000000000000000000000000000 : ℝ)*base72 + (33203874028947/4121500000000000000000000000 : ℝ)*base74 + (4376250330434078073/206075000000000000000000000000000 : ℝ)*base75 + (658994566401478073/206075000000000000000000000000000 : ℝ)*base77 + (657052414006503073/206075000000000000000000000000000 : ℝ)*base79 + (27797118083219/4121500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (4755179/500000000000000000000 : ℝ)*base89 + (4755179/500000000000000000000 : ℝ)*base91 + (4755179/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (935683622496415272341651181/257593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1123669769/100000000000000 : ℝ)*(base19) + (502249037/50000000000000 : ℝ)*(base23) + (3907203/10000000000000 : ℝ)*(upper2) + (93306903/50000000000000 : ℝ)*(upper3) + (870330595176657/25000000000000 : ℝ)*(major0) + (870330595176657/25000000000000 : ℝ)*(major1) + (870330595176657/25000000000000 : ℝ)*(major2) + (25646247511/100000000000000 : ℝ)*(sp1) + (4862294329/25000000000000 : ℝ)*(sp2) + (217001567/10000000000000 : ℝ)*(sp3) + (184089048068391/4000000000000 : ℝ)*(sp4) + (2301099715896247/50000000000000 : ℝ)*(sp5) + (920441149606877/20000000000000 : ℝ)*(sp6) + (590104067151949/25000000000000 : ℝ)*(sp7) + (1180209219311733/50000000000000 : ℝ)*(f.failure) + (184089048068391/4000000000000 : ℝ)*(f.sum) + (53125531159877/10303750000000000000000000000 : ℝ)*base65 + (1433613105783683727/515187500000000000000000000000000 : ℝ)*base68 + (678514000625816273/515187500000000000000000000000000 : ℝ)*base69 + (448995277521128773/515187500000000000000000000000000 : ℝ)*base71 + (1612450196487/41215000000000000000000000000 : ℝ)*base74 + (3500236167572128773/515187500000000000000000000000000 : ℝ)*base75 + (949361316907191273/515187500000000000000000000000000 : ℝ)*base77 + (530031289860058727/515187500000000000000000000000000 : ℝ)*base80 + (304553520954183/41215000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1395483/500000000000000000000 : ℝ)*base89 + (1395483/500000000000000000000 : ℝ)*base91 + (1395483/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1040_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16827/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1073/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2577/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (467/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1040_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1040_s4_0 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2215470403/10000000000 : ℝ)*x 0 + (540728741/1000000000 : ℝ)*x 1 + (2626124499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2215470403/10000000000 : ℝ)^8233 ≤ (13450369833767/100000000000000 : ℝ)^6185 := by
    have hnat : (2215470403 : ℕ)^8233*100000000000000^6185 ≤ 13450369833767^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215470403 10000000000 13450369833767 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540728741/1000000000 : ℝ)^8233 ≤ (4411259700797/10000000000000 : ℝ)^6185 := by
    have hnat : (540728741 : ℕ)^8233*10000000000000^6185 ≤ 4411259700797^6185*1000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540728741 1000000000 4411259700797 10000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626124499/5000000000 : ℝ)^8233 ≤ (10609258288147/25000000000000 : ℝ)^6185 := by
    have hnat : (2626124499 : ℕ)^8233*25000000000000^6185 ≤ 10609258288147^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626124499 5000000000 10609258288147 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2215470403/10000000000 : ℝ), (540728741/1000000000 : ℝ), (2626124499/5000000000 : ℝ)] ![(13450369833767/100000000000000 : ℝ), (4411259700797/10000000000000 : ℝ), (10609258288147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2215470403/10000000000 : ℝ)|^8233 ≤ (13450369833767/100000000000000 : ℝ)^6185
        have hw : |(-2215470403/10000000000 : ℝ)|=(2215470403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540728741/1000000000 : ℝ)|^8233 ≤ (4411259700797/10000000000000 : ℝ)^6185
        have hw : |(540728741/1000000000 : ℝ)|=(540728741/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626124499/5000000000 : ℝ)|^8233 ≤ (10609258288147/25000000000000 : ℝ)^6185
        have hw : |(2626124499/5000000000 : ℝ)|=(2626124499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s4_1 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5348132951/10000000000 : ℝ)*x 0 + (-91774113/400000000 : ℝ)*x 1 + (1313062257/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348132951/10000000000 : ℝ)^8233 ≤ (8694277536747/20000000000000 : ℝ)^6185 := by
    have hnat : (5348132951 : ℕ)^8233*20000000000000^6185 ≤ 8694277536747^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348132951 10000000000 8694277536747 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91774113/400000000 : ℝ)^8233 ≤ (140915788291/1000000000000 : ℝ)^6185 := by
    have hnat : (91774113 : ℕ)^8233*1000000000000^6185 ≤ 140915788291^6185*400000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91774113 400000000 140915788291 1000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313062257/2500000000 : ℝ)^8233 ≤ (10609258368811/25000000000000 : ℝ)^6185 := by
    have hnat : (1313062257 : ℕ)^8233*25000000000000^6185 ≤ 10609258368811^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313062257 2500000000 10609258368811 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348132951/10000000000 : ℝ), (-91774113/400000000 : ℝ), (1313062257/2500000000 : ℝ)] ![(8694277536747/20000000000000 : ℝ), (140915788291/1000000000000 : ℝ), (10609258368811/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348132951/10000000000 : ℝ)|^8233 ≤ (8694277536747/20000000000000 : ℝ)^6185
        have hw : |(5348132951/10000000000 : ℝ)|=(5348132951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-91774113/400000000 : ℝ)|^8233 ≤ (140915788291/1000000000000 : ℝ)^6185
        have hw : |(-91774113/400000000 : ℝ)|=(91774113/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313062257/2500000000 : ℝ)|^8233 ≤ (10609258368811/25000000000000 : ℝ)^6185
        have hw : |(1313062257/2500000000 : ℝ)|=(1313062257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s4_2 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5348133009/10000000000 : ℝ)*x 0 + (328265559/625000000 : ℝ)*x 1 + (-1147176429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348133009/10000000000 : ℝ)^8233 ≤ (10867847077821/25000000000000 : ℝ)^6185 := by
    have hnat : (5348133009 : ℕ)^8233*25000000000000^6185 ≤ 10867847077821^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348133009 10000000000 10867847077821 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328265559/625000000 : ℝ)^8233 ≤ (42437032571807/100000000000000 : ℝ)^6185 := by
    have hnat : (328265559 : ℕ)^8233*100000000000000^6185 ≤ 42437032571807^6185*625000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328265559 625000000 42437032571807 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1147176429/5000000000 : ℝ)^8233 ≤ (7045789549447/50000000000000 : ℝ)^6185 := by
    have hnat : (1147176429 : ℕ)^8233*50000000000000^6185 ≤ 7045789549447^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147176429 5000000000 7045789549447 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348133009/10000000000 : ℝ), (328265559/625000000 : ℝ), (-1147176429/5000000000 : ℝ)] ![(10867847077821/25000000000000 : ℝ), (42437032571807/100000000000000 : ℝ), (7045789549447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348133009/10000000000 : ℝ)|^8233 ≤ (10867847077821/25000000000000 : ℝ)^6185
        have hw : |(5348133009/10000000000 : ℝ)|=(5348133009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328265559/625000000 : ℝ)|^8233 ≤ (42437032571807/100000000000000 : ℝ)^6185
        have hw : |(328265559/625000000 : ℝ)|=(328265559/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1147176429/5000000000 : ℝ)|^8233 ≤ (7045789549447/50000000000000 : ℝ)^6185
        have hw : |(-1147176429/5000000000 : ℝ)|=(1147176429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s4_3 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (437856959/1000000000 : ℝ)*x 0 + (211504223/500000000 : ℝ)*x 1 + (4532370671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437856959/1000000000 : ℝ)^8233 ≤ (4163694761501/12500000000000 : ℝ)^6185 := by
    have hnat : (437856959 : ℕ)^8233*12500000000000^6185 ≤ 4163694761501^6185*1000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437856959 1000000000 4163694761501 12500000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211504223/500000000 : ℝ)^8233 ≤ (3181444527233/10000000000000 : ℝ)^6185 := by
    have hnat : (211504223 : ℕ)^8233*10000000000000^6185 ≤ 3181444527233^6185*500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211504223 500000000 3181444527233 10000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4532370671/10000000000 : ℝ)^8233 ≤ (17437998310631/50000000000000 : ℝ)^6185 := by
    have hnat : (4532370671 : ℕ)^8233*50000000000000^6185 ≤ 17437998310631^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532370671 10000000000 17437998310631 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437856959/1000000000 : ℝ), (211504223/500000000 : ℝ), (4532370671/10000000000 : ℝ)] ![(4163694761501/12500000000000 : ℝ), (3181444527233/10000000000000 : ℝ), (17437998310631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437856959/1000000000 : ℝ)|^8233 ≤ (4163694761501/12500000000000 : ℝ)^6185
        have hw : |(437856959/1000000000 : ℝ)|=(437856959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211504223/500000000 : ℝ)|^8233 ≤ (3181444527233/10000000000000 : ℝ)^6185
        have hw : |(211504223/500000000 : ℝ)|=(211504223/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4532370671/10000000000 : ℝ)|^8233 ≤ (17437998310631/50000000000000 : ℝ)^6185
        have hw : |(4532370671/10000000000 : ℝ)|=(4532370671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s4_4 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-17723833/80000000 : ℝ)*x 0 + (2626354009/5000000000 : ℝ)*x 1 + (1081365257/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17723833/80000000 : ℝ)^8233 ≤ (13450440319797/100000000000000 : ℝ)^6185 := by
    have hnat : (17723833 : ℕ)^8233*100000000000000^6185 ≤ 13450440319797^6185*80000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17723833 80000000 13450440319797 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626354009/5000000000 : ℝ)^8233 ≤ (10610492517923/25000000000000 : ℝ)^6185 := by
    have hnat : (2626354009 : ℕ)^8233*25000000000000^6185 ≤ 10610492517923^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626354009 5000000000 10610492517923 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081365257/2000000000 : ℝ)^8233 ≤ (4410758958681/10000000000000 : ℝ)^6185 := by
    have hnat : (1081365257 : ℕ)^8233*10000000000000^6185 ≤ 4410758958681^6185*2000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081365257 2000000000 4410758958681 10000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17723833/80000000 : ℝ), (2626354009/5000000000 : ℝ), (1081365257/2000000000 : ℝ)] ![(13450440319797/100000000000000 : ℝ), (10610492517923/25000000000000 : ℝ), (4410758958681/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17723833/80000000 : ℝ)|^8233 ≤ (13450440319797/100000000000000 : ℝ)^6185
        have hw : |(-17723833/80000000 : ℝ)|=(17723833/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626354009/5000000000 : ℝ)|^8233 ≤ (10610492517923/25000000000000 : ℝ)^6185
        have hw : |(2626354009/5000000000 : ℝ)|=(2626354009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081365257/2000000000 : ℝ)|^8233 ≤ (4410758958681/10000000000000 : ℝ)^6185
        have hw : |(1081365257/2000000000 : ℝ)|=(1081365257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s4_5 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309165267/10000000000 : ℝ)*x 0 + (-2139775631/10000000000 : ℝ)*x 1 + (2703413109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309165267/10000000000 : ℝ)^8233 ≤ (4305027410457/10000000000000 : ℝ)^6185 := by
    have hnat : (5309165267 : ℕ)^8233*10000000000000^6185 ≤ 4305027410457^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309165267 10000000000 4305027410457 10000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2139775631/10000000000 : ℝ)^8233 ≤ (3210534255701/25000000000000 : ℝ)^6185 := by
    have hnat : (2139775631 : ℕ)^8233*25000000000000^6185 ≤ 3210534255701^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139775631 10000000000 3210534255701 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703413109/5000000000 : ℝ)^8233 ≤ (44107588859257/100000000000000 : ℝ)^6185 := by
    have hnat : (2703413109 : ℕ)^8233*100000000000000^6185 ≤ 44107588859257^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703413109 5000000000 44107588859257 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309165267/10000000000 : ℝ), (-2139775631/10000000000 : ℝ), (2703413109/5000000000 : ℝ)] ![(4305027410457/10000000000000 : ℝ), (3210534255701/25000000000000 : ℝ), (44107588859257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309165267/10000000000 : ℝ)|^8233 ≤ (4305027410457/10000000000000 : ℝ)^6185
        have hw : |(5309165267/10000000000 : ℝ)|=(5309165267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2139775631/10000000000 : ℝ)|^8233 ≤ (3210534255701/25000000000000 : ℝ)^6185
        have hw : |(-2139775631/10000000000 : ℝ)|=(2139775631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703413109/5000000000 : ℝ)|^8233 ≤ (44107588859257/100000000000000 : ℝ)^6185
        have hw : |(2703413109/5000000000 : ℝ)|=(2703413109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s4_6 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265458261/500000000 : ℝ)*x 0 + (5406826253/10000000000 : ℝ)*x 1 + (-2139775647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265458261/500000000 : ℝ)^8233 ≤ (43050273597269/100000000000000 : ℝ)^6185 := by
    have hnat : (265458261 : ℕ)^8233*100000000000000^6185 ≤ 43050273597269^6185*500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265458261 500000000 43050273597269 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406826253/10000000000 : ℝ)^8233 ≤ (22053794619661/50000000000000 : ℝ)^6185 := by
    have hnat : (5406826253 : ℕ)^8233*50000000000000^6185 ≤ 22053794619661^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406826253 10000000000 22053794619661 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2139775647/10000000000 : ℝ)^8233 ≤ (12842137150627/100000000000000 : ℝ)^6185 := by
    have hnat : (2139775647 : ℕ)^8233*100000000000000^6185 ≤ 12842137150627^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139775647 10000000000 12842137150627 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265458261/500000000 : ℝ), (5406826253/10000000000 : ℝ), (-2139775647/10000000000 : ℝ)] ![(43050273597269/100000000000000 : ℝ), (22053794619661/50000000000000 : ℝ), (12842137150627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265458261/500000000 : ℝ)|^8233 ≤ (43050273597269/100000000000000 : ℝ)^6185
        have hw : |(265458261/500000000 : ℝ)|=(265458261/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406826253/10000000000 : ℝ)|^8233 ≤ (22053794619661/50000000000000 : ℝ)^6185
        have hw : |(5406826253/10000000000 : ℝ)|=(5406826253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2139775647/10000000000 : ℝ)|^8233 ≤ (12842137150627/100000000000000 : ℝ)^6185
        have hw : |(-2139775647/10000000000 : ℝ)|=(2139775647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s4_7 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2189293093/5000000000 : ℝ)*x 0 + (566434371/1250000000 : ℝ)*x 1 + (2115492011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189293093/5000000000 : ℝ)^8233 ≤ (8327431537457/25000000000000 : ℝ)^6185 := by
    have hnat : (2189293093 : ℕ)^8233*25000000000000^6185 ≤ 8327431537457^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189293093 5000000000 8327431537457 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566434371/1250000000 : ℝ)^8233 ≤ (17433411197613/50000000000000 : ℝ)^6185 := by
    have hnat : (566434371 : ℕ)^8233*50000000000000^6185 ≤ 17433411197613^6185*1250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566434371 1250000000 17433411197613 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115492011/5000000000 : ℝ)^8233 ≤ (31823451441881/100000000000000 : ℝ)^6185 := by
    have hnat : (2115492011 : ℕ)^8233*100000000000000^6185 ≤ 31823451441881^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115492011 5000000000 31823451441881 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189293093/5000000000 : ℝ), (566434371/1250000000 : ℝ), (2115492011/5000000000 : ℝ)] ![(8327431537457/25000000000000 : ℝ), (17433411197613/50000000000000 : ℝ), (31823451441881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189293093/5000000000 : ℝ)|^8233 ≤ (8327431537457/25000000000000 : ℝ)^6185
        have hw : |(2189293093/5000000000 : ℝ)|=(2189293093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(566434371/1250000000 : ℝ)|^8233 ≤ (17433411197613/50000000000000 : ℝ)^6185
        have hw : |(566434371/1250000000 : ℝ)|=(566434371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115492011/5000000000 : ℝ)|^8233 ≤ (31823451441881/100000000000000 : ℝ)^6185
        have hw : |(2115492011/5000000000 : ℝ)|=(2115492011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1040_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (467/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2577/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2193/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1781/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (467/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2577/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (467/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2577/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (467/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2577/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (467/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2577/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (467/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2577/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (467/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2577/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2577/25000 : ℝ) ^ (1029/256 : ℝ) ≤ (53999993375369/500000000000000000 : ℝ) := by
    have hpowers : (2577/25000 : ℝ)^1029 ≤ (53999993375369/500000000000000000 : ℝ)^256 := by
      have hnat : (2577 : ℕ)^1029*500000000000000000^256 ≤ 53999993375369^256*25000^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2577 25000 53999993375369 500000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2577/25000 : ℝ)) (X := (53999993375369/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hpowhi : (467/3125 : ℝ) ^ (1029/256 : ℝ) ≤ (9611114187684001/20000000000000000000 : ℝ) := by
    have hpowers : (467/3125 : ℝ)^1029 ≤ (9611114187684001/20000000000000000000 : ℝ)^256 := by
      have hnat : (467 : ℕ)^1029*20000000000000000000^256 ≤ 9611114187684001^256*3125^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        467 3125 9611114187684001 20000000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (467/3125 : ℝ)) (X := (9611114187684001/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (250053999993375369/250000000000000000 : ℝ) ≤ (10000537332434913/10000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (250053999993375369/250000000000000000 : ℝ)^256 ≤ (10000537332434913/10000000000000000 : ℝ)^1029 := by
      have hnat : (250053999993375369 : ℕ)^256*10000000000000000^1029 ≤ 10000537332434913^1029*250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250053999993375369 250000000000000000 10000537332434913 10000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000537332434913/10000000000000000 : ℝ)) (X := (250053999993375369/250000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20011771113922698761/20000000000000000000 : ℝ) ≤ (10001463916050517/10000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (20011771113922698761/20000000000000000000 : ℝ)^256 ≤ (10001463916050517/10000000000000000 : ℝ)^1029 := by
      have hnat : (20011771113922698761 : ℕ)^256*10000000000000000^1029 ≤ 10001463916050517^1029*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20011771113922698761 20000000000000000000 10001463916050517 10000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001463916050517/10000000000000000 : ℝ)) (X := (20011771113922698761/20000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10009611114187684001/10000000000000000000 : ℝ) ≤ (10002390499666121/10000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (10009611114187684001/10000000000000000000 : ℝ)^256 ≤ (10002390499666121/10000000000000000 : ℝ)^1029 := by
      have hnat : (10009611114187684001 : ℕ)^256*10000000000000000^1029 ≤ 10002390499666121^1029*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10009611114187684001 10000000000000000000 10002390499666121 10000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002390499666121/10000000000000000 : ℝ)) (X := (10009611114187684001/10000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(53999993375369/500000000000000000 : ℝ) ≤ ((609781429280907429/610000000000000000 : ℝ)+2*(12191889679/6100000000000 : ℝ)*(2577/25000 : ℝ))^(1029/256 : ℝ) := by
    rw [show (609781429280907429/610000000000000000 : ℝ)+2*(12191889679/6100000000000 : ℝ)*(2577/25000 : ℝ)=(10000537332434913/10000000000000000 : ℝ) by norm_num, show 1+2*(53999993375369/500000000000000000 : ℝ)=(250053999993375369/250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9611114187684001/20000000000000000000 : ℝ)+(53999993375369/500000000000000000 : ℝ) ≤ ((609781429280907429/610000000000000000 : ℝ)+(12191889679/6100000000000 : ℝ)*((467/3125 : ℝ)+(2577/25000 : ℝ)))^(1029/256 : ℝ) := by
    rw [show (609781429280907429/610000000000000000 : ℝ)+(12191889679/6100000000000 : ℝ)*((467/3125 : ℝ)+(2577/25000 : ℝ))=(10001463916050517/10000000000000000 : ℝ) by norm_num, show 1+(9611114187684001/20000000000000000000 : ℝ)+(53999993375369/500000000000000000 : ℝ)=(20011771113922698761/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9611114187684001/20000000000000000000 : ℝ) ≤ ((609781429280907429/610000000000000000 : ℝ)+2*(12191889679/6100000000000 : ℝ)*(467/3125 : ℝ))^(1029/256 : ℝ) := by
    rw [show (609781429280907429/610000000000000000 : ℝ)+2*(12191889679/6100000000000 : ℝ)*(467/3125 : ℝ)=(10002390499666121/10000000000000000 : ℝ) by norm_num, show 1+2*(9611114187684001/20000000000000000000 : ℝ)=(10009611114187684001/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (609781429280907429/610000000000000000 : ℝ)*(X 1 0+X 2 0)+(12191889679/6100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (2577/25000 : ℝ)) (hi := (467/3125 : ℝ)) (c := (609781429280907429/610000000000000000 : ℝ)) (alpha := (12191889679/6100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (609781429280907429/610000000000000000 : ℝ)*(X 0 1+X 2 1)+(12191889679/6100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (2577/25000 : ℝ)) (hi := (467/3125 : ℝ)) (c := (609781429280907429/610000000000000000 : ℝ)) (alpha := (12191889679/6100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (609781429280907429/610000000000000000 : ℝ)*(X 0 2+X 1 2)+(12191889679/6100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (2577/25000 : ℝ)) (hi := (467/3125 : ℝ)) (c := (609781429280907429/610000000000000000 : ℝ)) (alpha := (12191889679/6100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2215470403/10000000000 : ℝ)*X 0 0+(540728741/1000000000 : ℝ)*X 0 1+(2626124499/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348132951/10000000000 : ℝ)*X 1 0+(-91774113/400000000 : ℝ)*X 1 1+(1313062257/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348133009/10000000000 : ℝ)*X 2 0+(328265559/625000000 : ℝ)*X 2 1+(-1147176429/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((437856959/1000000000 : ℝ)*X 0 0+(211504223/500000000 : ℝ)*X 0 1+(4532370671/10000000000 : ℝ)*X 0 2+(437856959/1000000000 : ℝ)*X 1 0+(211504223/500000000 : ℝ)*X 1 1+(4532370671/10000000000 : ℝ)*X 1 2+(437856959/1000000000 : ℝ)*X 2 0+(211504223/500000000 : ℝ)*X 2 1+(4532370671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-17723833/80000000 : ℝ)*X 0 0+(2626354009/5000000000 : ℝ)*X 0 1+(1081365257/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309165267/10000000000 : ℝ)*X 1 0+(-2139775631/10000000000 : ℝ)*X 1 1+(2703413109/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265458261/500000000 : ℝ)*X 2 0+(5406826253/10000000000 : ℝ)*X 2 1+(-2139775647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2189293093/5000000000 : ℝ)*X 0 0+(566434371/1250000000 : ℝ)*X 0 1+(2115492011/5000000000 : ℝ)*X 0 2+(2189293093/5000000000 : ℝ)*X 1 0+(566434371/1250000000 : ℝ)*X 1 1+(2115492011/5000000000 : ℝ)*X 1 2+(2189293093/5000000000 : ℝ)*X 2 0+(566434371/1250000000 : ℝ)*X 2 1+(2115492011/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (65982183791690961711695697/7625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (911144761/50000000000000 : ℝ)*(base19) + (1807769611/100000000000000 : ℝ)*(base23) + (45176009/100000000000000 : ℝ)*(lower2) + (6042869/2500000000000 : ℝ)*(upper3) + (73221427/50000000000000 : ℝ)*(upper5) + (2439566799229569/50000000000000 : ℝ)*(major0) + (2439566799229569/50000000000000 : ℝ)*(major1) + (2439566799229569/50000000000000 : ℝ)*(major2) + (6450058008964383/100000000000000 : ℝ)*(sp0) + (6450097771906313/100000000000000 : ℝ)*(sp1) + (403131111651639/6250000000000 : ℝ)*(sp2) + (3308143973413639/100000000000000 : ℝ)*(sp3) + (41585231451/100000000000000 : ℝ)*(sp4) + (5835215521/25000000000000 : ℝ)*(sp7) + (1654083657137861/50000000000000 : ℝ)*(f.failure) + (1290019918839167/20000000000000 : ℝ)*(f.sum) + (94777212553/19062500000000000000000000 : ℝ)*base66 + (495369420543668101/30500000000000000000000000000000 : ℝ)*base67 + (2529802970668101/30500000000000000000000000000000 : ℝ)*base69 + (96244383314831899/30500000000000000000000000000000 : ℝ)*base72 + (435755166533/305000000000000000000000000 : ℝ)*base74 + (446110030123168101/30500000000000000000000000000000 : ℝ)*base75 + (23394661918668101/30500000000000000000000000000000 : ℝ)*base77 + (673790903649668101/30500000000000000000000000000000 : ℝ)*base79 + (380451467923/305000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (5438389/500000000000000000000 : ℝ)*base90 + (5438389/500000000000000000000 : ℝ)*base92 + (5438389/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5363004170045289562273653/953125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68156519/5000000000000 : ℝ)*(base19) + (1463440167/100000000000000 : ℝ)*(base23) + (113639673/100000000000000 : ℝ)*(upper2) + (7647261/50000000000000 : ℝ)*(upper3) + (368004871/100000000000000 : ℝ)*(upper5) + (153381473473003/3125000000000 : ℝ)*(major0) + (153381473473003/3125000000000 : ℝ)*(major1) + (153381473473003/3125000000000 : ℝ)*(major2) + (36702813043/100000000000000 : ℝ)*(sp1) + (29032931873/100000000000000 : ℝ)*(sp2) + (1297706849609637/20000000000000 : ℝ)*(sp4) + (6488496182104763/100000000000000 : ℝ)*(sp5) + (3244251875838073/50000000000000 : ℝ)*(sp6) + (665575973333077/20000000000000 : ℝ)*(sp7) + (665575973333077/20000000000000 : ℝ)*(f.failure) + (1297706849609637/20000000000000 : ℝ)*(f.sum) + (1022908040259/305000000000000000000000000 : ℝ)*base65 + (2573240120776787/1906250000000000000000000000000 : ℝ)*base67 + (20137063174370537/1906250000000000000000000000000 : ℝ)*base69 + (2516646962839287/1906250000000000000000000000000 : ℝ)*base71 + (197802968603/38125000000000000000000000 : ℝ)*base73 + (4183645843339287/1906250000000000000000000000000 : ℝ)*base75 + (12523332177120537/1906250000000000000000000000000 : ℝ)*base77 + (12552864532973213/1906250000000000000000000000000 : ℝ)*base80 + (207477983057/152500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (736827/200000000000000000000 : ℝ)*base89 + (736827/200000000000000000000 : ℝ)*base91 + (736827/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1040_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (467/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2577/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2193/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1781/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1040_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1040_s5_0 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-277047027/1250000000 : ℝ)*x 0 + (2698879447/5000000000 : ℝ)*x 1 + (5261183749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (277047027/1250000000 : ℝ)^8233 ≤ (13457690567791/100000000000000 : ℝ)^6185 := by
    have hnat : (277047027 : ℕ)^8233*100000000000000^6185 ≤ 13457690567791^6185*1250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277047027 1250000000 13457690567791 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698879447/5000000000 : ℝ)^8233 ≤ (44009154252847/100000000000000 : ℝ)^6185 := by
    have hnat : (2698879447 : ℕ)^8233*100000000000000^6185 ≤ 44009154252847^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698879447 5000000000 44009154252847 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261183749/10000000000 : ℝ)^8233 ≤ (42533155158297/100000000000000 : ℝ)^6185 := by
    have hnat : (5261183749 : ℕ)^8233*100000000000000^6185 ≤ 42533155158297^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261183749 10000000000 42533155158297 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-277047027/1250000000 : ℝ), (2698879447/5000000000 : ℝ), (5261183749/10000000000 : ℝ)] ![(13457690567791/100000000000000 : ℝ), (44009154252847/100000000000000 : ℝ), (42533155158297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-277047027/1250000000 : ℝ)|^8233 ≤ (13457690567791/100000000000000 : ℝ)^6185
        have hw : |(-277047027/1250000000 : ℝ)|=(277047027/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698879447/5000000000 : ℝ)|^8233 ≤ (44009154252847/100000000000000 : ℝ)^6185
        have hw : |(2698879447/5000000000 : ℝ)|=(2698879447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261183749/10000000000 : ℝ)|^8233 ≤ (42533155158297/100000000000000 : ℝ)^6185
        have hw : |(5261183749/10000000000 : ℝ)|=(5261183749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s5_1 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345766491/10000000000 : ℝ)*x 0 + (-2285721931/10000000000 : ℝ)*x 1 + (5261183707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345766491/10000000000 : ℝ)^8233 ≤ (43445784907041/100000000000000 : ℝ)^6185 := by
    have hnat : (5345766491 : ℕ)^8233*100000000000000^6185 ≤ 43445784907041^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345766491 10000000000 43445784907041 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2285721931/10000000000 : ℝ)^8233 ≤ (2804212072841/20000000000000 : ℝ)^6185 := by
    have hnat : (2285721931 : ℕ)^8233*20000000000000^6185 ≤ 2804212072841^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285721931 10000000000 2804212072841 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261183707/10000000000 : ℝ)^8233 ≤ (10633288676581/25000000000000 : ℝ)^6185 := by
    have hnat : (5261183707 : ℕ)^8233*25000000000000^6185 ≤ 10633288676581^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261183707 10000000000 10633288676581 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345766491/10000000000 : ℝ), (-2285721931/10000000000 : ℝ), (5261183707/10000000000 : ℝ)] ![(43445784907041/100000000000000 : ℝ), (2804212072841/20000000000000 : ℝ), (10633288676581/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345766491/10000000000 : ℝ)|^8233 ≤ (43445784907041/100000000000000 : ℝ)^6185
        have hw : |(5345766491/10000000000 : ℝ)|=(5345766491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2285721931/10000000000 : ℝ)|^8233 ≤ (2804212072841/20000000000000 : ℝ)^6185
        have hw : |(-2285721931/10000000000 : ℝ)|=(2285721931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261183707/10000000000 : ℝ)|^8233 ≤ (10633288676581/25000000000000 : ℝ)^6185
        have hw : |(5261183707/10000000000 : ℝ)|=(5261183707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s5_2 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534576651/1000000000 : ℝ)*x 0 + (657647963/1250000000 : ℝ)*x 1 + (-228572191/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534576651/1000000000 : ℝ)^8233 ≤ (10861446278147/25000000000000 : ℝ)^6185 := by
    have hnat : (534576651 : ℕ)^8233*25000000000000^6185 ≤ 10861446278147^6185*1000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534576651 1000000000 10861446278147 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657647963/1250000000 : ℝ)^8233 ≤ (42533154674041/100000000000000 : ℝ)^6185 := by
    have hnat : (657647963 : ℕ)^8233*100000000000000^6185 ≤ 42533154674041^6185*1250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657647963 1250000000 42533154674041 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228572191/1000000000 : ℝ)^8233 ≤ (3505265048183/25000000000000 : ℝ)^6185 := by
    have hnat : (228572191 : ℕ)^8233*25000000000000^6185 ≤ 3505265048183^6185*1000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228572191 1000000000 3505265048183 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534576651/1000000000 : ℝ), (657647963/1250000000 : ℝ), (-228572191/1000000000 : ℝ)] ![(10861446278147/25000000000000 : ℝ), (42533154674041/100000000000000 : ℝ), (3505265048183/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534576651/1000000000 : ℝ)|^8233 ≤ (10861446278147/25000000000000 : ℝ)^6185
        have hw : |(534576651/1000000000 : ℝ)|=(534576651/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657647963/1250000000 : ℝ)|^8233 ≤ (42533154674041/100000000000000 : ℝ)^6185
        have hw : |(657647963/1250000000 : ℝ)|=(657647963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-228572191/1000000000 : ℝ)|^8233 ≤ (3505265048183/25000000000000 : ℝ)^6185
        have hw : |(-228572191/1000000000 : ℝ)|=(228572191/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s5_3 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2189547553/5000000000 : ℝ)*x 0 + (4248014559/10000000000 : ℝ)*x 1 + (564287743/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189547553/5000000000 : ℝ)^8233 ≤ (33314879782331/100000000000000 : ℝ)^6185 := by
    have hnat : (2189547553 : ℕ)^8233*100000000000000^6185 ≤ 33314879782331^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189547553 5000000000 33314879782331 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4248014559/10000000000 : ℝ)^8233 ≤ (31994076068693/100000000000000 : ℝ)^6185 := by
    have hnat : (4248014559 : ℕ)^8233*100000000000000^6185 ≤ 31994076068693^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248014559 10000000000 31994076068693 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564287743/1250000000 : ℝ)^8233 ≤ (17345522066721/50000000000000 : ℝ)^6185 := by
    have hnat : (564287743 : ℕ)^8233*50000000000000^6185 ≤ 17345522066721^6185*1250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564287743 1250000000 17345522066721 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189547553/5000000000 : ℝ), (4248014559/10000000000 : ℝ), (564287743/1250000000 : ℝ)] ![(33314879782331/100000000000000 : ℝ), (31994076068693/100000000000000 : ℝ), (17345522066721/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189547553/5000000000 : ℝ)|^8233 ≤ (33314879782331/100000000000000 : ℝ)^6185
        have hw : |(2189547553/5000000000 : ℝ)|=(2189547553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4248014559/10000000000 : ℝ)|^8233 ≤ (31994076068693/100000000000000 : ℝ)^6185
        have hw : |(4248014559/10000000000 : ℝ)|=(4248014559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(564287743/1250000000 : ℝ)|^8233 ≤ (17345522066721/50000000000000 : ℝ)^6185
        have hw : |(564287743/1250000000 : ℝ)|=(564287743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s5_4 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2216381829/10000000000 : ℝ)*x 0 + (5261540409/10000000000 : ℝ)*x 1 + (269870053/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2216381829/10000000000 : ℝ)^8233 ≤ (13457735934857/100000000000000 : ℝ)^6185 := by
    have hnat : (2216381829 : ℕ)^8233*100000000000000^6185 ≤ 13457735934857^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216381829 10000000000 13457735934857 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261540409/10000000000 : ℝ)^8233 ≤ (2658562081701/6250000000000 : ℝ)^6185 := by
    have hnat : (5261540409 : ℕ)^8233*6250000000000^6185 ≤ 2658562081701^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261540409 10000000000 2658562081701 6250000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269870053/500000000 : ℝ)^8233 ≤ (44005270739619/100000000000000 : ℝ)^6185 := by
    have hnat : (269870053 : ℕ)^8233*100000000000000^6185 ≤ 44005270739619^6185*500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269870053 500000000 44005270739619 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2216381829/10000000000 : ℝ), (5261540409/10000000000 : ℝ), (269870053/500000000 : ℝ)] ![(13457735934857/100000000000000 : ℝ), (2658562081701/6250000000000 : ℝ), (44005270739619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2216381829/10000000000 : ℝ)|^8233 ≤ (13457735934857/100000000000000 : ℝ)^6185
        have hw : |(-2216381829/10000000000 : ℝ)|=(2216381829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261540409/10000000000 : ℝ)|^8233 ≤ (2658562081701/6250000000000 : ℝ)^6185
        have hw : |(5261540409/10000000000 : ℝ)|=(5261540409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269870053/500000000 : ℝ)|^8233 ≤ (44005270739619/100000000000000 : ℝ)^6185
        have hw : |(269870053/500000000 : ℝ)|=(269870053/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s5_5 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132785947/250000000 : ℝ)*x 0 + (-2149505259/10000000000 : ℝ)*x 1 + (539740097/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132785947/250000000 : ℝ)^8233 ≤ (5384350702297/12500000000000 : ℝ)^6185 := by
    have hnat : (132785947 : ℕ)^8233*12500000000000^6185 ≤ 5384350702297^6185*250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132785947 250000000 5384350702297 12500000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2149505259/10000000000 : ℝ)^8233 ≤ (3229981147957/25000000000000 : ℝ)^6185 := by
    have hnat : (2149505259 : ℕ)^8233*25000000000000^6185 ≤ 3229981147957^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149505259 10000000000 3229981147957 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539740097/1000000000 : ℝ)^8233 ≤ (352042158103/800000000000 : ℝ)^6185 := by
    have hnat : (539740097 : ℕ)^8233*800000000000^6185 ≤ 352042158103^6185*1000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539740097 1000000000 352042158103 800000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132785947/250000000 : ℝ), (-2149505259/10000000000 : ℝ), (539740097/1000000000 : ℝ)] ![(5384350702297/12500000000000 : ℝ), (3229981147957/25000000000000 : ℝ), (352042158103/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132785947/250000000 : ℝ)|^8233 ≤ (5384350702297/12500000000000 : ℝ)^6185
        have hw : |(132785947/250000000 : ℝ)|=(132785947/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2149505259/10000000000 : ℝ)|^8233 ≤ (3229981147957/25000000000000 : ℝ)^6185
        have hw : |(-2149505259/10000000000 : ℝ)|=(2149505259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539740097/1000000000 : ℝ)|^8233 ≤ (352042158103/800000000000 : ℝ)^6185
        have hw : |(539740097/1000000000 : ℝ)|=(539740097/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s5_6 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311438203/10000000000 : ℝ)*x 0 + (1349350249/2500000000 : ℝ)*x 1 + (-214950479/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311438203/10000000000 : ℝ)^8233 ≤ (43074809105217/100000000000000 : ℝ)^6185 := by
    have hnat : (5311438203 : ℕ)^8233*100000000000000^6185 ≤ 43074809105217^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311438203 10000000000 43074809105217 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349350249/2500000000 : ℝ)^8233 ≤ (22002635022523/50000000000000 : ℝ)^6185 := by
    have hnat : (1349350249 : ℕ)^8233*50000000000000^6185 ≤ 22002635022523^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349350249 2500000000 22002635022523 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214950479/1000000000 : ℝ)^8233 ≤ (12919920839397/100000000000000 : ℝ)^6185 := by
    have hnat : (214950479 : ℕ)^8233*100000000000000^6185 ≤ 12919920839397^6185*1000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214950479 1000000000 12919920839397 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311438203/10000000000 : ℝ), (1349350249/2500000000 : ℝ), (-214950479/1000000000 : ℝ)] ![(43074809105217/100000000000000 : ℝ), (22002635022523/50000000000000 : ℝ), (12919920839397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311438203/10000000000 : ℝ)|^8233 ≤ (43074809105217/100000000000000 : ℝ)^6185
        have hw : |(5311438203/10000000000 : ℝ)|=(5311438203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349350249/2500000000 : ℝ)|^8233 ≤ (22002635022523/50000000000000 : ℝ)^6185
        have hw : |(1349350249/2500000000 : ℝ)|=(1349350249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-214950479/1000000000 : ℝ)|^8233 ≤ (12919920839397/100000000000000 : ℝ)^6185
        have hw : |(-214950479/1000000000 : ℝ)|=(214950479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s5_7 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2189553061/5000000000 : ℝ)*x 0 + (902721373/2000000000 : ℝ)*x 1 + (4248712609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189553061/5000000000 : ℝ)^8233 ≤ (1665749566961/5000000000000 : ℝ)^6185 := by
    have hnat : (2189553061 : ℕ)^8233*5000000000000^6185 ≤ 1665749566961^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189553061 5000000000 1665749566961 5000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (902721373/2000000000 : ℝ)^8233 ≤ (6936786831029/20000000000000 : ℝ)^6185 := by
    have hnat : (902721373 : ℕ)^8233*20000000000000^6185 ≤ 6936786831029^6185*2000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902721373 2000000000 6936786831029 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4248712609/10000000000 : ℝ)^8233 ≤ (32001074494037/100000000000000 : ℝ)^6185 := by
    have hnat : (4248712609 : ℕ)^8233*100000000000000^6185 ≤ 32001074494037^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248712609 10000000000 32001074494037 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189553061/5000000000 : ℝ), (902721373/2000000000 : ℝ), (4248712609/10000000000 : ℝ)] ![(1665749566961/5000000000000 : ℝ), (6936786831029/20000000000000 : ℝ), (32001074494037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189553061/5000000000 : ℝ)|^8233 ≤ (1665749566961/5000000000000 : ℝ)^6185
        have hw : |(2189553061/5000000000 : ℝ)|=(2189553061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(902721373/2000000000 : ℝ)|^8233 ≤ (6936786831029/20000000000000 : ℝ)^6185
        have hw : |(902721373/2000000000 : ℝ)|=(902721373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4248712609/10000000000 : ℝ)|^8233 ≤ (32001074494037/100000000000000 : ℝ)^6185
        have hw : |(4248712609/10000000000 : ℝ)|=(4248712609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1040_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1781/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2193/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2789/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (439/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1781/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2193/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1781/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2193/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1781/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2193/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1781/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2193/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1781/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2193/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1781/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2193/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
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
  have hpowlo : (2193/20000 : ℝ) ^ (1029/256 : ℝ) ≤ (692236854133023/5000000000000000000 : ℝ) := by
    have hpowers : (2193/20000 : ℝ)^1029 ≤ (692236854133023/5000000000000000000 : ℝ)^256 := by
      have hnat : (2193 : ℕ)^1029*5000000000000000000^256 ≤ 692236854133023^256*20000^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2193 20000 692236854133023 5000000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2193/20000 : ℝ)) (X := (692236854133023/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1781/12500 : ℝ) ^ (1029/256 : ℝ) ≤ (19836150109482267/50000000000000000000 : ℝ) := by
    have hpowers : (1781/12500 : ℝ)^1029 ≤ (19836150109482267/50000000000000000000 : ℝ)^256 := by
      have hnat : (1781 : ℕ)^1029*50000000000000000000^256 ≤ 19836150109482267^256*12500^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1781 12500 19836150109482267 50000000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1781/12500 : ℝ)) (X := (19836150109482267/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500692236854133023/2500000000000000000 : ℝ) ≤ (5000344400790797/5000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (2500692236854133023/2500000000000000000 : ℝ)^256 ≤ (5000344400790797/5000000000000000 : ℝ)^1029 := by
      have hnat : (2500692236854133023 : ℕ)^256*5000000000000000^1029 ≤ 5000344400790797^1029*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500692236854133023 2500000000000000000 5000344400790797 5000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000344400790797/5000000000000000 : ℝ)) (X := (2500692236854133023/2500000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026758518650812497/50000000000000000000 : ℝ) ≤ (2000266231456667/2000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (50026758518650812497/50000000000000000000 : ℝ)^256 ≤ (2000266231456667/2000000000000000 : ℝ)^1029 := by
      have hnat : (50026758518650812497 : ℕ)^256*2000000000000000^1029 ≤ 2000266231456667^1029*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026758518650812497 50000000000000000000 2000266231456667 2000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000266231456667/2000000000000000 : ℝ)) (X := (50026758518650812497/50000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019836150109482267/25000000000000000000 : ℝ) ≤ (2500493378246269/2500000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (25019836150109482267/25000000000000000000 : ℝ)^256 ≤ (2500493378246269/2500000000000000 : ℝ)^1029 := by
      have hnat : (25019836150109482267 : ℕ)^256*2500000000000000^1029 ≤ 2500493378246269^1029*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019836150109482267 25000000000000000000 2500493378246269 2500000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500493378246269/2500000000000000 : ℝ)) (X := (25019836150109482267/25000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(692236854133023/5000000000000000000 : ℝ) ≤ ((8204543618763298243/8207500000000000000 : ℝ)+2*(642355701741/328300000000000 : ℝ)*(2193/20000 : ℝ))^(1029/256 : ℝ) := by
    rw [show (8204543618763298243/8207500000000000000 : ℝ)+2*(642355701741/328300000000000 : ℝ)*(2193/20000 : ℝ)=(5000344400790797/5000000000000000 : ℝ) by norm_num, show 1+2*(692236854133023/5000000000000000000 : ℝ)=(2500692236854133023/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19836150109482267/50000000000000000000 : ℝ)+(692236854133023/5000000000000000000 : ℝ) ≤ ((8204543618763298243/8207500000000000000 : ℝ)+(642355701741/328300000000000 : ℝ)*((1781/12500 : ℝ)+(2193/20000 : ℝ)))^(1029/256 : ℝ) := by
    rw [show (8204543618763298243/8207500000000000000 : ℝ)+(642355701741/328300000000000 : ℝ)*((1781/12500 : ℝ)+(2193/20000 : ℝ))=(2000266231456667/2000000000000000 : ℝ) by norm_num, show 1+(19836150109482267/50000000000000000000 : ℝ)+(692236854133023/5000000000000000000 : ℝ)=(50026758518650812497/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19836150109482267/50000000000000000000 : ℝ) ≤ ((8204543618763298243/8207500000000000000 : ℝ)+2*(642355701741/328300000000000 : ℝ)*(1781/12500 : ℝ))^(1029/256 : ℝ) := by
    rw [show (8204543618763298243/8207500000000000000 : ℝ)+2*(642355701741/328300000000000 : ℝ)*(1781/12500 : ℝ)=(2500493378246269/2500000000000000 : ℝ) by norm_num, show 1+2*(19836150109482267/50000000000000000000 : ℝ)=(25019836150109482267/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8204543618763298243/8207500000000000000 : ℝ)*(X 1 0+X 2 0)+(642355701741/328300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (2193/20000 : ℝ)) (hi := (1781/12500 : ℝ)) (c := (8204543618763298243/8207500000000000000 : ℝ)) (alpha := (642355701741/328300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8204543618763298243/8207500000000000000 : ℝ)*(X 0 1+X 2 1)+(642355701741/328300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (2193/20000 : ℝ)) (hi := (1781/12500 : ℝ)) (c := (8204543618763298243/8207500000000000000 : ℝ)) (alpha := (642355701741/328300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8204543618763298243/8207500000000000000 : ℝ)*(X 0 2+X 1 2)+(642355701741/328300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (2193/20000 : ℝ)) (hi := (1781/12500 : ℝ)) (c := (8204543618763298243/8207500000000000000 : ℝ)) (alpha := (642355701741/328300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-277047027/1250000000 : ℝ)*X 0 0+(2698879447/5000000000 : ℝ)*X 0 1+(5261183749/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345766491/10000000000 : ℝ)*X 1 0+(-2285721931/10000000000 : ℝ)*X 1 1+(5261183707/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534576651/1000000000 : ℝ)*X 2 0+(657647963/1250000000 : ℝ)*X 2 1+(-228572191/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2189547553/5000000000 : ℝ)*X 0 0+(4248014559/10000000000 : ℝ)*X 0 1+(564287743/1250000000 : ℝ)*X 0 2+(2189547553/5000000000 : ℝ)*X 1 0+(4248014559/10000000000 : ℝ)*X 1 1+(564287743/1250000000 : ℝ)*X 1 2+(2189547553/5000000000 : ℝ)*X 2 0+(4248014559/10000000000 : ℝ)*X 2 1+(564287743/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2216381829/10000000000 : ℝ)*X 0 0+(5261540409/10000000000 : ℝ)*X 0 1+(269870053/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132785947/250000000 : ℝ)*X 1 0+(-2149505259/10000000000 : ℝ)*X 1 1+(539740097/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311438203/10000000000 : ℝ)*X 2 0+(1349350249/2500000000 : ℝ)*X 2 1+(-214950479/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2189553061/5000000000 : ℝ)*X 0 0+(902721373/2000000000 : ℝ)*X 0 1+(4248712609/10000000000 : ℝ)*X 0 2+(2189553061/5000000000 : ℝ)*X 1 0+(902721373/2000000000 : ℝ)*X 1 1+(4248712609/10000000000 : ℝ)*X 1 2+(2189553061/5000000000 : ℝ)*X 2 0+(902721373/2000000000 : ℝ)*X 2 1+(4248712609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34905091567859297673206313/8207500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (237885051/25000000000000 : ℝ)*(base19) + (939302933/100000000000000 : ℝ)*(base23) + (4090721/20000000000000 : ℝ)*(lower2) + (15195407/20000000000000 : ℝ)*(upper3) + (20984377/25000000000000 : ℝ)*(upper5) + (110773919891499/2000000000000 : ℝ)*(major0) + (110773919891499/2000000000000 : ℝ)*(major1) + (110773919891499/2000000000000 : ℝ)*(major2) + (1464400090230017/20000000000000 : ℝ)*(sp0) + (7322024767167767/100000000000000 : ℝ)*(sp1) + (3661012389702519/50000000000000 : ℝ)*(sp2) + (15021414269683/400000000000 : ℝ)*(sp3) + (12633778943/50000000000000 : ℝ)*(sp4) + (6280630107/50000000000000 : ℝ)*(sp7) + (938841532170241/25000000000000 : ℝ)*(f.failure) + (7322025718707971/100000000000000 : ℝ)*(f.sum) + (286378522349/410375000000000000000000000 : ℝ)*base66 + (190725813388148743/16415000000000000000000000000000 : ℝ)*base68 + (180645598707353743/16415000000000000000000000000000 : ℝ)*base70 + (44730565058763743/16415000000000000000000000000000 : ℝ)*base72 + (15114050658501/3283000000000000000000000000 : ℝ)*base73 + (200446101255613743/16415000000000000000000000000000 : ℝ)*base76 + (275554713026708743/16415000000000000000000000000000 : ℝ)*base78 + (75293553542168743/16415000000000000000000000000000 : ℝ)*base80 + (6192763419/6412109375000000000000000 : ℝ)*base82 + (881009/250000000000000000000 : ℝ)*base90 + (881009/250000000000000000000 : ℝ)*base92 + (881009/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (608355411269488627719630963/205187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68340001/25000000000000 : ℝ)*(base8) + (150625949/100000000000000 : ℝ)*(base15) + (901167/6250000000000 : ℝ)*(lower2) + (18911451/10000000000000 : ℝ)*(upper4) + (89111557/50000000000000 : ℝ)*(upper5) + (2783899611277847/50000000000000 : ℝ)*(major0) + (2783899611277847/50000000000000 : ℝ)*(major1) + (2783899611277847/50000000000000 : ℝ)*(major2) + (82864733/781250000000 : ℝ)*(sp2) + (491150989/12500000000000 : ℝ)*(sp3) + (7360499271297769/100000000000000 : ℝ)*(sp4) + (460031212126989/6250000000000 : ℝ)*(sp5) + (7360488937971949/100000000000000 : ℝ)*(sp6) + (1887547436208253/50000000000000 : ℝ)*(sp7) + (1887549400812209/50000000000000 : ℝ)*(f.failure) + (7360499544657773/100000000000000 : ℝ)*(f.sum) + (297748427079491/16415000000000000000000000000 : ℝ)*base66 + (7210660784406527179/410375000000000000000000000000000 : ℝ)*base68 + (5042562743212652179/410375000000000000000000000000000 : ℝ)*base70 + (6687543257520902179/410375000000000000000000000000000 : ℝ)*base72 + (7341721001597/2051875000000000000000000000 : ℝ)*base74 + (5999711671584847821/410375000000000000000000000000000 : ℝ)*base75 + (956582137221472821/410375000000000000000000000000000 : ℝ)*base77 + (1040354938463652179/410375000000000000000000000000000 : ℝ)*base80 + (3743620027737/8207500000000000000000000000 : ℝ)*base81 + (1699041/500000000000000000000 : ℝ)*base90 + (1699041/500000000000000000000 : ℝ)*base92 + (1699041/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1040_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1781/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2193/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (439/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1040_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1040_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16827/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1073/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (439/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1040_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1040_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1040_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16827/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1073/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (439/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1040_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

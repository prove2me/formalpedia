-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1333_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:02:36.987989+00:00
-- url     : https://prove2.me/submissions/3fa351ec-47c5-46fb-babe-dcd3f2c8cf90

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
theorem support_rectangle_w1333_s3_0 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2049918177/10000000000 : ℝ)*x 0 + (5428337003/10000000000 : ℝ)*x 1 + (5230378937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049918177/10000000000 : ℝ)^4293 ≤ (6238942713193/50000000000000 : ℝ)^3269 := by
    have hnat : (2049918177 : ℕ)^4293*50000000000000^3269 ≤ 6238942713193^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049918177 10000000000 6238942713193 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428337003/10000000000 : ℝ)^4293 ≤ (22414153323391/50000000000000 : ℝ)^3269 := by
    have hnat : (5428337003 : ℕ)^4293*50000000000000^3269 ≤ 22414153323391^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428337003 10000000000 22414153323391 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230378937/10000000000 : ℝ)^4293 ≤ (8538761583893/20000000000000 : ℝ)^3269 := by
    have hnat : (5230378937 : ℕ)^4293*20000000000000^3269 ≤ 8538761583893^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230378937 10000000000 8538761583893 20000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2049918177/10000000000 : ℝ), (5428337003/10000000000 : ℝ), (5230378937/10000000000 : ℝ)] ![(6238942713193/50000000000000 : ℝ), (22414153323391/50000000000000 : ℝ), (8538761583893/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2049918177/10000000000 : ℝ)|^4293 ≤ (6238942713193/50000000000000 : ℝ)^3269
        have hw : |(-2049918177/10000000000 : ℝ)|=(2049918177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428337003/10000000000 : ℝ)|^4293 ≤ (22414153323391/50000000000000 : ℝ)^3269
        have hw : |(5428337003/10000000000 : ℝ)|=(5428337003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230378937/10000000000 : ℝ)|^4293 ≤ (8538761583893/20000000000000 : ℝ)^3269
        have hw : |(5230378937/10000000000 : ℝ)|=(5230378937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s3_1 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676506527/5000000000 : ℝ)*x 0 + (-2151112839/10000000000 : ℝ)*x 1 + (5230379041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676506527/5000000000 : ℝ)^4293 ≤ (4401319579409/10000000000000 : ℝ)^3269 := by
    have hnat : (2676506527 : ℕ)^4293*10000000000000^3269 ≤ 4401319579409^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676506527 5000000000 4401319579409 10000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2151112839/10000000000 : ℝ)^4293 ≤ (3323248788317/25000000000000 : ℝ)^3269 := by
    have hnat : (2151112839 : ℕ)^4293*25000000000000^3269 ≤ 3323248788317^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151112839 10000000000 3323248788317 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230379041/10000000000 : ℝ)^4293 ≤ (42693809034301/100000000000000 : ℝ)^3269 := by
    have hnat : (5230379041 : ℕ)^4293*100000000000000^3269 ≤ 42693809034301^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230379041 10000000000 42693809034301 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676506527/5000000000 : ℝ), (-2151112839/10000000000 : ℝ), (5230379041/10000000000 : ℝ)] ![(4401319579409/10000000000000 : ℝ), (3323248788317/25000000000000 : ℝ), (42693809034301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676506527/5000000000 : ℝ)|^4293 ≤ (4401319579409/10000000000000 : ℝ)^3269
        have hw : |(2676506527/5000000000 : ℝ)|=(2676506527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2151112839/10000000000 : ℝ)|^4293 ≤ (3323248788317/25000000000000 : ℝ)^3269
        have hw : |(-2151112839/10000000000 : ℝ)|=(2151112839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230379041/10000000000 : ℝ)|^4293 ≤ (42693809034301/100000000000000 : ℝ)^3269
        have hw : |(5230379041/10000000000 : ℝ)|=(5230379041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s3_2 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353012823/10000000000 : ℝ)*x 0 + (2615189657/5000000000 : ℝ)*x 1 + (-1075556393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353012823/10000000000 : ℝ)^4293 ≤ (1760527731993/4000000000000 : ℝ)^3269 := by
    have hnat : (5353012823 : ℕ)^4293*4000000000000^3269 ≤ 1760527731993^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353012823 10000000000 1760527731993 4000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2615189657/5000000000 : ℝ)^4293 ≤ (21346905980373/50000000000000 : ℝ)^3269 := by
    have hnat : (2615189657 : ℕ)^4293*50000000000000^3269 ≤ 21346905980373^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615189657 5000000000 21346905980373 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075556393/5000000000 : ℝ)^4293 ≤ (3323248680789/25000000000000 : ℝ)^3269 := by
    have hnat : (1075556393 : ℕ)^4293*25000000000000^3269 ≤ 3323248680789^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075556393 5000000000 3323248680789 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353012823/10000000000 : ℝ), (2615189657/5000000000 : ℝ), (-1075556393/5000000000 : ℝ)] ![(1760527731993/4000000000000 : ℝ), (21346905980373/50000000000000 : ℝ), (3323248680789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353012823/10000000000 : ℝ)|^4293 ≤ (1760527731993/4000000000000 : ℝ)^3269
        have hw : |(5353012823/10000000000 : ℝ)|=(5353012823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2615189657/5000000000 : ℝ)|^4293 ≤ (21346905980373/50000000000000 : ℝ)^3269
        have hw : |(2615189657/5000000000 : ℝ)|=(2615189657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1075556393/5000000000 : ℝ)|^4293 ≤ (3323248680789/25000000000000 : ℝ)^3269
        have hw : |(-1075556393/5000000000 : ℝ)|=(1075556393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s3_3 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081964259/2500000000 : ℝ)*x 0 + (2062932873/5000000000 : ℝ)*x 1 + (4539099359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081964259/2500000000 : ℝ)^4293 ≤ (2080736074717/6250000000000 : ℝ)^3269 := by
    have hnat : (1081964259 : ℕ)^4293*6250000000000^3269 ≤ 2080736074717^3269*2500000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081964259 2500000000 2080736074717 6250000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062932873/5000000000 : ℝ)^4293 ≤ (31266327364479/100000000000000 : ℝ)^3269 := by
    have hnat : (2062932873 : ℕ)^4293*100000000000000^3269 ≤ 31266327364479^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062932873 5000000000 31266327364479 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4539099359/10000000000 : ℝ)^4293 ≤ (17720947715383/50000000000000 : ℝ)^3269 := by
    have hnat : (4539099359 : ℕ)^4293*50000000000000^3269 ≤ 17720947715383^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4539099359 10000000000 17720947715383 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081964259/2500000000 : ℝ), (2062932873/5000000000 : ℝ), (4539099359/10000000000 : ℝ)] ![(2080736074717/6250000000000 : ℝ), (31266327364479/100000000000000 : ℝ), (17720947715383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081964259/2500000000 : ℝ)|^4293 ≤ (2080736074717/6250000000000 : ℝ)^3269
        have hw : |(1081964259/2500000000 : ℝ)|=(1081964259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2062932873/5000000000 : ℝ)|^4293 ≤ (31266327364479/100000000000000 : ℝ)^3269
        have hw : |(2062932873/5000000000 : ℝ)|=(2062932873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4539099359/10000000000 : ℝ)|^4293 ≤ (17720947715383/50000000000000 : ℝ)^3269
        have hw : |(4539099359/10000000000 : ℝ)|=(4539099359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s3_4 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2049938019/10000000000 : ℝ)*x 0 + (5231208419/10000000000 : ℝ)*x 1 + (5427502451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049938019/10000000000 : ℝ)^4293 ≤ (1559755504821/12500000000000 : ℝ)^3269 := by
    have hnat : (2049938019 : ℕ)^4293*12500000000000^3269 ≤ 1559755504821^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049938019 10000000000 1559755504821 12500000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231208419/10000000000 : ℝ)^4293 ≤ (5337837479707/12500000000000 : ℝ)^3269 := by
    have hnat : (5231208419 : ℕ)^4293*12500000000000^3269 ≤ 5337837479707^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231208419 10000000000 5337837479707 12500000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427502451/10000000000 : ℝ)^4293 ≤ (1792770244311/4000000000000 : ℝ)^3269 := by
    have hnat : (5427502451 : ℕ)^4293*4000000000000^3269 ≤ 1792770244311^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427502451 10000000000 1792770244311 4000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2049938019/10000000000 : ℝ), (5231208419/10000000000 : ℝ), (5427502451/10000000000 : ℝ)] ![(1559755504821/12500000000000 : ℝ), (5337837479707/12500000000000 : ℝ), (1792770244311/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2049938019/10000000000 : ℝ)|^4293 ≤ (1559755504821/12500000000000 : ℝ)^3269
        have hw : |(-2049938019/10000000000 : ℝ)|=(2049938019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231208419/10000000000 : ℝ)|^4293 ≤ (5337837479707/12500000000000 : ℝ)^3269
        have hw : |(5231208419/10000000000 : ℝ)|=(5231208419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427502451/10000000000 : ℝ)|^4293 ≤ (1792770244311/4000000000000 : ℝ)^3269
        have hw : |(5427502451/10000000000 : ℝ)|=(5427502451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s3_5 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302074841/10000000000 : ℝ)*x 0 + (-976994839/5000000000 : ℝ)*x 1 + (1085500531/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302074841/10000000000 : ℝ)^4293 ≤ (5433000331603/12500000000000 : ℝ)^3269 := by
    have hnat : (5302074841 : ℕ)^4293*12500000000000^3269 ≤ 5433000331603^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302074841 10000000000 5433000331603 12500000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (976994839/5000000000 : ℝ)^4293 ≤ (117167389999/1000000000000 : ℝ)^3269 := by
    have hnat : (976994839 : ℕ)^4293*1000000000000^3269 ≤ 117167389999^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976994839 5000000000 117167389999 1000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085500531/2000000000 : ℝ)^4293 ≤ (44819258320059/100000000000000 : ℝ)^3269 := by
    have hnat : (1085500531 : ℕ)^4293*100000000000000^3269 ≤ 44819258320059^3269*2000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085500531 2000000000 44819258320059 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302074841/10000000000 : ℝ), (-976994839/5000000000 : ℝ), (1085500531/2000000000 : ℝ)] ![(5433000331603/12500000000000 : ℝ), (117167389999/1000000000000 : ℝ), (44819258320059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302074841/10000000000 : ℝ)|^4293 ≤ (5433000331603/12500000000000 : ℝ)^3269
        have hw : |(5302074841/10000000000 : ℝ)|=(5302074841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-976994839/5000000000 : ℝ)|^4293 ≤ (117167389999/1000000000000 : ℝ)^3269
        have hw : |(-976994839/5000000000 : ℝ)|=(976994839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085500531/2000000000 : ℝ)|^4293 ≤ (44819258320059/100000000000000 : ℝ)^3269
        have hw : |(1085500531/2000000000 : ℝ)|=(1085500531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s3_6 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302076507/10000000000 : ℝ)*x 0 + (678437687/1250000000 : ℝ)*x 1 + (-1953988999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302076507/10000000000 : ℝ)^4293 ≤ (43464020587967/100000000000000 : ℝ)^3269 := by
    have hnat : (5302076507 : ℕ)^4293*100000000000000^3269 ≤ 43464020587967^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302076507 10000000000 43464020587967 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678437687/1250000000 : ℝ)^4293 ≤ (44819245751253/100000000000000 : ℝ)^3269 := by
    have hnat : (678437687 : ℕ)^4293*100000000000000^3269 ≤ 44819245751253^3269*1250000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678437687 1250000000 44819245751253 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1953988999/10000000000 : ℝ)^4293 ≤ (11716733653023/100000000000000 : ℝ)^3269 := by
    have hnat : (1953988999 : ℕ)^4293*100000000000000^3269 ≤ 11716733653023^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953988999 10000000000 11716733653023 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302076507/10000000000 : ℝ), (678437687/1250000000 : ℝ), (-1953988999/10000000000 : ℝ)] ![(43464020587967/100000000000000 : ℝ), (44819245751253/100000000000000 : ℝ), (11716733653023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302076507/10000000000 : ℝ)|^4293 ≤ (43464020587967/100000000000000 : ℝ)^3269
        have hw : |(5302076507/10000000000 : ℝ)|=(5302076507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678437687/1250000000 : ℝ)|^4293 ≤ (44819245751253/100000000000000 : ℝ)^3269
        have hw : |(678437687/1250000000 : ℝ)|=(678437687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1953988999/10000000000 : ℝ)|^4293 ≤ (11716733653023/100000000000000 : ℝ)^3269
        have hw : |(-1953988999/10000000000 : ℝ)|=(1953988999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s3_7 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4327899017/10000000000 : ℝ)*x 0 + (1134341977/2500000000 : ℝ)*x 1 + (2063803457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327899017/10000000000 : ℝ)^4293 ≤ (4161525161349/12500000000000 : ℝ)^3269 := by
    have hnat : (4327899017 : ℕ)^4293*12500000000000^3269 ≤ 4161525161349^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327899017 10000000000 4161525161349 12500000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134341977/2500000000 : ℝ)^4293 ≤ (8856035549223/25000000000000 : ℝ)^3269 := by
    have hnat : (1134341977 : ℕ)^4293*25000000000000^3269 ≤ 8856035549223^3269*2500000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134341977 2500000000 8856035549223 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063803457/5000000000 : ℝ)^4293 ≤ (31283656509061/100000000000000 : ℝ)^3269 := by
    have hnat : (2063803457 : ℕ)^4293*100000000000000^3269 ≤ 31283656509061^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063803457 5000000000 31283656509061 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327899017/10000000000 : ℝ), (1134341977/2500000000 : ℝ), (2063803457/5000000000 : ℝ)] ![(4161525161349/12500000000000 : ℝ), (8856035549223/25000000000000 : ℝ), (31283656509061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327899017/10000000000 : ℝ)|^4293 ≤ (4161525161349/12500000000000 : ℝ)^3269
        have hw : |(4327899017/10000000000 : ℝ)|=(4327899017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1134341977/2500000000 : ℝ)|^4293 ≤ (8856035549223/25000000000000 : ℝ)^3269
        have hw : |(1134341977/2500000000 : ℝ)|=(1134341977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2063803457/5000000000 : ℝ)|^4293 ≤ (31283656509061/100000000000000 : ℝ)^3269
        have hw : |(2063803457/5000000000 : ℝ)|=(2063803457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1333_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (807/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (306/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (1083/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7509/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (807/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (306/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (807/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (306/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (807/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (306/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (807/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (306/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (807/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (306/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (807/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (306/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (306/3125 : ℝ) ^ (1073/256 : ℝ) ≤ (1178588216449511/20000000000000000000 : ℝ) := by
    have hpowers : (306/3125 : ℝ)^1073 ≤ (1178588216449511/20000000000000000000 : ℝ)^256 := by
      have hnat : (306 : ℕ)^1073*20000000000000000000^256 ≤ 1178588216449511^256*3125^1073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        306 3125 1178588216449511 20000000000000000000 1073 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (306/3125 : ℝ)) (X := (1178588216449511/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hpowhi : (807/5000 : ℝ) ^ (1073/256 : ℝ) ≤ (11965804840709969/25000000000000000000 : ℝ) := by
    have hpowers : (807/5000 : ℝ)^1073 ≤ (11965804840709969/25000000000000000000 : ℝ)^256 := by
      have hnat : (807 : ℕ)^1073*25000000000000000000^256 ≤ 11965804840709969^256*5000^1073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        807 5000 11965804840709969 25000000000000000000 1073 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (807/5000 : ℝ)) (X := (11965804840709969/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001178588216449511/10000000000000000000 : ℝ) ≤ (1250035147372587/1250000000000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (10001178588216449511/10000000000000000000 : ℝ)^256 ≤ (1250035147372587/1250000000000000 : ℝ)^1073 := by
      have hnat : (10001178588216449511 : ℕ)^256*1250000000000000^1073 ≤ 1250035147372587^1073*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001178588216449511 10000000000000000000 1250035147372587 1250000000000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250035147372587/1250000000000000 : ℝ)) (X := (10001178588216449511/10000000000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053756160445087431/100000000000000000000 : ℝ) ≤ (5000641135209623/5000000000000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (100053756160445087431/100000000000000000000 : ℝ)^256 ≤ (5000641135209623/5000000000000000 : ℝ)^1073 := by
      have hnat : (100053756160445087431 : ℕ)^256*5000000000000000^1073 ≤ 5000641135209623^1073*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053756160445087431 100000000000000000000 5000641135209623 5000000000000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000641135209623/5000000000000000 : ℝ)) (X := (100053756160445087431/100000000000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12511965804840709969/12500000000000000000 : ℝ) ≤ (2500570840464449/2500000000000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (12511965804840709969/12500000000000000000 : ℝ)^256 ≤ (2500570840464449/2500000000000000 : ℝ)^1073 := by
      have hnat : (12511965804840709969 : ℕ)^256*2500000000000000^1073 ≤ 2500570840464449^1073*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12511965804840709969 12500000000000000000 2500570840464449 2500000000000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500570840464449/2500000000000000 : ℝ)) (X := (12511965804840709969/12500000000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1178588216449511/20000000000000000000 : ℝ) ≤ ((661064370306634323/661250000000000000 : ℝ)+2*(20021828771/12696000000000 : ℝ)*(306/3125 : ℝ))^(1073/256 : ℝ) := by
    rw [show (661064370306634323/661250000000000000 : ℝ)+2*(20021828771/12696000000000 : ℝ)*(306/3125 : ℝ)=(1250035147372587/1250000000000000 : ℝ) by norm_num, show 1+2*(1178588216449511/20000000000000000000 : ℝ)=(10001178588216449511/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11965804840709969/25000000000000000000 : ℝ)+(1178588216449511/20000000000000000000 : ℝ) ≤ ((661064370306634323/661250000000000000 : ℝ)+(20021828771/12696000000000 : ℝ)*((807/5000 : ℝ)+(306/3125 : ℝ)))^(1073/256 : ℝ) := by
    rw [show (661064370306634323/661250000000000000 : ℝ)+(20021828771/12696000000000 : ℝ)*((807/5000 : ℝ)+(306/3125 : ℝ))=(5000641135209623/5000000000000000 : ℝ) by norm_num, show 1+(11965804840709969/25000000000000000000 : ℝ)+(1178588216449511/20000000000000000000 : ℝ)=(100053756160445087431/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11965804840709969/25000000000000000000 : ℝ) ≤ ((661064370306634323/661250000000000000 : ℝ)+2*(20021828771/12696000000000 : ℝ)*(807/5000 : ℝ))^(1073/256 : ℝ) := by
    rw [show (661064370306634323/661250000000000000 : ℝ)+2*(20021828771/12696000000000 : ℝ)*(807/5000 : ℝ)=(2500570840464449/2500000000000000 : ℝ) by norm_num, show 1+2*(11965804840709969/25000000000000000000 : ℝ)=(12511965804840709969/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (661064370306634323/661250000000000000 : ℝ)*(X 1 0+X 2 0)+(20021828771/12696000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (306/3125 : ℝ)) (hi := (807/5000 : ℝ)) (c := (661064370306634323/661250000000000000 : ℝ)) (alpha := (20021828771/12696000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (661064370306634323/661250000000000000 : ℝ)*(X 0 1+X 2 1)+(20021828771/12696000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (306/3125 : ℝ)) (hi := (807/5000 : ℝ)) (c := (661064370306634323/661250000000000000 : ℝ)) (alpha := (20021828771/12696000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (661064370306634323/661250000000000000 : ℝ)*(X 0 2+X 1 2)+(20021828771/12696000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (306/3125 : ℝ)) (hi := (807/5000 : ℝ)) (c := (661064370306634323/661250000000000000 : ℝ)) (alpha := (20021828771/12696000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2049918177/10000000000 : ℝ)*X 0 0+(5428337003/10000000000 : ℝ)*X 0 1+(5230378937/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676506527/5000000000 : ℝ)*X 1 0+(-2151112839/10000000000 : ℝ)*X 1 1+(5230379041/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353012823/10000000000 : ℝ)*X 2 0+(2615189657/5000000000 : ℝ)*X 2 1+(-1075556393/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1081964259/2500000000 : ℝ)*X 0 0+(2062932873/5000000000 : ℝ)*X 0 1+(4539099359/10000000000 : ℝ)*X 0 2+(1081964259/2500000000 : ℝ)*X 1 0+(2062932873/5000000000 : ℝ)*X 1 1+(4539099359/10000000000 : ℝ)*X 1 2+(1081964259/2500000000 : ℝ)*X 2 0+(2062932873/5000000000 : ℝ)*X 2 1+(4539099359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2049938019/10000000000 : ℝ)*X 0 0+(5231208419/10000000000 : ℝ)*X 0 1+(5427502451/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302074841/10000000000 : ℝ)*X 1 0+(-976994839/5000000000 : ℝ)*X 1 1+(1085500531/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302076507/10000000000 : ℝ)*X 2 0+(678437687/1250000000 : ℝ)*X 2 1+(-1953988999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4327899017/10000000000 : ℝ)*X 0 0+(1134341977/2500000000 : ℝ)*X 0 1+(2063803457/5000000000 : ℝ)*X 0 2+(4327899017/10000000000 : ℝ)*X 1 0+(1134341977/2500000000 : ℝ)*X 1 1+(2063803457/5000000000 : ℝ)*X 1 2+(4327899017/10000000000 : ℝ)*X 2 0+(1134341977/2500000000 : ℝ)*X 2 1+(2063803457/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87381947802113182310135281/33062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (461880973/100000000000000 : ℝ)*(base19) + (975947/800000000000 : ℝ)*(base23) + (13566291/12500000000000 : ℝ)*(upper3) + (65250459/100000000000000 : ℝ)*(upper4) + (36966081/100000000000000 : ℝ)*(upper5) + (3735770086496749/100000000000000 : ℝ)*(major0) + (3735770086496749/100000000000000 : ℝ)*(major1) + (3735770086496749/100000000000000 : ℝ)*(major2) + (5051585570341641/100000000000000 : ℝ)*(sp0) + (2525796721819521/50000000000000 : ℝ)*(sp1) + (5051593783526641/100000000000000 : ℝ)*(sp2) + (1209971051272717/50000000000000 : ℝ)*(sp3) + (66681427/800000000000 : ℝ)*(sp4) + (4076830299/100000000000000 : ℝ)*(sp7) + (2419946179375733/100000000000000 : ℝ)*(f.failure) + (315724619095001/6250000000000 : ℝ)*(f.sum) + (2780015695471/634800000000000000000000000 : ℝ)*base66 + (1602133326110958469/198375000000000000000000000000000 : ℝ)*base68 + (1018549695125291531/198375000000000000000000000000000 : ℝ)*base69 + (1422368811470583469/198375000000000000000000000000000 : ℝ)*base72 + (10556732541737/3174000000000000000000000000 : ℝ)*base74 + (1171098883842791531/198375000000000000000000000000000 : ℝ)*base75 + (1490820738648708469/198375000000000000000000000000000 : ℝ)*base78 + (1343357746068708469/198375000000000000000000000000000 : ℝ)*base80 + (11654779015111/3174000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (42481917/5000000000000000000000 : ℝ)*base89 + (42481917/5000000000000000000000 : ℝ)*base91 + (42481917/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1464088090078505428934213/6612500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (447331667/100000000000000 : ℝ)*(base19) + (2437381573/100000000000000 : ℝ)*(base23) + (53509033/25000000000000 : ℝ)*(upper3) + (6806337/12500000000000 : ℝ)*(lower4) + (1946969/3125000000000 : ℝ)*(upper5) + (753485865740023/20000000000000 : ℝ)*(major0) + (753485865740023/20000000000000 : ℝ)*(major1) + (753485865740023/20000000000000 : ℝ)*(major2) + (958099341/20000000000000 : ℝ)*(sp1) + (8656065487/25000000000000 : ℝ)*(sp2) + (5094404339672943/100000000000000 : ℝ)*(sp4) + (5094399101844571/100000000000000 : ℝ)*(sp5) + (2547183639014711/50000000000000 : ℝ)*(sp6) + (2440454310346879/100000000000000 : ℝ)*(sp7) + (2440454310346879/100000000000000 : ℝ)*(f.failure) + (5094404339672943/100000000000000 : ℝ)*(f.sum) + (2635596891199/3174000000000000000000000000 : ℝ)*base66 + (133298841881534537/39675000000000000000000000000000 : ℝ)*base67 + (70686198877784537/39675000000000000000000000000000 : ℝ)*base69 + (63131169601590463/39675000000000000000000000000000 : ℝ)*base72 + (8017212109499/3174000000000000000000000000 : ℝ)*base73 + (5598860798309537/39675000000000000000000000000000 : ℝ)*base75 + (71945427753434537/39675000000000000000000000000000 : ℝ)*base77 + (106554460941690463/39675000000000000000000000000000 : ℝ)*base80 + (188548490861/126960000000000000000000000 : ℝ)*base81 + (6370071/5000000000000000000000 : ℝ)*base89 + (6370071/5000000000000000000000 : ℝ)*base91 + (6370071/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1333_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (807/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (306/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1083/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7509/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1333_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1333_s4_0 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-205145189/1000000000 : ℝ)*x 0 + (338493503/625000000 : ℝ)*x 1 + (524181323/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205145189/1000000000 : ℝ)^4293 ≤ (499605879101/4000000000000 : ℝ)^3269 := by
    have hnat : (205145189 : ℕ)^4293*4000000000000^3269 ≤ 499605879101^3269*1000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205145189 1000000000 499605879101 4000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338493503/625000000 : ℝ)^4293 ≤ (44693432342769/100000000000000 : ℝ)^3269 := by
    have hnat : (338493503 : ℕ)^4293*100000000000000^3269 ≤ 44693432342769^3269*625000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338493503 625000000 44693432342769 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524181323/1000000000 : ℝ)^4293 ≤ (21408210333441/50000000000000 : ℝ)^3269 := by
    have hnat : (524181323 : ℕ)^4293*50000000000000^3269 ≤ 21408210333441^3269*1000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524181323 1000000000 21408210333441 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-205145189/1000000000 : ℝ), (338493503/625000000 : ℝ), (524181323/1000000000 : ℝ)] ![(499605879101/4000000000000 : ℝ), (44693432342769/100000000000000 : ℝ), (21408210333441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-205145189/1000000000 : ℝ)|^4293 ≤ (499605879101/4000000000000 : ℝ)^3269
        have hw : |(-205145189/1000000000 : ℝ)|=(205145189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338493503/625000000 : ℝ)|^4293 ≤ (44693432342769/100000000000000 : ℝ)^3269
        have hw : |(338493503/625000000 : ℝ)|=(338493503/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524181323/1000000000 : ℝ)|^4293 ≤ (21408210333441/50000000000000 : ℝ)^3269
        have hw : |(524181323/1000000000 : ℝ)|=(524181323/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s4_1 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674923657/5000000000 : ℝ)*x 0 + (-1070103719/5000000000 : ℝ)*x 1 + (2620906537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674923657/5000000000 : ℝ)^4293 ≤ (879580326081/2000000000000 : ℝ)^3269 := by
    have hnat : (2674923657 : ℕ)^4293*2000000000000^3269 ≤ 879580326081^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674923657 5000000000 879580326081 2000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1070103719/5000000000 : ℝ)^4293 ≤ (13204564693503/100000000000000 : ℝ)^3269 := by
    have hnat : (1070103719 : ℕ)^4293*100000000000000^3269 ≤ 13204564693503^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070103719 5000000000 13204564693503 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620906537/5000000000 : ℝ)^4293 ≤ (42816418993483/100000000000000 : ℝ)^3269 := by
    have hnat : (2620906537 : ℕ)^4293*100000000000000^3269 ≤ 42816418993483^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620906537 5000000000 42816418993483 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674923657/5000000000 : ℝ), (-1070103719/5000000000 : ℝ), (2620906537/5000000000 : ℝ)] ![(879580326081/2000000000000 : ℝ), (13204564693503/100000000000000 : ℝ), (42816418993483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674923657/5000000000 : ℝ)|^4293 ≤ (879580326081/2000000000000 : ℝ)^3269
        have hw : |(2674923657/5000000000 : ℝ)|=(2674923657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1070103719/5000000000 : ℝ)|^4293 ≤ (13204564693503/100000000000000 : ℝ)^3269
        have hw : |(-1070103719/5000000000 : ℝ)|=(1070103719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620906537/5000000000 : ℝ)|^4293 ≤ (42816418993483/100000000000000 : ℝ)^3269
        have hw : |(2620906537/5000000000 : ℝ)|=(2620906537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s4_2 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334365467/625000000 : ℝ)*x 0 + (2620906399/5000000000 : ℝ)*x 1 + (-2140207593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334365467/625000000 : ℝ)^4293 ≤ (5497377251221/12500000000000 : ℝ)^3269 := by
    have hnat : (334365467 : ℕ)^4293*12500000000000^3269 ≤ 5497377251221^3269*625000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334365467 625000000 5497377251221 12500000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620906399/5000000000 : ℝ)^4293 ≤ (8563283206571/20000000000000 : ℝ)^3269 := by
    have hnat : (2620906399 : ℕ)^4293*20000000000000^3269 ≤ 8563283206571^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620906399 5000000000 8563283206571 20000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2140207593/10000000000 : ℝ)^4293 ≤ (13204565949377/100000000000000 : ℝ)^3269 := by
    have hnat : (2140207593 : ℕ)^4293*100000000000000^3269 ≤ 13204565949377^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140207593 10000000000 13204565949377 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334365467/625000000 : ℝ), (2620906399/5000000000 : ℝ), (-2140207593/10000000000 : ℝ)] ![(5497377251221/12500000000000 : ℝ), (8563283206571/20000000000000 : ℝ), (13204565949377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334365467/625000000 : ℝ)|^4293 ≤ (5497377251221/12500000000000 : ℝ)^3269
        have hw : |(334365467/625000000 : ℝ)|=(334365467/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620906399/5000000000 : ℝ)|^4293 ≤ (8563283206571/20000000000000 : ℝ)^3269
        have hw : |(2620906399/5000000000 : ℝ)|=(2620906399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2140207593/10000000000 : ℝ)|^4293 ≤ (13204565949377/100000000000000 : ℝ)^3269
        have hw : |(-2140207593/10000000000 : ℝ)|=(2140207593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s4_3 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2164394491/5000000000 : ℝ)*x 0 + (2075334441/5000000000 : ℝ)*x 1 + (2257032203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164394491/5000000000 : ℝ)^4293 ≤ (1040662252797/3125000000000 : ℝ)^3269 := by
    have hnat : (2164394491 : ℕ)^4293*3125000000000^3269 ≤ 1040662252797^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164394491 5000000000 1040662252797 3125000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2075334441/5000000000 : ℝ)^4293 ≤ (31513398778569/100000000000000 : ℝ)^3269 := by
    have hnat : (2075334441 : ℕ)^4293*100000000000000^3269 ≤ 31513398778569^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075334441 5000000000 31513398778569 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257032203/5000000000 : ℝ)^4293 ≤ (17592704556827/50000000000000 : ℝ)^3269 := by
    have hnat : (2257032203 : ℕ)^4293*50000000000000^3269 ≤ 17592704556827^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257032203 5000000000 17592704556827 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2164394491/5000000000 : ℝ), (2075334441/5000000000 : ℝ), (2257032203/5000000000 : ℝ)] ![(1040662252797/3125000000000 : ℝ), (31513398778569/100000000000000 : ℝ), (17592704556827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2164394491/5000000000 : ℝ)|^4293 ≤ (1040662252797/3125000000000 : ℝ)^3269
        have hw : |(2164394491/5000000000 : ℝ)|=(2164394491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2075334441/5000000000 : ℝ)|^4293 ≤ (31513398778569/100000000000000 : ℝ)^3269
        have hw : |(2075334441/5000000000 : ℝ)|=(2075334441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2257032203/5000000000 : ℝ)|^4293 ≤ (17592704556827/50000000000000 : ℝ)^3269
        have hw : |(2257032203/5000000000 : ℝ)|=(2257032203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s4_4 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2051465523/10000000000 : ℝ)*x 0 + (1048491003/2000000000 : ℝ)*x 1 + (2707625357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2051465523/10000000000 : ℝ)^4293 ≤ (2498051196387/20000000000000 : ℝ)^3269 := by
    have hnat : (2051465523 : ℕ)^4293*20000000000000^3269 ≤ 2498051196387^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051465523 10000000000 2498051196387 20000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048491003/2000000000 : ℝ)^4293 ≤ (1070582629279/2500000000000 : ℝ)^3269 := by
    have hnat : (1048491003 : ℕ)^4293*2500000000000^3269 ≤ 1070582629279^3269*2000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048491003 2000000000 1070582629279 2500000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707625357/5000000000 : ℝ)^4293 ≤ (2234321941157/5000000000000 : ℝ)^3269 := by
    have hnat : (2707625357 : ℕ)^4293*5000000000000^3269 ≤ 2234321941157^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707625357 5000000000 2234321941157 5000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2051465523/10000000000 : ℝ), (1048491003/2000000000 : ℝ), (2707625357/5000000000 : ℝ)] ![(2498051196387/20000000000000 : ℝ), (1070582629279/2500000000000 : ℝ), (2234321941157/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2051465523/10000000000 : ℝ)|^4293 ≤ (2498051196387/20000000000000 : ℝ)^3269
        have hw : |(-2051465523/10000000000 : ℝ)|=(2051465523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048491003/2000000000 : ℝ)|^4293 ≤ (1070582629279/2500000000000 : ℝ)^3269
        have hw : |(1048491003/2000000000 : ℝ)|=(1048491003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707625357/5000000000 : ℝ)|^4293 ≤ (2234321941157/5000000000000 : ℝ)^3269
        have hw : |(2707625357/5000000000 : ℝ)|=(2707625357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s4_5 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305054211/10000000000 : ℝ)*x 0 + (-1966769907/10000000000 : ℝ)*x 1 + (1083050143/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305054211/10000000000 : ℝ)^4293 ≤ (21748039780059/50000000000000 : ℝ)^3269 := by
    have hnat : (5305054211 : ℕ)^4293*50000000000000^3269 ≤ 21748039780059^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305054211 10000000000 21748039780059 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1966769907/10000000000 : ℝ)^4293 ≤ (2954370396547/25000000000000 : ℝ)^3269 := by
    have hnat : (1966769907 : ℕ)^4293*25000000000000^3269 ≤ 2954370396547^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966769907 10000000000 2954370396547 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083050143/2000000000 : ℝ)^4293 ≤ (5585804854247/12500000000000 : ℝ)^3269 := by
    have hnat : (1083050143 : ℕ)^4293*12500000000000^3269 ≤ 5585804854247^3269*2000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083050143 2000000000 5585804854247 12500000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305054211/10000000000 : ℝ), (-1966769907/10000000000 : ℝ), (1083050143/2000000000 : ℝ)] ![(21748039780059/50000000000000 : ℝ), (2954370396547/25000000000000 : ℝ), (5585804854247/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305054211/10000000000 : ℝ)|^4293 ≤ (21748039780059/50000000000000 : ℝ)^3269
        have hw : |(5305054211/10000000000 : ℝ)|=(5305054211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1966769907/10000000000 : ℝ)|^4293 ≤ (2954370396547/25000000000000 : ℝ)^3269
        have hw : |(-1966769907/10000000000 : ℝ)|=(1966769907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083050143/2000000000 : ℝ)|^4293 ≤ (5585804854247/12500000000000 : ℝ)^3269
        have hw : |(1083050143/2000000000 : ℝ)|=(1083050143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s4_6 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305054219/10000000000 : ℝ)*x 0 + (338453169/625000000 : ℝ)*x 1 + (-245846239/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305054219/10000000000 : ℝ)^4293 ≤ (2718504977891/6250000000000 : ℝ)^3269 := by
    have hnat : (5305054219 : ℕ)^4293*6250000000000^3269 ≤ 2718504977891^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305054219 10000000000 2718504977891 6250000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338453169/625000000 : ℝ)^4293 ≤ (44686438714771/100000000000000 : ℝ)^3269 := by
    have hnat : (338453169 : ℕ)^4293*100000000000000^3269 ≤ 44686438714771^3269*625000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338453169 625000000 44686438714771 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245846239/1250000000 : ℝ)^4293 ≤ (5908740812821/50000000000000 : ℝ)^3269 := by
    have hnat : (245846239 : ℕ)^4293*50000000000000^3269 ≤ 5908740812821^3269*1250000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245846239 1250000000 5908740812821 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305054219/10000000000 : ℝ), (338453169/625000000 : ℝ), (-245846239/1250000000 : ℝ)] ![(2718504977891/6250000000000 : ℝ), (44686438714771/100000000000000 : ℝ), (5908740812821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305054219/10000000000 : ℝ)|^4293 ≤ (2718504977891/6250000000000 : ℝ)^3269
        have hw : |(5305054219/10000000000 : ℝ)|=(5305054219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338453169/625000000 : ℝ)|^4293 ≤ (44686438714771/100000000000000 : ℝ)^3269
        have hw : |(338453169/625000000 : ℝ)|=(338453169/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-245846239/1250000000 : ℝ)|^4293 ≤ (5908740812821/50000000000000 : ℝ)^3269
        have hw : |(-245846239/1250000000 : ℝ)|=(245846239/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s4_7 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4328816899/10000000000 : ℝ)*x 0 + (4512724227/10000000000 : ℝ)*x 1 + (2076008171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328816899/10000000000 : ℝ)^4293 ≤ (33301474128083/100000000000000 : ℝ)^3269 := by
    have hnat : (4328816899 : ℕ)^4293*100000000000000^3269 ≤ 33301474128083^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328816899 10000000000 33301474128083 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4512724227/10000000000 : ℝ)^4293 ≤ (879292283657/2500000000000 : ℝ)^3269 := by
    have hnat : (4512724227 : ℕ)^4293*2500000000000^3269 ≤ 879292283657^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512724227 10000000000 879292283657 2500000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2076008171/5000000000 : ℝ)^4293 ≤ (31526834502929/100000000000000 : ℝ)^3269 := by
    have hnat : (2076008171 : ℕ)^4293*100000000000000^3269 ≤ 31526834502929^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076008171 5000000000 31526834502929 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328816899/10000000000 : ℝ), (4512724227/10000000000 : ℝ), (2076008171/5000000000 : ℝ)] ![(33301474128083/100000000000000 : ℝ), (879292283657/2500000000000 : ℝ), (31526834502929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328816899/10000000000 : ℝ)|^4293 ≤ (33301474128083/100000000000000 : ℝ)^3269
        have hw : |(4328816899/10000000000 : ℝ)|=(4328816899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4512724227/10000000000 : ℝ)|^4293 ≤ (879292283657/2500000000000 : ℝ)^3269
        have hw : |(4512724227/10000000000 : ℝ)|=(4512724227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2076008171/5000000000 : ℝ)|^4293 ≤ (31526834502929/100000000000000 : ℝ)^3269
        have hw : |(2076008171/5000000000 : ℝ)|=(2076008171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1333_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7509/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1083/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (5537/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14759/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7509/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1083/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7509/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1083/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7509/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1083/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7509/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1083/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7509/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1083/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7509/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1083/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1083/10000 : ℝ) ^ (1073/256 : ℝ) ≤ (1123687869414253/12500000000000000000 : ℝ) := by
    have hpowers : (1083/10000 : ℝ)^1073 ≤ (1123687869414253/12500000000000000000 : ℝ)^256 := by
      have hnat : (1083 : ℕ)^1073*12500000000000000000^256 ≤ 1123687869414253^256*10000^1073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1083 10000 1123687869414253 12500000000000000000 1073 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1083/10000 : ℝ)) (X := (1123687869414253/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7509/50000 : ℝ) ^ (1073/256 : ℝ) ≤ (7077449926731587/20000000000000000000 : ℝ) := by
    have hpowers : (7509/50000 : ℝ)^1073 ≤ (7077449926731587/20000000000000000000 : ℝ)^256 := by
      have hnat : (7509 : ℕ)^1073*20000000000000000000^256 ≤ 7077449926731587^256*50000^1073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7509 50000 7077449926731587 20000000000000000000 1073 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7509/50000 : ℝ)) (X := (7077449926731587/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251123687869414253/6250000000000000000 : ℝ) ≤ (1250053614987277/1250000000000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (6251123687869414253/6250000000000000000 : ℝ)^256 ≤ (1250053614987277/1250000000000000 : ℝ)^1073 := by
      have hnat : (6251123687869414253 : ℕ)^256*1250000000000000^1073 ≤ 1250053614987277^1073*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251123687869414253 6250000000000000000 1250053614987277 1250000000000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250053614987277/1250000000000000 : ℝ)) (X := (6251123687869414253/6250000000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044376752588971959/100000000000000000000 : ℝ) ≤ (7813327013183/7812500000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (100044376752588971959/100000000000000000000 : ℝ)^256 ≤ (7813327013183/7812500000000 : ℝ)^1073 := by
      have hnat : (100044376752588971959 : ℕ)^256*7812500000000^1073 ≤ 7813327013183^1073*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044376752588971959 100000000000000000000 7813327013183 7812500000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (7813327013183/7812500000000 : ℝ)) (X := (100044376752588971959/100000000000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007077449926731587/10000000000000000000 : ℝ) ≤ (1250211029231283/1250000000000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (10007077449926731587/10000000000000000000 : ℝ)^256 ≤ (1250211029231283/1250000000000000 : ℝ)^1073 := by
      have hnat : (10007077449926731587 : ℕ)^256*1250000000000000^1073 ≤ 1250211029231283^1073*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007077449926731587 10000000000000000000 1250211029231283 1250000000000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250211029231283/1250000000000000 : ℝ)) (X := (10007077449926731587/10000000000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1123687869414253/12500000000000000000 : ℝ) ≤ ((218063322637672129/218125000000000000 : ℝ)+2*(78707122003/52350000000000 : ℝ)*(1083/10000 : ℝ))^(1073/256 : ℝ) := by
    rw [show (218063322637672129/218125000000000000 : ℝ)+2*(78707122003/52350000000000 : ℝ)*(1083/10000 : ℝ)=(1250053614987277/1250000000000000 : ℝ) by norm_num, show 1+2*(1123687869414253/12500000000000000000 : ℝ)=(6251123687869414253/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7077449926731587/20000000000000000000 : ℝ)+(1123687869414253/12500000000000000000 : ℝ) ≤ ((218063322637672129/218125000000000000 : ℝ)+(78707122003/52350000000000 : ℝ)*((7509/50000 : ℝ)+(1083/10000 : ℝ)))^(1073/256 : ℝ) := by
    rw [show (218063322637672129/218125000000000000 : ℝ)+(78707122003/52350000000000 : ℝ)*((7509/50000 : ℝ)+(1083/10000 : ℝ))=(7813327013183/7812500000000 : ℝ) by norm_num, show 1+(7077449926731587/20000000000000000000 : ℝ)+(1123687869414253/12500000000000000000 : ℝ)=(100044376752588971959/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7077449926731587/20000000000000000000 : ℝ) ≤ ((218063322637672129/218125000000000000 : ℝ)+2*(78707122003/52350000000000 : ℝ)*(7509/50000 : ℝ))^(1073/256 : ℝ) := by
    rw [show (218063322637672129/218125000000000000 : ℝ)+2*(78707122003/52350000000000 : ℝ)*(7509/50000 : ℝ)=(1250211029231283/1250000000000000 : ℝ) by norm_num, show 1+2*(7077449926731587/20000000000000000000 : ℝ)=(10007077449926731587/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (218063322637672129/218125000000000000 : ℝ)*(X 1 0+X 2 0)+(78707122003/52350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (1083/10000 : ℝ)) (hi := (7509/50000 : ℝ)) (c := (218063322637672129/218125000000000000 : ℝ)) (alpha := (78707122003/52350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (218063322637672129/218125000000000000 : ℝ)*(X 0 1+X 2 1)+(78707122003/52350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (1083/10000 : ℝ)) (hi := (7509/50000 : ℝ)) (c := (218063322637672129/218125000000000000 : ℝ)) (alpha := (78707122003/52350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (218063322637672129/218125000000000000 : ℝ)*(X 0 2+X 1 2)+(78707122003/52350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (1083/10000 : ℝ)) (hi := (7509/50000 : ℝ)) (c := (218063322637672129/218125000000000000 : ℝ)) (alpha := (78707122003/52350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-205145189/1000000000 : ℝ)*X 0 0+(338493503/625000000 : ℝ)*X 0 1+(524181323/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674923657/5000000000 : ℝ)*X 1 0+(-1070103719/5000000000 : ℝ)*X 1 1+(2620906537/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334365467/625000000 : ℝ)*X 2 0+(2620906399/5000000000 : ℝ)*X 2 1+(-2140207593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2164394491/5000000000 : ℝ)*X 0 0+(2075334441/5000000000 : ℝ)*X 0 1+(2257032203/5000000000 : ℝ)*X 0 2+(2164394491/5000000000 : ℝ)*X 1 0+(2075334441/5000000000 : ℝ)*X 1 1+(2257032203/5000000000 : ℝ)*X 1 2+(2164394491/5000000000 : ℝ)*X 2 0+(2075334441/5000000000 : ℝ)*X 2 1+(2257032203/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2051465523/10000000000 : ℝ)*X 0 0+(1048491003/2000000000 : ℝ)*X 0 1+(2707625357/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305054211/10000000000 : ℝ)*X 1 0+(-1966769907/10000000000 : ℝ)*X 1 1+(1083050143/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305054219/10000000000 : ℝ)*X 2 0+(338453169/625000000 : ℝ)*X 2 1+(-245846239/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4328816899/10000000000 : ℝ)*X 0 0+(4512724227/10000000000 : ℝ)*X 0 1+(2076008171/5000000000 : ℝ)*X 0 2+(4328816899/10000000000 : ℝ)*X 1 0+(4512724227/10000000000 : ℝ)*X 1 1+(2076008171/5000000000 : ℝ)*X 1 2+(4328816899/10000000000 : ℝ)*X 2 0+(4512724227/10000000000 : ℝ)*X 2 1+(2076008171/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6146305058006820422793/1745000000000000000000000000 : ℝ) := by norm_num
    linear_combination (735367659/100000000000000 : ℝ)*(base19) + (198269769/20000000000000 : ℝ)*(base23) + (61752701/100000000000000 : ℝ)*(lower2) + (44715401/50000000000000 : ℝ)*(upper3) + (53968493/50000000000000 : ℝ)*(lower4) + (4248127232483561/100000000000000 : ℝ)*(major0) + (4248127232483561/100000000000000 : ℝ)*(major1) + (4248127232483561/100000000000000 : ℝ)*(major2) + (114888102180621/2000000000000 : ℝ)*(sp0) + (229776568997463/4000000000000 : ℝ)*(sp1) + (5744413968955389/100000000000000 : ℝ)*(sp2) + (110073207152087/4000000000000 : ℝ)*(sp3) + (307852287/3125000000000 : ℝ)*(sp4) + (9208452779/100000000000000 : ℝ)*(sp7) + (1375919693627477/50000000000000 : ℝ)*(f.failure) + (2872207480152117/50000000000000 : ℝ)*(f.sum) + (69872865592799/5235000000000000000000000000 : ℝ)*base66 + (56257148052089107/65437500000000000000000000000000 : ℝ)*base67 + (280358402174151607/65437500000000000000000000000000 : ℝ)*base69 + (345251279058285893/65437500000000000000000000000000 : ℝ)*base72 + (15623722207889/5235000000000000000000000000 : ℝ)*base74 + (815641296069276607/65437500000000000000000000000000 : ℝ)*base75 + (131814901541160893/65437500000000000000000000000000 : ℝ)*base78 + (97596901592535893/65437500000000000000000000000000 : ℝ)*base80 + (537386435519/5235000000000000000000000000 : ℝ)*base82 + (29945373/2500000000000000000000 : ℝ)*base89 + (29945373/2500000000000000000000 : ℝ)*base91 + (29945373/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (125281787504853800016819231/10906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40532501/2000000000000 : ℝ)*(base19) + (2198843813/100000000000000 : ℝ)*(base23) + (11744349/5000000000000 : ℝ)*(upper3) + (18766651/25000000000000 : ℝ)*(lower4) + (120442749/50000000000000 : ℝ)*(upper5) + (4279753042528637/100000000000000 : ℝ)*(major0) + (4279753042528637/100000000000000 : ℝ)*(major1) + (4279753042528637/100000000000000 : ℝ)*(major2) + (10015826281/25000000000000 : ℝ)*(sp1) + (8533544791/20000000000000 : ℝ)*(sp2) + (2893589920255671/50000000000000 : ℝ)*(sp4) + (361696109411323/6250000000000 : ℝ)*(sp5) + (2893567486971787/50000000000000 : ℝ)*(sp6) + (2772325861640751/100000000000000 : ℝ)*(sp7) + (2772325861640751/100000000000000 : ℝ)*(f.failure) + (2893589920255671/50000000000000 : ℝ)*(f.sum) + (23870197296683/5235000000000000000000000000 : ℝ)*base66 + (490860987901099519/65437500000000000000000000000000 : ℝ)*base67 + (115583703221037019/65437500000000000000000000000000 : ℝ)*base69 + (419304745006525481/65437500000000000000000000000000 : ℝ)*base72 + (3434717219407/5235000000000000000000000000 : ℝ)*base73 + (284325545153787019/65437500000000000000000000000000 : ℝ)*base75 + (341229833065099519/65437500000000000000000000000000 : ℝ)*base77 + (463065427263400481/65437500000000000000000000000000 : ℝ)*base80 + (9446870599343/5235000000000000000000000000 : ℝ)*base82 + (17833799/5000000000000000000000 : ℝ)*base89 + (17833799/5000000000000000000000 : ℝ)*base91 + (17833799/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1333_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7509/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1083/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5537/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1333_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1333_s5_0 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-205171809/1000000000 : ℝ)*x 0 + (270679629/500000000 : ℝ)*x 1 + (2621970839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205171809/1000000000 : ℝ)^4293 ≤ (2498455090999/20000000000000 : ℝ)^3269 := by
    have hnat : (205171809 : ℕ)^4293*20000000000000^3269 ≤ 2498455090999^3269*1000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205171809 1000000000 2498455090999 20000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270679629/500000000 : ℝ)^4293 ≤ (893369414641/2000000000000 : ℝ)^3269 := by
    have hnat : (270679629 : ℕ)^4293*2000000000000^3269 ≤ 893369414641^3269*500000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270679629 500000000 893369414641 2000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621970839/5000000000 : ℝ)^4293 ≤ (42839253796641/100000000000000 : ℝ)^3269 := by
    have hnat : (2621970839 : ℕ)^4293*100000000000000^3269 ≤ 42839253796641^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621970839 5000000000 42839253796641 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-205171809/1000000000 : ℝ), (270679629/500000000 : ℝ), (2621970839/5000000000 : ℝ)] ![(2498455090999/20000000000000 : ℝ), (893369414641/2000000000000 : ℝ), (42839253796641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-205171809/1000000000 : ℝ)|^4293 ≤ (2498455090999/20000000000000 : ℝ)^3269
        have hw : |(-205171809/1000000000 : ℝ)|=(205171809/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270679629/500000000 : ℝ)|^4293 ≤ (893369414641/2000000000000 : ℝ)^3269
        have hw : |(270679629/500000000 : ℝ)|=(270679629/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621970839/5000000000 : ℝ)|^4293 ≤ (42839253796641/100000000000000 : ℝ)^3269
        have hw : |(2621970839/5000000000 : ℝ)|=(2621970839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s5_1 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674629977/5000000000 : ℝ)*x 0 + (-2138171447/10000000000 : ℝ)*x 1 + (65549271/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674629977/5000000000 : ℝ)^4293 ≤ (43972675461189/100000000000000 : ℝ)^3269 := by
    have hnat : (2674629977 : ℕ)^4293*100000000000000^3269 ≤ 43972675461189^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674629977 5000000000 43972675461189 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2138171447/10000000000 : ℝ)^4293 ≤ (527522828767/4000000000000 : ℝ)^3269 := by
    have hnat : (2138171447 : ℕ)^4293*4000000000000^3269 ≤ 527522828767^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138171447 10000000000 527522828767 4000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65549271/125000000 : ℝ)^4293 ≤ (21419626909049/50000000000000 : ℝ)^3269 := by
    have hnat : (65549271 : ℕ)^4293*50000000000000^3269 ≤ 21419626909049^3269*125000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65549271 125000000 21419626909049 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674629977/5000000000 : ℝ), (-2138171447/10000000000 : ℝ), (65549271/125000000 : ℝ)] ![(43972675461189/100000000000000 : ℝ), (527522828767/4000000000000 : ℝ), (21419626909049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674629977/5000000000 : ℝ)|^4293 ≤ (43972675461189/100000000000000 : ℝ)^3269
        have hw : |(2674629977/5000000000 : ℝ)|=(2674629977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2138171447/10000000000 : ℝ)|^4293 ≤ (527522828767/4000000000000 : ℝ)^3269
        have hw : |(-2138171447/10000000000 : ℝ)|=(2138171447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65549271/125000000 : ℝ)|^4293 ≤ (21419626909049/50000000000000 : ℝ)^3269
        have hw : |(65549271/125000000 : ℝ)|=(65549271/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s5_2 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534925997/1000000000 : ℝ)*x 0 + (2621970839/5000000000 : ℝ)*x 1 + (-1069085713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534925997/1000000000 : ℝ)^4293 ≤ (21986337816957/50000000000000 : ℝ)^3269 := by
    have hnat : (534925997 : ℕ)^4293*50000000000000^3269 ≤ 21986337816957^3269*1000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534925997 1000000000 21986337816957 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621970839/5000000000 : ℝ)^4293 ≤ (42839253796641/100000000000000 : ℝ)^3269 := by
    have hnat : (2621970839 : ℕ)^4293*100000000000000^3269 ≤ 42839253796641^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621970839 5000000000 42839253796641 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1069085713/5000000000 : ℝ)^4293 ≤ (527522821963/4000000000000 : ℝ)^3269 := by
    have hnat : (1069085713 : ℕ)^4293*4000000000000^3269 ≤ 527522821963^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069085713 5000000000 527522821963 4000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534925997/1000000000 : ℝ), (2621970839/5000000000 : ℝ), (-1069085713/5000000000 : ℝ)] ![(21986337816957/50000000000000 : ℝ), (42839253796641/100000000000000 : ℝ), (527522821963/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534925997/1000000000 : ℝ)|^4293 ≤ (21986337816957/50000000000000 : ℝ)^3269
        have hw : |(534925997/1000000000 : ℝ)|=(534925997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621970839/5000000000 : ℝ)|^4293 ≤ (42839253796641/100000000000000 : ℝ)^3269
        have hw : |(2621970839/5000000000 : ℝ)|=(2621970839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1069085713/5000000000 : ℝ)|^4293 ≤ (527522821963/4000000000000 : ℝ)^3269
        have hw : |(-1069085713/5000000000 : ℝ)|=(1069085713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s5_3 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4328948667/10000000000 : ℝ)*x 0 + (16621101/40000000 : ℝ)*x 1 + (4509418431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328948667/10000000000 : ℝ)^4293 ≤ (16651402677721/50000000000000 : ℝ)^3269 := by
    have hnat : (4328948667 : ℕ)^4293*50000000000000^3269 ≤ 16651402677721^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328948667 10000000000 16651402677721 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16621101/40000000 : ℝ)^4293 ≤ (15779667603049/50000000000000 : ℝ)^3269 := by
    have hnat : (16621101 : ℕ)^4293*50000000000000^3269 ≤ 15779667603049^3269*40000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16621101 40000000 15779667603049 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4509418431/10000000000 : ℝ)^4293 ≤ (17568929713463/50000000000000 : ℝ)^3269 := by
    have hnat : (4509418431 : ℕ)^4293*50000000000000^3269 ≤ 17568929713463^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509418431 10000000000 17568929713463 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328948667/10000000000 : ℝ), (16621101/40000000 : ℝ), (4509418431/10000000000 : ℝ)] ![(16651402677721/50000000000000 : ℝ), (15779667603049/50000000000000 : ℝ), (17568929713463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328948667/10000000000 : ℝ)|^4293 ≤ (16651402677721/50000000000000 : ℝ)^3269
        have hw : |(4328948667/10000000000 : ℝ)|=(4328948667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16621101/40000000 : ℝ)|^4293 ≤ (15779667603049/50000000000000 : ℝ)^3269
        have hw : |(16621101/40000000 : ℝ)|=(16621101/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4509418431/10000000000 : ℝ)|^4293 ≤ (17568929713463/50000000000000 : ℝ)^3269
        have hw : |(4509418431/10000000000 : ℝ)|=(4509418431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s5_4 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1025865329/5000000000 : ℝ)*x 0 + (2622275757/5000000000 : ℝ)*x 1 + (10825959/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1025865329/5000000000 : ℝ)^4293 ≤ (1561546993517/12500000000000 : ℝ)^3269 := by
    have hnat : (1025865329 : ℕ)^4293*12500000000000^3269 ≤ 1561546993517^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025865329 5000000000 1561546993517 12500000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622275757/5000000000 : ℝ)^4293 ≤ (856915928117/2000000000000 : ℝ)^3269 := by
    have hnat : (2622275757 : ℕ)^4293*2000000000000^3269 ≤ 856915928117^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622275757 5000000000 856915928117 2000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10825959/20000000 : ℝ)^4293 ≤ (22330913814961/50000000000000 : ℝ)^3269 := by
    have hnat : (10825959 : ℕ)^4293*50000000000000^3269 ≤ 22330913814961^3269*20000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10825959 20000000 22330913814961 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1025865329/5000000000 : ℝ), (2622275757/5000000000 : ℝ), (10825959/20000000 : ℝ)] ![(1561546993517/12500000000000 : ℝ), (856915928117/2000000000000 : ℝ), (22330913814961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1025865329/5000000000 : ℝ)|^4293 ≤ (1561546993517/12500000000000 : ℝ)^3269
        have hw : |(-1025865329/5000000000 : ℝ)|=(1025865329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622275757/5000000000 : ℝ)|^4293 ≤ (856915928117/2000000000000 : ℝ)^3269
        have hw : |(2622275757/5000000000 : ℝ)|=(2622275757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10825959/20000000 : ℝ)|^4293 ≤ (22330913814961/50000000000000 : ℝ)^3269
        have hw : |(10825959/20000000 : ℝ)|=(10825959/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s5_5 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305607431/10000000000 : ℝ)*x 0 + (-492283381/2500000000 : ℝ)*x 1 + (5412979523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305607431/10000000000 : ℝ)^4293 ≤ (5437754541933/12500000000000 : ℝ)^3269 := by
    have hnat : (5305607431 : ℕ)^4293*12500000000000^3269 ≤ 5437754541933^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305607431 10000000000 5437754541933 12500000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (492283381/2500000000 : ℝ)^4293 ≤ (11836135766381/100000000000000 : ℝ)^3269 := by
    have hnat : (492283381 : ℕ)^4293*100000000000000^3269 ≤ 11836135766381^3269*2500000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492283381 2500000000 11836135766381 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412979523/10000000000 : ℝ)^4293 ≤ (1395682121223/3125000000000 : ℝ)^3269 := by
    have hnat : (5412979523 : ℕ)^4293*3125000000000^3269 ≤ 1395682121223^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412979523 10000000000 1395682121223 3125000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305607431/10000000000 : ℝ), (-492283381/2500000000 : ℝ), (5412979523/10000000000 : ℝ)] ![(5437754541933/12500000000000 : ℝ), (11836135766381/100000000000000 : ℝ), (1395682121223/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305607431/10000000000 : ℝ)|^4293 ≤ (5437754541933/12500000000000 : ℝ)^3269
        have hw : |(5305607431/10000000000 : ℝ)|=(5305607431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-492283381/2500000000 : ℝ)|^4293 ≤ (11836135766381/100000000000000 : ℝ)^3269
        have hw : |(-492283381/2500000000 : ℝ)|=(492283381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412979523/10000000000 : ℝ)|^4293 ≤ (1395682121223/3125000000000 : ℝ)^3269
        have hw : |(5412979523/10000000000 : ℝ)|=(5412979523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s5_6 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305607267/10000000000 : ℝ)*x 0 + (5412979677/10000000000 : ℝ)*x 1 + (-1969133537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305607267/10000000000 : ℝ)^4293 ≤ (10875508642393/25000000000000 : ℝ)^3269 := by
    have hnat : (5305607267 : ℕ)^4293*25000000000000^3269 ≤ 10875508642393^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305607267 10000000000 10875508642393 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412979677/10000000000 : ℝ)^4293 ≤ (2791364346737/6250000000000 : ℝ)^3269 := by
    have hnat : (5412979677 : ℕ)^4293*6250000000000^3269 ≤ 2791364346737^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412979677 10000000000 2791364346737 6250000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1969133537/10000000000 : ℝ)^4293 ≤ (11836135869/100000000000 : ℝ)^3269 := by
    have hnat : (1969133537 : ℕ)^4293*100000000000^3269 ≤ 11836135869^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1969133537 10000000000 11836135869 100000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305607267/10000000000 : ℝ), (5412979677/10000000000 : ℝ), (-1969133537/10000000000 : ℝ)] ![(10875508642393/25000000000000 : ℝ), (2791364346737/6250000000000 : ℝ), (11836135869/100000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305607267/10000000000 : ℝ)|^4293 ≤ (10875508642393/25000000000000 : ℝ)^3269
        have hw : |(5305607267/10000000000 : ℝ)|=(5305607267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412979677/10000000000 : ℝ)|^4293 ≤ (2791364346737/6250000000000 : ℝ)^3269
        have hw : |(5412979677/10000000000 : ℝ)|=(5412979677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1969133537/10000000000 : ℝ)|^4293 ≤ (11836135869/100000000000 : ℝ)^3269
        have hw : |(-1969133537/10000000000 : ℝ)|=(1969133537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s5_7 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (27056091/62500000 : ℝ)*x 0 + (4508145549/10000000000 : ℝ)*x 1 + (4156554817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27056091/62500000 : ℝ)^4293 ≤ (33303066949051/100000000000000 : ℝ)^3269 := by
    have hnat : (27056091 : ℕ)^4293*100000000000000^3269 ≤ 33303066949051^3269*62500000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27056091 62500000 33303066949051 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508145549/10000000000 : ℝ)^4293 ≤ (17562417334257/50000000000000 : ℝ)^3269 := by
    have hnat : (4508145549 : ℕ)^4293*50000000000000^3269 ≤ 17562417334257^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508145549 10000000000 17562417334257 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4156554817/10000000000 : ℝ)^4293 ≤ (3157209835959/10000000000000 : ℝ)^3269 := by
    have hnat : (4156554817 : ℕ)^4293*10000000000000^3269 ≤ 3157209835959^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4156554817 10000000000 3157209835959 10000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27056091/62500000 : ℝ), (4508145549/10000000000 : ℝ), (4156554817/10000000000 : ℝ)] ![(33303066949051/100000000000000 : ℝ), (17562417334257/50000000000000 : ℝ), (3157209835959/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27056091/62500000 : ℝ)|^4293 ≤ (33303066949051/100000000000000 : ℝ)^3269
        have hw : |(27056091/62500000 : ℝ)|=(27056091/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508145549/10000000000 : ℝ)|^4293 ≤ (17562417334257/50000000000000 : ℝ)^3269
        have hw : |(4508145549/10000000000 : ℝ)|=(4508145549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4156554817/10000000000 : ℝ)|^4293 ≤ (3157209835959/10000000000000 : ℝ)^3269
        have hw : |(4156554817/10000000000 : ℝ)|=(4156554817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1333_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5537/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11119/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1471/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5537/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5537/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5537/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5537/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5537/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5537/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5537/50000 : ℝ) ^ (1073/256 : ℝ) ≤ (77104907222239/781250000000000000 : ℝ) := by
    have hpowers : (5537/50000 : ℝ)^1073 ≤ (77104907222239/781250000000000000 : ℝ)^256 := by
      have hnat : (5537 : ℕ)^1073*781250000000000000^256 ≤ 77104907222239^256*50000^1073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5537 50000 77104907222239 781250000000000000 1073 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5537/50000 : ℝ)) (X := (77104907222239/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14759/100000 : ℝ) ^ (1073/256 : ℝ) ≤ (32898798286463279/100000000000000000000 : ℝ) := by
    have hpowers : (14759/100000 : ℝ)^1073 ≤ (32898798286463279/100000000000000000000 : ℝ)^256 := by
      have hnat : (14759 : ℕ)^1073*100000000000000000000^256 ≤ 32898798286463279^256*100000^1073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14759 100000 32898798286463279 100000000000000000000 1073 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14759/100000 : ℝ)) (X := (32898798286463279/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (390702104907222239/390625000000000000 : ℝ) ≤ (10000470900979733/10000000000000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (390702104907222239/390625000000000000 : ℝ)^256 ≤ (10000470900979733/10000000000000000 : ℝ)^1073 := by
      have hnat : (390702104907222239 : ℕ)^256*10000000000000000^1073 ≤ 10000470900979733^1073*390625000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390702104907222239 390625000000000000 10000470900979733 10000000000000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000470900979733/10000000000000000 : ℝ)) (X := (390702104907222239/390625000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042768226410909871/100000000000000000000 : ℝ) ≤ (10001020212835321/10000000000000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (100042768226410909871/100000000000000000000 : ℝ)^256 ≤ (10001020212835321/10000000000000000 : ℝ)^1073 := by
      have hnat : (100042768226410909871 : ℕ)^256*10000000000000000^1073 ≤ 10001020212835321^1073*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042768226410909871 100000000000000000000 10001020212835321 10000000000000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001020212835321/10000000000000000 : ℝ)) (X := (100042768226410909871/100000000000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032898798286463279/50000000000000000000 : ℝ) ≤ (10001569524690909/10000000000000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (50032898798286463279/50000000000000000000 : ℝ)^256 ≤ (10001569524690909/10000000000000000 : ℝ)^1073 := by
      have hnat : (50032898798286463279 : ℕ)^256*10000000000000000^1073 ≤ 10001569524690909^1073*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032898798286463279 50000000000000000000 10001569524690909 10000000000000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001569524690909/10000000000000000 : ℝ)) (X := (50032898798286463279/50000000000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(77104907222239/781250000000000000 : ℝ) ≤ ((36839569111132753081/36850000000000000000 : ℝ)+2*(137327963897/92125000000000 : ℝ)*(5537/50000 : ℝ))^(1073/256 : ℝ) := by
    rw [show (36839569111132753081/36850000000000000000 : ℝ)+2*(137327963897/92125000000000 : ℝ)*(5537/50000 : ℝ)=(10000470900979733/10000000000000000 : ℝ) by norm_num, show 1+2*(77104907222239/781250000000000000 : ℝ)=(390702104907222239/390625000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32898798286463279/100000000000000000000 : ℝ)+(77104907222239/781250000000000000 : ℝ) ≤ ((36839569111132753081/36850000000000000000 : ℝ)+(137327963897/92125000000000 : ℝ)*((14759/100000 : ℝ)+(5537/50000 : ℝ)))^(1073/256 : ℝ) := by
    rw [show (36839569111132753081/36850000000000000000 : ℝ)+(137327963897/92125000000000 : ℝ)*((14759/100000 : ℝ)+(5537/50000 : ℝ))=(10001020212835321/10000000000000000 : ℝ) by norm_num, show 1+(32898798286463279/100000000000000000000 : ℝ)+(77104907222239/781250000000000000 : ℝ)=(100042768226410909871/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32898798286463279/100000000000000000000 : ℝ) ≤ ((36839569111132753081/36850000000000000000 : ℝ)+2*(137327963897/92125000000000 : ℝ)*(14759/100000 : ℝ))^(1073/256 : ℝ) := by
    rw [show (36839569111132753081/36850000000000000000 : ℝ)+2*(137327963897/92125000000000 : ℝ)*(14759/100000 : ℝ)=(10001569524690909/10000000000000000 : ℝ) by norm_num, show 1+2*(32898798286463279/100000000000000000000 : ℝ)=(50032898798286463279/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36839569111132753081/36850000000000000000 : ℝ)*(X 1 0+X 2 0)+(137327963897/92125000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (5537/50000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (36839569111132753081/36850000000000000000 : ℝ)) (alpha := (137327963897/92125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36839569111132753081/36850000000000000000 : ℝ)*(X 0 1+X 2 1)+(137327963897/92125000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (5537/50000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (36839569111132753081/36850000000000000000 : ℝ)) (alpha := (137327963897/92125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36839569111132753081/36850000000000000000 : ℝ)*(X 0 2+X 1 2)+(137327963897/92125000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (5537/50000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (36839569111132753081/36850000000000000000 : ℝ)) (alpha := (137327963897/92125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-205171809/1000000000 : ℝ)*X 0 0+(270679629/500000000 : ℝ)*X 0 1+(2621970839/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674629977/5000000000 : ℝ)*X 1 0+(-2138171447/10000000000 : ℝ)*X 1 1+(65549271/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534925997/1000000000 : ℝ)*X 2 0+(2621970839/5000000000 : ℝ)*X 2 1+(-1069085713/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4328948667/10000000000 : ℝ)*X 0 0+(16621101/40000000 : ℝ)*X 0 1+(4509418431/10000000000 : ℝ)*X 0 2+(4328948667/10000000000 : ℝ)*X 1 0+(16621101/40000000 : ℝ)*X 1 1+(4509418431/10000000000 : ℝ)*X 1 2+(4328948667/10000000000 : ℝ)*X 2 0+(16621101/40000000 : ℝ)*X 2 1+(4509418431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1025865329/5000000000 : ℝ)*X 0 0+(2622275757/5000000000 : ℝ)*X 0 1+(10825959/20000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305607431/10000000000 : ℝ)*X 1 0+(-492283381/2500000000 : ℝ)*X 1 1+(5412979523/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305607267/10000000000 : ℝ)*X 2 0+(5412979677/10000000000 : ℝ)*X 2 1+(-1969133537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((27056091/62500000 : ℝ)*X 0 0+(4508145549/10000000000 : ℝ)*X 0 1+(4156554817/10000000000 : ℝ)*X 0 2+(27056091/62500000 : ℝ)*X 1 0+(4508145549/10000000000 : ℝ)*X 1 1+(4156554817/10000000000 : ℝ)*X 1 2+(27056091/62500000 : ℝ)*X 2 0+(4508145549/10000000000 : ℝ)*X 2 1+(4156554817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (935709501076832745621/115156250000000000000000000 : ℝ) := by norm_num
    linear_combination (776123447/50000000000000 : ℝ)*(base19) + (1464359147/100000000000000 : ℝ)*(base23) + (56444673/100000000000000 : ℝ)*(lower2) + (198877799/100000000000000 : ℝ)*(upper3) + (3706663/2500000000000 : ℝ)*(upper5) + (435913458118159/10000000000000 : ℝ)*(major0) + (435913458118159/10000000000000 : ℝ)*(major1) + (435913458118159/10000000000000 : ℝ)*(major2) + (5894489511235457/100000000000000 : ℝ)*(sp0) + (1473629984389613/25000000000000 : ℝ)*(sp1) + (2947260012723099/50000000000000 : ℝ)*(sp2) + (112949253947509/4000000000000 : ℝ)*(sp3) + (31978569887/100000000000000 : ℝ)*(sp4) + (8026508981/50000000000000 : ℝ)*(sp7) + (2823747401705687/100000000000000 : ℝ)*(f.failure) + (1178904297961069/20000000000000 : ℝ)*(f.sum) + (18524576577531/3685000000000000000000000000 : ℝ)*base66 + (350806943947497879/368500000000000000000000000000000 : ℝ)*base67 + (4902684618230997879/368500000000000000000000000000000 : ℝ)*base69 + (6427148109037002121/368500000000000000000000000000000 : ℝ)*base72 + (283981283457/460625000000000000000000000 : ℝ)*base74 + (255241577928002121/368500000000000000000000000000000 : ℝ)*base76 + (2938286969999002121/368500000000000000000000000000000 : ℝ)*base78 + (2130635313926497879/368500000000000000000000000000000 : ℝ)*base79 + (10498860906499/3685000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (46047663/5000000000000000000000 : ℝ)*base89 + (46047663/5000000000000000000000 : ℝ)*base91 + (46047663/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1350436565806302062101034643/460625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (164304629/25000000000000 : ℝ)*(base19) + (650653947/100000000000000 : ℝ)*(base23) + (38238939/50000000000000 : ℝ)*(upper2) + (16162273/12500000000000 : ℝ)*(upper3) + (1020751/2000000000000 : ℝ)*(upper5) + (2195366469857199/50000000000000 : ℝ)*(major0) + (2195366469857199/50000000000000 : ℝ)*(major1) + (2195366469857199/50000000000000 : ℝ)*(major2) + (2748274677/25000000000000 : ℝ)*(sp1) + (14981375557/100000000000000 : ℝ)*(sp2) + (5937249688072389/100000000000000 : ℝ)*(sp4) + (1187447607551033/20000000000000 : ℝ)*(sp5) + (1187446811208577/20000000000000 : ℝ)*(sp6) + (1422108046815729/50000000000000 : ℝ)*(sp7) + (1422108046815729/50000000000000 : ℝ)*(f.failure) + (5937249688072389/100000000000000 : ℝ)*(f.sum) + (7203201380937/9212500000000000000000000000 : ℝ)*base65 + (13495415281208480119/1842500000000000000000000000000000 : ℝ)*base67 + (2982421114643480119/1842500000000000000000000000000000 : ℝ)*base69 + (12465362636350980119/1842500000000000000000000000000000 : ℝ)*base71 + (27819560441487/9212500000000000000000000000 : ℝ)*base73 + (2807733256655980119/1842500000000000000000000000000000 : ℝ)*base75 + (1279739023664019881/1842500000000000000000000000000000 : ℝ)*base78 + (37085558461795980119/1842500000000000000000000000000000 : ℝ)*base79 + (69800094013949/18425000000000000000000000000 : ℝ)*base81 + (18293721/2500000000000000000000 : ℝ)*base89 + (18293721/2500000000000000000000 : ℝ)*base91 + (18293721/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1333_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5537/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11119/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1333_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1333_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (807/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (306/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11119/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1333_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1333_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1333_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (807/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (306/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11119/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1333_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

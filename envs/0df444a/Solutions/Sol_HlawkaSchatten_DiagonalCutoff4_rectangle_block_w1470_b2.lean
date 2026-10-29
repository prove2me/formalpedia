-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1470_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:10:15.997767+00:00
-- url     : https://prove2.me/submissions/6d4e6cd0-ced9-41b7-9dfc-cde2e9d29817

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
theorem support_rectangle_w1470_s6_0 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1931895197/10000000000 : ℝ)*x 0 + (679844413/1250000000 : ℝ)*x 1 + (6519019/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1931895197/10000000000 : ℝ)^4437 ≤ (11796623292623/100000000000000 : ℝ)^3413 := by
    have hnat : (1931895197 : ℕ)^4437*100000000000000^3413 ≤ 11796623292623^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931895197 10000000000 11796623292623 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679844413/1250000000 : ℝ)^4437 ≤ (11326132413977/25000000000000 : ℝ)^3413 := by
    have hnat : (679844413 : ℕ)^4437*25000000000000^3413 ≤ 11326132413977^3413*1250000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679844413 1250000000 11326132413977 25000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6519019/12500000 : ℝ)^4437 ≤ (42898847036401/100000000000000 : ℝ)^3413 := by
    have hnat : (6519019 : ℕ)^4437*100000000000000^3413 ≤ 42898847036401^3413*12500000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6519019 12500000 42898847036401 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1931895197/10000000000 : ℝ), (679844413/1250000000 : ℝ), (6519019/12500000 : ℝ)] ![(11796623292623/100000000000000 : ℝ), (11326132413977/25000000000000 : ℝ), (42898847036401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1931895197/10000000000 : ℝ)|^4437 ≤ (11796623292623/100000000000000 : ℝ)^3413
        have hw : |(-1931895197/10000000000 : ℝ)|=(1931895197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679844413/1250000000 : ℝ)|^4437 ≤ (11326132413977/25000000000000 : ℝ)^3413
        have hw : |(679844413/1250000000 : ℝ)|=(679844413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6519019/12500000 : ℝ)|^4437 ≤ (42898847036401/100000000000000 : ℝ)^3413
        have hw : |(6519019/12500000 : ℝ)|=(6519019/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s6_1 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353819477/10000000000 : ℝ)*x 0 + (-2046483683/10000000000 : ℝ)*x 1 + (5215215197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353819477/10000000000 : ℝ)^4437 ≤ (22193453856269/50000000000000 : ℝ)^3413 := by
    have hnat : (5353819477 : ℕ)^4437*50000000000000^3413 ≤ 22193453856269^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353819477 10000000000 22193453856269 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2046483683/10000000000 : ℝ)^4437 ≤ (508569810519/4000000000000 : ℝ)^3413 := by
    have hnat : (2046483683 : ℕ)^4437*4000000000000^3413 ≤ 508569810519^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046483683 10000000000 508569810519 4000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215215197/10000000000 : ℝ)^4437 ≤ (268117793777/625000000000 : ℝ)^3413 := by
    have hnat : (5215215197 : ℕ)^4437*625000000000^3413 ≤ 268117793777^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215215197 10000000000 268117793777 625000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353819477/10000000000 : ℝ), (-2046483683/10000000000 : ℝ), (5215215197/10000000000 : ℝ)] ![(22193453856269/50000000000000 : ℝ), (508569810519/4000000000000 : ℝ), (268117793777/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353819477/10000000000 : ℝ)|^4437 ≤ (22193453856269/50000000000000 : ℝ)^3413
        have hw : |(5353819477/10000000000 : ℝ)|=(5353819477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2046483683/10000000000 : ℝ)|^4437 ≤ (508569810519/4000000000000 : ℝ)^3413
        have hw : |(-2046483683/10000000000 : ℝ)|=(2046483683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215215197/10000000000 : ℝ)|^4437 ≤ (268117793777/625000000000 : ℝ)^3413
        have hw : |(5215215197/10000000000 : ℝ)|=(5215215197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s6_2 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353819491/10000000000 : ℝ)*x 0 + (2607607591/5000000000 : ℝ)*x 1 + (-409296737/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353819491/10000000000 : ℝ)^4437 ≤ (5548363482929/12500000000000 : ℝ)^3413 := by
    have hnat : (5353819491 : ℕ)^4437*12500000000000^3413 ≤ 5548363482929^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353819491 10000000000 5548363482929 12500000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607607591/5000000000 : ℝ)^4437 ≤ (8579769368783/20000000000000 : ℝ)^3413 := by
    have hnat : (2607607591 : ℕ)^4437*20000000000000^3413 ≤ 8579769368783^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607607591 5000000000 8579769368783 20000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (409296737/2000000000 : ℝ)^4437 ≤ (1589280659891/12500000000000 : ℝ)^3413 := by
    have hnat : (409296737 : ℕ)^4437*12500000000000^3413 ≤ 1589280659891^3413*2000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409296737 2000000000 1589280659891 12500000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353819491/10000000000 : ℝ), (2607607591/5000000000 : ℝ), (-409296737/2000000000 : ℝ)] ![(5548363482929/12500000000000 : ℝ), (8579769368783/20000000000000 : ℝ), (1589280659891/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353819491/10000000000 : ℝ)|^4437 ≤ (5548363482929/12500000000000 : ℝ)^3413
        have hw : |(5353819491/10000000000 : ℝ)|=(5353819491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607607591/5000000000 : ℝ)|^4437 ≤ (8579769368783/20000000000000 : ℝ)^3413
        have hw : |(2607607591/5000000000 : ℝ)|=(2607607591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-409296737/2000000000 : ℝ)|^4437 ≤ (1589280659891/12500000000000 : ℝ)^3413
        have hw : |(-409296737/2000000000 : ℝ)|=(409296737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s6_3 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2144870089/5000000000 : ℝ)*x 0 + (4049976811/10000000000 : ℝ)*x 1 + (2270954093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144870089/5000000000 : ℝ)^4437 ≤ (16638704918393/50000000000000 : ℝ)^3413 := by
    have hnat : (2144870089 : ℕ)^4437*50000000000000^3413 ≤ 16638704918393^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144870089 5000000000 16638704918393 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4049976811/10000000000 : ℝ)^4437 ≤ (30879964757331/100000000000000 : ℝ)^3413 := by
    have hnat : (4049976811 : ℕ)^4437*100000000000000^3413 ≤ 30879964757331^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4049976811 10000000000 30879964757331 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2270954093/5000000000 : ℝ)^4437 ≤ (17921312693/50000000000 : ℝ)^3413 := by
    have hnat : (2270954093 : ℕ)^4437*50000000000^3413 ≤ 17921312693^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270954093 5000000000 17921312693 50000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2144870089/5000000000 : ℝ), (4049976811/10000000000 : ℝ), (2270954093/5000000000 : ℝ)] ![(16638704918393/50000000000000 : ℝ), (30879964757331/100000000000000 : ℝ), (17921312693/50000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2144870089/5000000000 : ℝ)|^4437 ≤ (16638704918393/50000000000000 : ℝ)^3413
        have hw : |(2144870089/5000000000 : ℝ)|=(2144870089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4049976811/10000000000 : ℝ)|^4437 ≤ (30879964757331/100000000000000 : ℝ)^3413
        have hw : |(4049976811/10000000000 : ℝ)|=(4049976811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2270954093/5000000000 : ℝ)|^4437 ≤ (17921312693/50000000000 : ℝ)^3413
        have hw : |(2270954093/5000000000 : ℝ)|=(2270954093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s6_4 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1931925987/10000000000 : ℝ)*x 0 + (5216356457/10000000000 : ℝ)*x 1 + (1359401421/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1931925987/10000000000 : ℝ)^4437 ≤ (5898433856671/50000000000000 : ℝ)^3413 := by
    have hnat : (1931925987 : ℕ)^4437*50000000000000^3413 ≤ 5898433856671^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931925987 10000000000 5898433856671 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216356457/10000000000 : ℝ)^4437 ≤ (21455525827853/50000000000000 : ℝ)^3413 := by
    have hnat : (5216356457 : ℕ)^4437*50000000000000^3413 ≤ 21455525827853^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216356457 10000000000 21455525827853 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359401421/2500000000 : ℝ)^4437 ≤ (45292080618123/100000000000000 : ℝ)^3413 := by
    have hnat : (1359401421 : ℕ)^4437*100000000000000^3413 ≤ 45292080618123^3413*2500000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359401421 2500000000 45292080618123 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1931925987/10000000000 : ℝ), (5216356457/10000000000 : ℝ), (1359401421/2500000000 : ℝ)] ![(5898433856671/50000000000000 : ℝ), (21455525827853/50000000000000 : ℝ), (45292080618123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1931925987/10000000000 : ℝ)|^4437 ≤ (5898433856671/50000000000000 : ℝ)^3413
        have hw : |(-1931925987/10000000000 : ℝ)|=(1931925987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216356457/10000000000 : ℝ)|^4437 ≤ (21455525827853/50000000000000 : ℝ)^3413
        have hw : |(5216356457/10000000000 : ℝ)|=(5216356457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359401421/2500000000 : ℝ)|^4437 ≤ (45292080618123/100000000000000 : ℝ)^3413
        have hw : |(1359401421/2500000000 : ℝ)|=(1359401421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s6_5 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295541037/10000000000 : ℝ)*x 0 + (-912046597/5000000000 : ℝ)*x 1 + (5437605589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295541037/10000000000 : ℝ)^4437 ≤ (21879901081649/50000000000000 : ℝ)^3413 := by
    have hnat : (5295541037 : ℕ)^4437*50000000000000^3413 ≤ 21879901081649^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295541037 10000000000 21879901081649 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (912046597/5000000000 : ℝ)^4437 ≤ (1368514778467/12500000000000 : ℝ)^3413 := by
    have hnat : (912046597 : ℕ)^4437*12500000000000^3413 ≤ 1368514778467^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912046597 5000000000 1368514778467 12500000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437605589/10000000000 : ℝ)^4437 ≤ (45292079589417/100000000000000 : ℝ)^3413 := by
    have hnat : (5437605589 : ℕ)^4437*100000000000000^3413 ≤ 45292079589417^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437605589 10000000000 45292079589417 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295541037/10000000000 : ℝ), (-912046597/5000000000 : ℝ), (5437605589/10000000000 : ℝ)] ![(21879901081649/50000000000000 : ℝ), (1368514778467/12500000000000 : ℝ), (45292079589417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295541037/10000000000 : ℝ)|^4437 ≤ (21879901081649/50000000000000 : ℝ)^3413
        have hw : |(5295541037/10000000000 : ℝ)|=(5295541037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-912046597/5000000000 : ℝ)|^4437 ≤ (1368514778467/12500000000000 : ℝ)^3413
        have hw : |(-912046597/5000000000 : ℝ)|=(912046597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437605589/10000000000 : ℝ)|^4437 ≤ (45292079589417/100000000000000 : ℝ)^3413
        have hw : |(5437605589/10000000000 : ℝ)|=(5437605589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s6_6 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059108163/2000000000 : ℝ)*x 0 + (67970069/125000000 : ℝ)*x 1 + (-456023399/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059108163/2000000000 : ℝ)^4437 ≤ (5469974972299/12500000000000 : ℝ)^3413 := by
    have hnat : (1059108163 : ℕ)^4437*12500000000000^3413 ≤ 5469974972299^3413*2000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059108163 2000000000 5469974972299 12500000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67970069/125000000 : ℝ)^4437 ≤ (11323019710563/25000000000000 : ℝ)^3413 := by
    have hnat : (67970069 : ℕ)^4437*25000000000000^3413 ≤ 11323019710563^3413*125000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67970069 125000000 11323019710563 25000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (456023399/2500000000 : ℝ)^4437 ≤ (5474060682213/50000000000000 : ℝ)^3413 := by
    have hnat : (456023399 : ℕ)^4437*50000000000000^3413 ≤ 5474060682213^3413*2500000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456023399 2500000000 5474060682213 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059108163/2000000000 : ℝ), (67970069/125000000 : ℝ), (-456023399/2500000000 : ℝ)] ![(5469974972299/12500000000000 : ℝ), (11323019710563/25000000000000 : ℝ), (5474060682213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059108163/2000000000 : ℝ)|^4437 ≤ (5469974972299/12500000000000 : ℝ)^3413
        have hw : |(1059108163/2000000000 : ℝ)|=(1059108163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67970069/125000000 : ℝ)|^4437 ≤ (11323019710563/25000000000000 : ℝ)^3413
        have hw : |(67970069/125000000 : ℝ)|=(67970069/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-456023399/2500000000 : ℝ)|^4437 ≤ (5474060682213/50000000000000 : ℝ)^3413
        have hw : |(-456023399/2500000000 : ℝ)|=(456023399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s6_7 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4289808451/10000000000 : ℝ)*x 0 + (907879193/2000000000 : ℝ)*x 1 + (4052507027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4289808451/10000000000 : ℝ)^4437 ≤ (33278098364921/100000000000000 : ℝ)^3413 := by
    have hnat : (4289808451 : ℕ)^4437*100000000000000^3413 ≤ 33278098364921^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4289808451 10000000000 33278098364921 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (907879193/2000000000 : ℝ)^4437 ≤ (35816854081507/100000000000000 : ℝ)^3413 := by
    have hnat : (907879193 : ℕ)^4437*100000000000000^3413 ≤ 35816854081507^3413*2000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907879193 2000000000 35816854081507 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4052507027/10000000000 : ℝ)^4437 ≤ (7726261884671/25000000000000 : ℝ)^3413 := by
    have hnat : (4052507027 : ℕ)^4437*25000000000000^3413 ≤ 7726261884671^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4052507027 10000000000 7726261884671 25000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4289808451/10000000000 : ℝ), (907879193/2000000000 : ℝ), (4052507027/10000000000 : ℝ)] ![(33278098364921/100000000000000 : ℝ), (35816854081507/100000000000000 : ℝ), (7726261884671/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4289808451/10000000000 : ℝ)|^4437 ≤ (33278098364921/100000000000000 : ℝ)^3413
        have hw : |(4289808451/10000000000 : ℝ)|=(4289808451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(907879193/2000000000 : ℝ)|^4437 ≤ (35816854081507/100000000000000 : ℝ)^3413
        have hw : |(907879193/2000000000 : ℝ)|=(907879193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4052507027/10000000000 : ℝ)|^4437 ≤ (7726261884671/25000000000000 : ℝ)^3413
        have hw : |(4052507027/10000000000 : ℝ)|=(4052507027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1470_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40008003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10741/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10743/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15473/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (619/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10741/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (619/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10741/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (619/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10741/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (619/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10741/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (619/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10741/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (619/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10741/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10741/100000 : ℝ) ^ (4435/1024 : ℝ) ≤ (198724631101241/3125000000000000000 : ℝ) := by
    have hpowers : (10741/100000 : ℝ)^4435 ≤ (198724631101241/3125000000000000000 : ℝ)^1024 := by
      have hnat : (10741 : ℕ)^4435*3125000000000000000^1024 ≤ 198724631101241^1024*100000^4435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10741 100000 198724631101241 3125000000000000000 4435 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10741/100000 : ℝ)) (X := (198724631101241/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (619/4000 : ℝ) ^ (4435/1024 : ℝ) ≤ (30920468198313127/100000000000000000000 : ℝ) := by
    have hpowers : (619/4000 : ℝ)^4435 ≤ (30920468198313127/100000000000000000000 : ℝ)^1024 := by
      have hnat : (619 : ℕ)^4435*100000000000000000000^1024 ≤ 30920468198313127^1024*4000^4435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        619 4000 30920468198313127 100000000000000000000 4435 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (619/4000 : ℝ)) (X := (30920468198313127/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562698724631101241/1562500000000000000 : ℝ) ≤ (2000058728209687/2000000000000000 : ℝ) ^ (4435/1024 : ℝ) := by
    have hpowers : (1562698724631101241/1562500000000000000 : ℝ)^1024 ≤ (2000058728209687/2000000000000000 : ℝ)^4435 := by
      have hnat : (1562698724631101241 : ℕ)^1024*2000000000000000^4435 ≤ 2000058728209687^4435*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562698724631101241 1562500000000000000 2000058728209687 2000000000000000 1024 4435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000058728209687/2000000000000000 : ℝ)) (X := (1562698724631101241/1562500000000000000 : ℝ)) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037279656393552839/100000000000000000000 : ℝ) ≤ (10000860629011209/10000000000000000 : ℝ) ^ (4435/1024 : ℝ) := by
    have hpowers : (100037279656393552839/100000000000000000000 : ℝ)^1024 ≤ (10000860629011209/10000000000000000 : ℝ)^4435 := by
      have hnat : (100037279656393552839 : ℕ)^1024*10000000000000000^4435 ≤ 10000860629011209^4435*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037279656393552839 100000000000000000000 10000860629011209 10000000000000000 1024 4435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000860629011209/10000000000000000 : ℝ)) (X := (100037279656393552839/100000000000000000000 : ℝ)) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030920468198313127/50000000000000000000 : ℝ) ≤ (10001427616973983/10000000000000000 : ℝ) ^ (4435/1024 : ℝ) := by
    have hpowers : (50030920468198313127/50000000000000000000 : ℝ)^1024 ≤ (10001427616973983/10000000000000000 : ℝ)^4435 := by
      have hnat : (50030920468198313127 : ℕ)^1024*10000000000000000^4435 ≤ 10001427616973983^4435*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030920468198313127 50000000000000000000 10001427616973983 10000000000000000 1024 4435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001427616973983/10000000000000000 : ℝ)) (X := (50030920468198313127/50000000000000000000 : ℝ)) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(198724631101241/3125000000000000000 : ℝ) ≤ ((23664605030653490111/23670000000000000000 : ℝ)+2*(283493981387/236700000000000 : ℝ)*(10741/100000 : ℝ))^(4435/1024 : ℝ) := by
    rw [show (23664605030653490111/23670000000000000000 : ℝ)+2*(283493981387/236700000000000 : ℝ)*(10741/100000 : ℝ)=(2000058728209687/2000000000000000 : ℝ) by norm_num, show 1+2*(198724631101241/3125000000000000000 : ℝ)=(1562698724631101241/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30920468198313127/100000000000000000000 : ℝ)+(198724631101241/3125000000000000000 : ℝ) ≤ ((23664605030653490111/23670000000000000000 : ℝ)+(283493981387/236700000000000 : ℝ)*((619/4000 : ℝ)+(10741/100000 : ℝ)))^(4435/1024 : ℝ) := by
    rw [show (23664605030653490111/23670000000000000000 : ℝ)+(283493981387/236700000000000 : ℝ)*((619/4000 : ℝ)+(10741/100000 : ℝ))=(10000860629011209/10000000000000000 : ℝ) by norm_num, show 1+(30920468198313127/100000000000000000000 : ℝ)+(198724631101241/3125000000000000000 : ℝ)=(100037279656393552839/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30920468198313127/100000000000000000000 : ℝ) ≤ ((23664605030653490111/23670000000000000000 : ℝ)+2*(283493981387/236700000000000 : ℝ)*(619/4000 : ℝ))^(4435/1024 : ℝ) := by
    rw [show (23664605030653490111/23670000000000000000 : ℝ)+2*(283493981387/236700000000000 : ℝ)*(619/4000 : ℝ)=(10001427616973983/10000000000000000 : ℝ) by norm_num, show 1+2*(30920468198313127/100000000000000000000 : ℝ)=(50030920468198313127/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23664605030653490111/23670000000000000000 : ℝ)*(X 1 0+X 2 0)+(283493981387/236700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4435/1024 : ℝ)) (lo := (10741/100000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (23664605030653490111/23670000000000000000 : ℝ)) (alpha := (283493981387/236700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23664605030653490111/23670000000000000000 : ℝ)*(X 0 1+X 2 1)+(283493981387/236700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4435/1024 : ℝ)) (lo := (10741/100000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (23664605030653490111/23670000000000000000 : ℝ)) (alpha := (283493981387/236700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23664605030653490111/23670000000000000000 : ℝ)*(X 0 2+X 1 2)+(283493981387/236700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4435/1024 : ℝ)) (lo := (10741/100000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (23664605030653490111/23670000000000000000 : ℝ)) (alpha := (283493981387/236700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1931895197/10000000000 : ℝ)*X 0 0+(679844413/1250000000 : ℝ)*X 0 1+(6519019/12500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353819477/10000000000 : ℝ)*X 1 0+(-2046483683/10000000000 : ℝ)*X 1 1+(5215215197/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353819491/10000000000 : ℝ)*X 2 0+(2607607591/5000000000 : ℝ)*X 2 1+(-409296737/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2144870089/5000000000 : ℝ)*X 0 0+(4049976811/10000000000 : ℝ)*X 0 1+(2270954093/5000000000 : ℝ)*X 0 2+(2144870089/5000000000 : ℝ)*X 1 0+(4049976811/10000000000 : ℝ)*X 1 1+(2270954093/5000000000 : ℝ)*X 1 2+(2144870089/5000000000 : ℝ)*X 2 0+(4049976811/10000000000 : ℝ)*X 2 1+(2270954093/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1931925987/10000000000 : ℝ)*X 0 0+(5216356457/10000000000 : ℝ)*X 0 1+(1359401421/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295541037/10000000000 : ℝ)*X 1 0+(-912046597/5000000000 : ℝ)*X 1 1+(5437605589/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1059108163/2000000000 : ℝ)*X 2 0+(67970069/125000000 : ℝ)*X 2 1+(-456023399/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4289808451/10000000000 : ℝ)*X 0 0+(907879193/2000000000 : ℝ)*X 0 1+(4052507027/10000000000 : ℝ)*X 0 2+(4289808451/10000000000 : ℝ)*X 1 0+(907879193/2000000000 : ℝ)*X 1 1+(4052507027/10000000000 : ℝ)*X 1 2+(4289808451/10000000000 : ℝ)*X 2 0+(907879193/2000000000 : ℝ)*X 2 1+(4052507027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62313747041292294503/15780000000000000000000000 : ℝ) := by norm_num
    linear_combination (713609791/100000000000000 : ℝ)*(base19) + (671203527/100000000000000 : ℝ)*(base23) + (7241609/25000000000000 : ℝ)*(lower2) + (101911421/100000000000000 : ℝ)*(upper3) + (62322531/100000000000000 : ℝ)*(upper5) + (162657655232509/5000000000000 : ℝ)*(major0) + (162657655232509/5000000000000 : ℝ)*(major1) + (162657655232509/5000000000000 : ℝ)*(major2) + (2236740695961961/50000000000000 : ℝ)*(sp0) + (2236745694455029/50000000000000 : ℝ)*(sp1) + (4473491431316321/100000000000000 : ℝ)*(sp2) + (1016404293478477/50000000000000 : ℝ)*(sp3) + (5355297963/50000000000000 : ℝ)*(sp4) + (538819333/10000000000000 : ℝ)*(sp7) + (508203493787571/25000000000000 : ℝ)*(f.failure) + (559186512814981/12500000000000 : ℝ)*(f.sum) + (265747629301/47340000000000000000000000 : ℝ)*base65 + (329329187681381501/118350000000000000000000000000000 : ℝ)*base68 + (647090596846781501/118350000000000000000000000000000 : ℝ)*base70 + (134116270566281501/118350000000000000000000000000000 : ℝ)*base72 + (5511879522211/1183500000000000000000000000 : ℝ)*base73 + (507426240622518499/118350000000000000000000000000000 : ℝ)*base75 + (240507287392968499/118350000000000000000000000000000 : ℝ)*base77 + (17009192849418499/118350000000000000000000000000000 : ℝ)*base79 + (1084650614191/2367000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3069287/625000000000000000000 : ℝ)*base90 + (3069287/625000000000000000000 : ℝ)*base92 + (3069287/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (222928914630279137951581681/24656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1595613917/100000000000000 : ℝ)*(base19) + (1631439663/100000000000000 : ℝ)*(base23) + (365770429/100000000000000 : ℝ)*(lower1) + (67450299/50000000000000 : ℝ)*(upper3) + (167626459/100000000000000 : ℝ)*(lower4) + (40633699/12500000000000 : ℝ)*(upper5) + (205425617339621/6250000000000 : ℝ)*(major0) + (205425617339621/6250000000000 : ℝ)*(major1) + (205425617339621/6250000000000 : ℝ)*(major2) + (8290516421/100000000000000 : ℝ)*(sp1) + (1129943550794387/25000000000000 : ℝ)*(sp4) + (4519764317047211/100000000000000 : ℝ)*(sp5) + (903954514347577/20000000000000 : ℝ)*(sp6) + (410769050061551/20000000000000 : ℝ)*(sp7) + (410769050061551/20000000000000 : ℝ)*(f.failure) + (1129943550794387/25000000000000 : ℝ)*(f.sum) + (55770294710017/11835000000000000000000000000 : ℝ)*base65 + (532626116007375431/147937500000000000000000000000000 : ℝ)*base67 + (625804573655249569/147937500000000000000000000000000 : ℝ)*base70 + (76333618761749569/147937500000000000000000000000000 : ℝ)*base72 + (38065197354701/5917500000000000000000000000 : ℝ)*base73 + (1575819164400749569/147937500000000000000000000000000 : ℝ)*base76 + (349166857694062069/147937500000000000000000000000000 : ℝ)*base78 + (970240365545625431/147937500000000000000000000000000 : ℝ)*base79 + (58287296313143/11835000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2592653/500000000000000000000 : ℝ)*base89 + (2592653/500000000000000000000 : ℝ)*base91 + (2592653/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1470_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40008003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10741/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10743/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15473/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1470_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1470_box_0 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-855216589/5000000000 : ℝ)*x 0 + (5407389831/10000000000 : ℝ)*x 1 + (540738991/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855216589/5000000000 : ℝ)^4437 ≤ (201393510259/2000000000000 : ℝ)^3413 := by
    have hnat : (855216589 : ℕ)^4437*2000000000000^3413 ≤ 201393510259^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855216589 5000000000 201393510259 2000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407389831/10000000000 : ℝ)^4437 ≤ (44965161809283/100000000000000 : ℝ)^3413 := by
    have hnat : (5407389831 : ℕ)^4437*100000000000000^3413 ≤ 44965161809283^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407389831 10000000000 44965161809283 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540738991/1000000000 : ℝ)^4437 ≤ (5620645332913/12500000000000 : ℝ)^3413 := by
    have hnat : (540738991 : ℕ)^4437*12500000000000^3413 ≤ 5620645332913^3413*1000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540738991 1000000000 5620645332913 12500000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-855216589/5000000000 : ℝ), (5407389831/10000000000 : ℝ), (540738991/1000000000 : ℝ)] ![(201393510259/2000000000000 : ℝ), (44965161809283/100000000000000 : ℝ), (5620645332913/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-855216589/5000000000 : ℝ)|^4437 ≤ (201393510259/2000000000000 : ℝ)^3413
        have hw : |(-855216589/5000000000 : ℝ)|=(855216589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407389831/10000000000 : ℝ)|^4437 ≤ (44965161809283/100000000000000 : ℝ)^3413
        have hw : |(5407389831/10000000000 : ℝ)|=(5407389831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540738991/1000000000 : ℝ)|^4437 ≤ (5620645332913/12500000000000 : ℝ)^3413
        have hw : |(540738991/1000000000 : ℝ)|=(540738991/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_box_1 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658750709/1250000000 : ℝ)*x 0 + (-1900645537/10000000000 : ℝ)*x 1 + (2703694943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658750709/1250000000 : ℝ)^4437 ≤ (43485679088133/100000000000000 : ℝ)^3413 := by
    have hnat : (658750709 : ℕ)^4437*100000000000000^3413 ≤ 43485679088133^3413*1250000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658750709 1250000000 43485679088133 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1900645537/10000000000 : ℝ)^4437 ≤ (5774579244867/50000000000000 : ℝ)^3413 := by
    have hnat : (1900645537 : ℕ)^4437*50000000000000^3413 ≤ 5774579244867^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900645537 10000000000 5774579244867 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703694943/5000000000 : ℝ)^4437 ≤ (8993032480771/20000000000000 : ℝ)^3413 := by
    have hnat : (2703694943 : ℕ)^4437*20000000000000^3413 ≤ 8993032480771^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703694943 5000000000 8993032480771 20000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658750709/1250000000 : ℝ), (-1900645537/10000000000 : ℝ), (2703694943/5000000000 : ℝ)] ![(43485679088133/100000000000000 : ℝ), (5774579244867/50000000000000 : ℝ), (8993032480771/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658750709/1250000000 : ℝ)|^4437 ≤ (43485679088133/100000000000000 : ℝ)^3413
        have hw : |(658750709/1250000000 : ℝ)|=(658750709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1900645537/10000000000 : ℝ)|^4437 ≤ (5774579244867/50000000000000 : ℝ)^3413
        have hw : |(-1900645537/10000000000 : ℝ)|=(1900645537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703694943/5000000000 : ℝ)|^4437 ≤ (8993032480771/20000000000000 : ℝ)^3413
        have hw : |(2703694943/5000000000 : ℝ)|=(2703694943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_box_2 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658750719/1250000000 : ℝ)*x 0 + (5407389863/10000000000 : ℝ)*x 1 + (-1900645461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658750719/1250000000 : ℝ)^4437 ≤ (43485679946313/100000000000000 : ℝ)^3413 := by
    have hnat : (658750719 : ℕ)^4437*100000000000000^3413 ≤ 43485679946313^3413*1250000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658750719 1250000000 43485679946313 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407389863/10000000000 : ℝ)^4437 ≤ (2810322634701/6250000000000 : ℝ)^3413 := by
    have hnat : (5407389863 : ℕ)^4437*6250000000000^3413 ≤ 2810322634701^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407389863 10000000000 2810322634701 6250000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1900645461/10000000000 : ℝ)^4437 ≤ (1443644736171/12500000000000 : ℝ)^3413 := by
    have hnat : (1900645461 : ℕ)^4437*12500000000000^3413 ≤ 1443644736171^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900645461 10000000000 1443644736171 12500000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658750719/1250000000 : ℝ), (5407389863/10000000000 : ℝ), (-1900645461/10000000000 : ℝ)] ![(43485679946313/100000000000000 : ℝ), (2810322634701/6250000000000 : ℝ), (1443644736171/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658750719/1250000000 : ℝ)|^4437 ≤ (43485679946313/100000000000000 : ℝ)^3413
        have hw : |(658750719/1250000000 : ℝ)|=(658750719/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407389863/10000000000 : ℝ)|^4437 ≤ (2810322634701/6250000000000 : ℝ)^3413
        have hw : |(5407389863/10000000000 : ℝ)|=(5407389863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1900645461/10000000000 : ℝ)|^4437 ≤ (1443644736171/12500000000000 : ℝ)^3413
        have hw : |(-1900645461/10000000000 : ℝ)|=(1900645461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_box_3 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (898973073/2000000000 : ℝ)*x 0 + (2097224239/5000000000 : ℝ)*x 1 + (4194448733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (898973073/2000000000 : ℝ)^4437 ≤ (7072150831161/20000000000000 : ℝ)^3413 := by
    have hnat : (898973073 : ℕ)^4437*20000000000000^3413 ≤ 7072150831161^3413*2000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898973073 2000000000 7072150831161 20000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2097224239/5000000000 : ℝ)^4437 ≤ (32319621636897/100000000000000 : ℝ)^3413 := by
    have hnat : (2097224239 : ℕ)^4437*100000000000000^3413 ≤ 32319621636897^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097224239 5000000000 32319621636897 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4194448733/10000000000 : ℝ)^4437 ≤ (4039953023909/12500000000000 : ℝ)^3413 := by
    have hnat : (4194448733 : ℕ)^4437*12500000000000^3413 ≤ 4039953023909^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4194448733 10000000000 4039953023909 12500000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(898973073/2000000000 : ℝ), (2097224239/5000000000 : ℝ), (4194448733/10000000000 : ℝ)] ![(7072150831161/20000000000000 : ℝ), (32319621636897/100000000000000 : ℝ), (4039953023909/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(898973073/2000000000 : ℝ)|^4437 ≤ (7072150831161/20000000000000 : ℝ)^3413
        have hw : |(898973073/2000000000 : ℝ)|=(898973073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2097224239/5000000000 : ℝ)|^4437 ≤ (32319621636897/100000000000000 : ℝ)^3413
        have hw : |(2097224239/5000000000 : ℝ)|=(2097224239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4194448733/10000000000 : ℝ)|^4437 ≤ (4039953023909/12500000000000 : ℝ)^3413
        have hw : |(4194448733/10000000000 : ℝ)|=(4194448733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_box_4 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079416641/5000000000 : ℝ)*x 0 + (5241998269/10000000000 : ℝ)*x 1 + (209679949/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079416641/5000000000 : ℝ)^4437 ≤ (13629041974061/100000000000000 : ℝ)^3413 := by
    have hnat : (1079416641 : ℕ)^4437*100000000000000^3413 ≤ 13629041974061^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079416641 5000000000 13629041974061 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241998269/10000000000 : ℝ)^4437 ≤ (21592738280399/50000000000000 : ℝ)^3413 := by
    have hnat : (5241998269 : ℕ)^4437*50000000000000^3413 ≤ 21592738280399^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241998269 10000000000 21592738280399 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209679949/400000000 : ℝ)^4437 ≤ (43185481444609/100000000000000 : ℝ)^3413 := by
    have hnat : (209679949 : ℕ)^4437*100000000000000^3413 ≤ 43185481444609^3413*400000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209679949 400000000 43185481444609 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079416641/5000000000 : ℝ), (5241998269/10000000000 : ℝ), (209679949/400000000 : ℝ)] ![(13629041974061/100000000000000 : ℝ), (21592738280399/50000000000000 : ℝ), (43185481444609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079416641/5000000000 : ℝ)|^4437 ≤ (13629041974061/100000000000000 : ℝ)^3413
        have hw : |(-1079416641/5000000000 : ℝ)|=(1079416641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241998269/10000000000 : ℝ)|^4437 ≤ (21592738280399/50000000000000 : ℝ)^3413
        have hw : |(5241998269/10000000000 : ℝ)|=(5241998269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209679949/400000000 : ℝ)|^4437 ≤ (43185481444609/100000000000000 : ℝ)^3413
        have hw : |(209679949/400000000 : ℝ)|=(209679949/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_box_5 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385535373/10000000000 : ℝ)*x 0 + (-1968180213/10000000000 : ℝ)*x 1 + (5241998367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385535373/10000000000 : ℝ)^4437 ≤ (44729049830581/100000000000000 : ℝ)^3413 := by
    have hnat : (5385535373 : ℕ)^4437*100000000000000^3413 ≤ 44729049830581^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385535373 10000000000 44729049830581 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1968180213/10000000000 : ℝ)^4437 ≤ (12085472542883/100000000000000 : ℝ)^3413 := by
    have hnat : (1968180213 : ℕ)^4437*100000000000000^3413 ≤ 12085472542883^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968180213 10000000000 12085472542883 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241998367/10000000000 : ℝ)^4437 ≤ (43185477610389/100000000000000 : ℝ)^3413 := by
    have hnat : (5241998367 : ℕ)^4437*100000000000000^3413 ≤ 43185477610389^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241998367 10000000000 43185477610389 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385535373/10000000000 : ℝ), (-1968180213/10000000000 : ℝ), (5241998367/10000000000 : ℝ)] ![(44729049830581/100000000000000 : ℝ), (12085472542883/100000000000000 : ℝ), (43185477610389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385535373/10000000000 : ℝ)|^4437 ≤ (44729049830581/100000000000000 : ℝ)^3413
        have hw : |(5385535373/10000000000 : ℝ)|=(5385535373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1968180213/10000000000 : ℝ)|^4437 ≤ (12085472542883/100000000000000 : ℝ)^3413
        have hw : |(-1968180213/10000000000 : ℝ)|=(1968180213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241998367/10000000000 : ℝ)|^4437 ≤ (43185477610389/100000000000000 : ℝ)^3413
        have hw : |(5241998367/10000000000 : ℝ)|=(5241998367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_box_6 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385535593/10000000000 : ℝ)*x 0 + (5241998459/10000000000 : ℝ)*x 1 + (-1968179793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385535593/10000000000 : ℝ)^4437 ≤ (44729052205981/100000000000000 : ℝ)^3413 := by
    have hnat : (5385535593 : ℕ)^4437*100000000000000^3413 ≤ 44729052205981^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385535593 10000000000 44729052205981 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241998459/10000000000 : ℝ)^4437 ≤ (43185478595719/100000000000000 : ℝ)^3413 := by
    have hnat : (5241998459 : ℕ)^4437*100000000000000^3413 ≤ 43185478595719^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241998459 10000000000 43185478595719 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1968179793/10000000000 : ℝ)^4437 ≤ (12085469190133/100000000000000 : ℝ)^3413 := by
    have hnat : (1968179793 : ℕ)^4437*100000000000000^3413 ≤ 12085469190133^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968179793 10000000000 12085469190133 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385535593/10000000000 : ℝ), (5241998459/10000000000 : ℝ), (-1968179793/10000000000 : ℝ)] ![(44729052205981/100000000000000 : ℝ), (43185478595719/100000000000000 : ℝ), (12085469190133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385535593/10000000000 : ℝ)|^4437 ≤ (44729052205981/100000000000000 : ℝ)^3413
        have hw : |(5385535593/10000000000 : ℝ)|=(5385535593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241998459/10000000000 : ℝ)|^4437 ≤ (43185478595719/100000000000000 : ℝ)^3413
        have hw : |(5241998459/10000000000 : ℝ)|=(5241998459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1968179793/10000000000 : ℝ)|^4437 ≤ (12085469190133/100000000000000 : ℝ)^3413
        have hw : |(-1968179793/10000000000 : ℝ)|=(1968179793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_box_7 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4082408869/10000000000 : ℝ)*x 0 + (440053643/1000000000 : ℝ)*x 1 + (275033563/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4082408869/10000000000 : ℝ)^4437 ≤ (15600914357607/50000000000000 : ℝ)^3413 := by
    have hnat : (4082408869 : ℕ)^4437*50000000000000^3413 ≤ 15600914357607^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4082408869 10000000000 15600914357607 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440053643/1000000000 : ℝ)^4437 ≤ (6879816540349/20000000000000 : ℝ)^3413 := by
    have hnat : (440053643 : ℕ)^4437*20000000000000^3413 ≤ 6879816540349^3413*1000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440053643 1000000000 6879816540349 20000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275033563/625000000 : ℝ)^4437 ≤ (17199544287793/50000000000000 : ℝ)^3413 := by
    have hnat : (275033563 : ℕ)^4437*50000000000000^3413 ≤ 17199544287793^3413*625000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275033563 625000000 17199544287793 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4082408869/10000000000 : ℝ), (440053643/1000000000 : ℝ), (275033563/625000000 : ℝ)] ![(15600914357607/50000000000000 : ℝ), (6879816540349/20000000000000 : ℝ), (17199544287793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4082408869/10000000000 : ℝ)|^4437 ≤ (15600914357607/50000000000000 : ℝ)^3413
        have hw : |(4082408869/10000000000 : ℝ)|=(4082408869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(440053643/1000000000 : ℝ)|^4437 ≤ (6879816540349/20000000000000 : ℝ)^3413
        have hw : |(440053643/1000000000 : ℝ)|=(440053643/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275033563/625000000 : ℝ)|^4437 ≤ (17199544287793/50000000000000 : ℝ)^3413
        have hw : |(275033563/625000000 : ℝ)|=(275033563/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_box_8 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1032161889/5000000000 : ℝ)*x 0 + (256330621/500000000 : ℝ)*x 1 + (542796311/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1032161889/5000000000 : ℝ)^4437 ≤ (12858522902057/100000000000000 : ℝ)^3413 := by
    have hnat : (1032161889 : ℕ)^4437*100000000000000^3413 ≤ 12858522902057^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032161889 5000000000 12858522902057 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256330621/500000000 : ℝ)^4437 ≤ (4195378314437/10000000000000 : ℝ)^3413 := by
    have hnat : (256330621 : ℕ)^4437*10000000000000^3413 ≤ 4195378314437^3413*500000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256330621 500000000 4195378314437 10000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542796311/1000000000 : ℝ)^4437 ≤ (4518769393787/10000000000000 : ℝ)^3413 := by
    have hnat : (542796311 : ℕ)^4437*10000000000000^3413 ≤ 4518769393787^3413*1000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542796311 1000000000 4518769393787 10000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1032161889/5000000000 : ℝ), (256330621/500000000 : ℝ), (542796311/1000000000 : ℝ)] ![(12858522902057/100000000000000 : ℝ), (4195378314437/10000000000000 : ℝ), (4518769393787/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1032161889/5000000000 : ℝ)|^4437 ≤ (12858522902057/100000000000000 : ℝ)^3413
        have hw : |(-1032161889/5000000000 : ℝ)|=(1032161889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(256330621/500000000 : ℝ)|^4437 ≤ (4195378314437/10000000000000 : ℝ)^3413
        have hw : |(256330621/500000000 : ℝ)|=(256330621/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542796311/1000000000 : ℝ)|^4437 ≤ (4518769393787/10000000000000 : ℝ)^3413
        have hw : |(542796311/1000000000 : ℝ)|=(542796311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_box_9 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5255626581/10000000000 : ℝ)*x 0 + (-1891987599/10000000000 : ℝ)*x 1 + (2713981573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255626581/10000000000 : ℝ)^4437 ≤ (433314941911/1000000000000 : ℝ)^3413 := by
    have hnat : (5255626581 : ℕ)^4437*1000000000000^3413 ≤ 433314941911^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255626581 10000000000 433314941911 1000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1891987599/10000000000 : ℝ)^4437 ≤ (11480811462827/100000000000000 : ℝ)^3413 := by
    have hnat : (1891987599 : ℕ)^4437*100000000000000^3413 ≤ 11480811462827^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1891987599 10000000000 11480811462827 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713981573/5000000000 : ℝ)^4437 ≤ (706057723867/1562500000000 : ℝ)^3413 := by
    have hnat : (2713981573 : ℕ)^4437*1562500000000^3413 ≤ 706057723867^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713981573 5000000000 706057723867 1562500000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255626581/10000000000 : ℝ), (-1891987599/10000000000 : ℝ), (2713981573/5000000000 : ℝ)] ![(433314941911/1000000000000 : ℝ), (11480811462827/100000000000000 : ℝ), (706057723867/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255626581/10000000000 : ℝ)|^4437 ≤ (433314941911/1000000000000 : ℝ)^3413
        have hw : |(5255626581/10000000000 : ℝ)|=(5255626581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1891987599/10000000000 : ℝ)|^4437 ≤ (11480811462827/100000000000000 : ℝ)^3413
        have hw : |(-1891987599/10000000000 : ℝ)|=(1891987599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713981573/5000000000 : ℝ)|^4437 ≤ (706057723867/1562500000000 : ℝ)^3413
        have hw : |(2713981573/5000000000 : ℝ)|=(2713981573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_box_10 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20529793/39062500 : ℝ)*x 0 + (1356990711/2500000000 : ℝ)*x 1 + (-945993717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20529793/39062500 : ℝ)^4437 ≤ (21665749383941/50000000000000 : ℝ)^3413 := by
    have hnat : (20529793 : ℕ)^4437*50000000000000^3413 ≤ 21665749383941^3413*39062500^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20529793 39062500 21665749383941 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356990711/2500000000 : ℝ)^4437 ≤ (22593845529513/50000000000000 : ℝ)^3413 := by
    have hnat : (1356990711 : ℕ)^4437*50000000000000^3413 ≤ 22593845529513^3413*2500000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356990711 2500000000 22593845529513 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (945993717/5000000000 : ℝ)^4437 ≤ (5740405080593/50000000000000 : ℝ)^3413 := by
    have hnat : (945993717 : ℕ)^4437*50000000000000^3413 ≤ 5740405080593^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945993717 5000000000 5740405080593 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20529793/39062500 : ℝ), (1356990711/2500000000 : ℝ), (-945993717/5000000000 : ℝ)] ![(21665749383941/50000000000000 : ℝ), (22593845529513/50000000000000 : ℝ), (5740405080593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20529793/39062500 : ℝ)|^4437 ≤ (21665749383941/50000000000000 : ℝ)^3413
        have hw : |(20529793/39062500 : ℝ)|=(20529793/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356990711/2500000000 : ℝ)|^4437 ≤ (22593845529513/50000000000000 : ℝ)^3413
        have hw : |(1356990711/2500000000 : ℝ)|=(1356990711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-945993717/5000000000 : ℝ)|^4437 ≤ (5740405080593/50000000000000 : ℝ)^3413
        have hw : |(-945993717/5000000000 : ℝ)|=(945993717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_box_11 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4545014043/10000000000 : ℝ)*x 0 + (2084390977/5000000000 : ℝ)*x 1 + (521097781/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4545014043/10000000000 : ℝ)^4437 ≤ (35874492343479/100000000000000 : ℝ)^3413 := by
    have hnat : (4545014043 : ℕ)^4437*100000000000000^3413 ≤ 35874492343479^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4545014043 10000000000 35874492343479 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084390977/5000000000 : ℝ)^4437 ≤ (2003922021899/6250000000000 : ℝ)^3413 := by
    have hnat : (2084390977 : ℕ)^4437*6250000000000^3413 ≤ 2003922021899^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084390977 5000000000 2003922021899 6250000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521097781/1250000000 : ℝ)^4437 ≤ (32062755290011/100000000000000 : ℝ)^3413 := by
    have hnat : (521097781 : ℕ)^4437*100000000000000^3413 ≤ 32062755290011^3413*1250000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521097781 1250000000 32062755290011 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4545014043/10000000000 : ℝ), (2084390977/5000000000 : ℝ), (521097781/1250000000 : ℝ)] ![(35874492343479/100000000000000 : ℝ), (2003922021899/6250000000000 : ℝ), (32062755290011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4545014043/10000000000 : ℝ)|^4437 ≤ (35874492343479/100000000000000 : ℝ)^3413
        have hw : |(4545014043/10000000000 : ℝ)|=(4545014043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2084390977/5000000000 : ℝ)|^4437 ≤ (2003922021899/6250000000000 : ℝ)^3413
        have hw : |(2084390977/5000000000 : ℝ)|=(2084390977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521097781/1250000000 : ℝ)|^4437 ≤ (32062755290011/100000000000000 : ℝ)^3413
        have hw : |(521097781/1250000000 : ℝ)|=(521097781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_box_12 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-902567237/5000000000 : ℝ)*x 0 + (5518910427/10000000000 : ℝ)*x 1 + (5227019791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (902567237/5000000000 : ℝ)^4437 ≤ (5400209999689/50000000000000 : ℝ)^3413 := by
    have hnat : (902567237 : ℕ)^4437*50000000000000^3413 ≤ 5400209999689^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902567237 5000000000 5400209999689 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5518910427/10000000000 : ℝ)^4437 ≤ (2885903486027/6250000000000 : ℝ)^3413 := by
    have hnat : (5518910427 : ℕ)^4437*6250000000000^3413 ≤ 2885903486027^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518910427 10000000000 2885903486027 6250000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227019791/10000000000 : ℝ)^4437 ≤ (21512562102567/50000000000000 : ℝ)^3413 := by
    have hnat : (5227019791 : ℕ)^4437*50000000000000^3413 ≤ 21512562102567^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227019791 10000000000 21512562102567 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-902567237/5000000000 : ℝ), (5518910427/10000000000 : ℝ), (5227019791/10000000000 : ℝ)] ![(5400209999689/50000000000000 : ℝ), (2885903486027/6250000000000 : ℝ), (21512562102567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-902567237/5000000000 : ℝ)|^4437 ≤ (5400209999689/50000000000000 : ℝ)^3413
        have hw : |(-902567237/5000000000 : ℝ)|=(902567237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5518910427/10000000000 : ℝ)|^4437 ≤ (2885903486027/6250000000000 : ℝ)^3413
        have hw : |(5518910427/10000000000 : ℝ)|=(5518910427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227019791/10000000000 : ℝ)|^4437 ≤ (21512562102567/50000000000000 : ℝ)^3413
        have hw : |(5227019791/10000000000 : ℝ)|=(5227019791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_box_13 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539599667/1000000000 : ℝ)*x 0 + (-98705547/500000000 : ℝ)*x 1 + (261351/500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539599667/1000000000 : ℝ)^4437 ≤ (11210509042623/25000000000000 : ℝ)^3413 := by
    have hnat : (539599667 : ℕ)^4437*25000000000000^3413 ≤ 11210509042623^3413*1000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539599667 1000000000 11210509042623 25000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98705547/500000000 : ℝ)^4437 ≤ (12132837373079/100000000000000 : ℝ)^3413 := by
    have hnat : (98705547 : ℕ)^4437*100000000000000^3413 ≤ 12132837373079^3413*500000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98705547 500000000 12132837373079 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261351/500000 : ℝ)^4437 ≤ (21512563220813/50000000000000 : ℝ)^3413 := by
    have hnat : (261351 : ℕ)^4437*50000000000000^3413 ≤ 21512563220813^3413*500000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261351 500000 21512563220813 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539599667/1000000000 : ℝ), (-98705547/500000000 : ℝ), (261351/500000 : ℝ)] ![(11210509042623/25000000000000 : ℝ), (12132837373079/100000000000000 : ℝ), (21512563220813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539599667/1000000000 : ℝ)|^4437 ≤ (11210509042623/25000000000000 : ℝ)^3413
        have hw : |(539599667/1000000000 : ℝ)|=(539599667/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-98705547/500000000 : ℝ)|^4437 ≤ (12132837373079/100000000000000 : ℝ)^3413
        have hw : |(-98705547/500000000 : ℝ)|=(98705547/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261351/500000 : ℝ)|^4437 ≤ (21512563220813/50000000000000 : ℝ)^3413
        have hw : |(261351/500000 : ℝ)|=(261351/500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_box_14 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395996459/10000000000 : ℝ)*x 0 + (163344369/312500000 : ℝ)*x 1 + (-987055741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395996459/10000000000 : ℝ)^4437 ≤ (44842033890941/100000000000000 : ℝ)^3413 := by
    have hnat : (5395996459 : ℕ)^4437*100000000000000^3413 ≤ 44842033890941^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395996459 10000000000 44842033890941 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163344369/312500000 : ℝ)^4437 ≤ (43025124387049/100000000000000 : ℝ)^3413 := by
    have hnat : (163344369 : ℕ)^4437*100000000000000^3413 ≤ 43025124387049^3413*312500000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163344369 312500000 43025124387049 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (987055741/5000000000 : ℝ)^4437 ≤ (12132841703631/100000000000000 : ℝ)^3413 := by
    have hnat : (987055741 : ℕ)^4437*100000000000000^3413 ≤ 12132841703631^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987055741 5000000000 12132841703631 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395996459/10000000000 : ℝ), (163344369/312500000 : ℝ), (-987055741/5000000000 : ℝ)] ![(44842033890941/100000000000000 : ℝ), (43025124387049/100000000000000 : ℝ), (12132841703631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395996459/10000000000 : ℝ)|^4437 ≤ (44842033890941/100000000000000 : ℝ)^3413
        have hw : |(5395996459/10000000000 : ℝ)|=(5395996459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163344369/312500000 : ℝ)|^4437 ≤ (43025124387049/100000000000000 : ℝ)^3413
        have hw : |(163344369/312500000 : ℝ)|=(163344369/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-987055741/5000000000 : ℝ)|^4437 ≤ (12132841703631/100000000000000 : ℝ)^3413
        have hw : |(-987055741/5000000000 : ℝ)|=(987055741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_box_15 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4044195383/10000000000 : ℝ)*x 0 + (2209589881/5000000000 : ℝ)*x 1 + (2209590091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4044195383/10000000000 : ℝ)^4437 ≤ (30822669394159/100000000000000 : ℝ)^3413 := by
    have hnat : (4044195383 : ℕ)^4437*100000000000000^3413 ≤ 30822669394159^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4044195383 10000000000 30822669394159 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2209589881/5000000000 : ℝ)^4437 ≤ (6917732632303/20000000000000 : ℝ)^3413 := by
    have hnat : (2209589881 : ℕ)^4437*20000000000000^3413 ≤ 6917732632303^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209589881 5000000000 6917732632303 20000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2209590091/5000000000 : ℝ)^4437 ≤ (34588667435121/100000000000000 : ℝ)^3413 := by
    have hnat : (2209590091 : ℕ)^4437*100000000000000^3413 ≤ 34588667435121^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209590091 5000000000 34588667435121 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4044195383/10000000000 : ℝ), (2209589881/5000000000 : ℝ), (2209590091/5000000000 : ℝ)] ![(30822669394159/100000000000000 : ℝ), (6917732632303/20000000000000 : ℝ), (34588667435121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4044195383/10000000000 : ℝ)|^4437 ≤ (30822669394159/100000000000000 : ℝ)^3413
        have hw : |(4044195383/10000000000 : ℝ)|=(4044195383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2209589881/5000000000 : ℝ)|^4437 ≤ (6917732632303/20000000000000 : ℝ)^3413
        have hw : |(2209589881/5000000000 : ℝ)|=(2209589881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2209590091/5000000000 : ℝ)|^4437 ≤ (34588667435121/100000000000000 : ℝ)^3413
        have hw : |(2209590091/5000000000 : ℝ)|=(2209590091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1470_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40008003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15473/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10743/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15923/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58431/100000 : ℝ) ∧ (15971/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (2679/3125 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15473/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10743/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15473/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10743/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15473/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10743/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15473/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10743/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15473/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10743/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15473/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10743/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10743/100000 : ℝ) ^ (4435/1024 : ℝ) ≤ (6364318170948319/100000000000000000000 : ℝ) := by
    have hpowers : (10743/100000 : ℝ)^4435 ≤ (6364318170948319/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10743 : ℕ)^4435*100000000000000000000^1024 ≤ 6364318170948319^1024*100000^4435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10743 100000 6364318170948319 100000000000000000000 4435 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10743/100000 : ℝ)) (X := (6364318170948319/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15473/100000 : ℝ) ^ (4435/1024 : ℝ) ≤ (30903164235121339/100000000000000000000 : ℝ) := by
    have hpowers : (15473/100000 : ℝ)^4435 ≤ (30903164235121339/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15473 : ℕ)^4435*100000000000000000000^1024 ≤ 30903164235121339^1024*100000^4435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15473 100000 30903164235121339 100000000000000000000 4435 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15473/100000 : ℝ)) (X := (30903164235121339/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006364318170948319/50000000000000000000 : ℝ) ≤ (10000293877917933/10000000000000000 : ℝ) ^ (4435/1024 : ℝ) := by
    have hpowers : (50006364318170948319/50000000000000000000 : ℝ)^1024 ≤ (10000293877917933/10000000000000000 : ℝ)^4435 := by
      have hnat : (50006364318170948319 : ℕ)^1024*10000000000000000^4435 ≤ 10000293877917933^4435*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006364318170948319 50000000000000000000 10000293877917933 10000000000000000 1024 4435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000293877917933/10000000000000000 : ℝ)) (X := (50006364318170948319/50000000000000000000 : ℝ)) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018633741203034829/50000000000000000000 : ℝ) ≤ (10000860348005783/10000000000000000 : ℝ) ^ (4435/1024 : ℝ) := by
    have hpowers : (50018633741203034829/50000000000000000000 : ℝ)^1024 ≤ (10000860348005783/10000000000000000 : ℝ)^4435 := by
      have hnat : (50018633741203034829 : ℕ)^1024*10000000000000000^4435 ≤ 10000860348005783^4435*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018633741203034829 50000000000000000000 10000860348005783 10000000000000000 1024 4435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000860348005783/10000000000000000 : ℝ)) (X := (50018633741203034829/50000000000000000000 : ℝ)) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030903164235121339/50000000000000000000 : ℝ) ≤ (10001426818093633/10000000000000000 : ℝ) ^ (4435/1024 : ℝ) := by
    have hpowers : (50030903164235121339/50000000000000000000 : ℝ)^1024 ≤ (10001426818093633/10000000000000000 : ℝ)^4435 := by
      have hnat : (50030903164235121339 : ℕ)^1024*10000000000000000^4435 ≤ 10001426818093633^4435*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030903164235121339 50000000000000000000 10001426818093633 10000000000000000 1024 4435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001426818093633/10000000000000000 : ℝ)) (X := (50030903164235121339/50000000000000000000 : ℝ)) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6364318170948319/100000000000000000000 : ℝ) ≤ ((4728921886624427799/4730000000000000000 : ℝ)+2*(11329401757/9460000000000 : ℝ)*(10743/100000 : ℝ))^(4435/1024 : ℝ) := by
    rw [show (4728921886624427799/4730000000000000000 : ℝ)+2*(11329401757/9460000000000 : ℝ)*(10743/100000 : ℝ)=(10000293877917933/10000000000000000 : ℝ) by norm_num, show 1+2*(6364318170948319/100000000000000000000 : ℝ)=(50006364318170948319/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30903164235121339/100000000000000000000 : ℝ)+(6364318170948319/100000000000000000000 : ℝ) ≤ ((4728921886624427799/4730000000000000000 : ℝ)+(11329401757/9460000000000 : ℝ)*((15473/100000 : ℝ)+(10743/100000 : ℝ)))^(4435/1024 : ℝ) := by
    rw [show (4728921886624427799/4730000000000000000 : ℝ)+(11329401757/9460000000000 : ℝ)*((15473/100000 : ℝ)+(10743/100000 : ℝ))=(10000860348005783/10000000000000000 : ℝ) by norm_num, show 1+(30903164235121339/100000000000000000000 : ℝ)+(6364318170948319/100000000000000000000 : ℝ)=(50018633741203034829/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30903164235121339/100000000000000000000 : ℝ) ≤ ((4728921886624427799/4730000000000000000 : ℝ)+2*(11329401757/9460000000000 : ℝ)*(15473/100000 : ℝ))^(4435/1024 : ℝ) := by
    rw [show (4728921886624427799/4730000000000000000 : ℝ)+2*(11329401757/9460000000000 : ℝ)*(15473/100000 : ℝ)=(10001426818093633/10000000000000000 : ℝ) by norm_num, show 1+2*(30903164235121339/100000000000000000000 : ℝ)=(50030903164235121339/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4728921886624427799/4730000000000000000 : ℝ)*(X 1 0+X 2 0)+(11329401757/9460000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4435/1024 : ℝ)) (lo := (10743/100000 : ℝ)) (hi := (15473/100000 : ℝ)) (c := (4728921886624427799/4730000000000000000 : ℝ)) (alpha := (11329401757/9460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4728921886624427799/4730000000000000000 : ℝ)*(X 0 1+X 2 1)+(11329401757/9460000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4435/1024 : ℝ)) (lo := (10743/100000 : ℝ)) (hi := (15473/100000 : ℝ)) (c := (4728921886624427799/4730000000000000000 : ℝ)) (alpha := (11329401757/9460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4728921886624427799/4730000000000000000 : ℝ)*(X 0 2+X 1 2)+(11329401757/9460000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4435/1024 : ℝ)) (lo := (10743/100000 : ℝ)) (hi := (15473/100000 : ℝ)) (c := (4728921886624427799/4730000000000000000 : ℝ)) (alpha := (11329401757/9460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-855216589/5000000000 : ℝ)*X 0 0+(5407389831/10000000000 : ℝ)*X 0 1+(540738991/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((658750709/1250000000 : ℝ)*X 1 0+(-1900645537/10000000000 : ℝ)*X 1 1+(2703694943/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((658750719/1250000000 : ℝ)*X 2 0+(5407389863/10000000000 : ℝ)*X 2 1+(-1900645461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((898973073/2000000000 : ℝ)*X 0 0+(2097224239/5000000000 : ℝ)*X 0 1+(4194448733/10000000000 : ℝ)*X 0 2+(898973073/2000000000 : ℝ)*X 1 0+(2097224239/5000000000 : ℝ)*X 1 1+(4194448733/10000000000 : ℝ)*X 1 2+(898973073/2000000000 : ℝ)*X 2 0+(2097224239/5000000000 : ℝ)*X 2 1+(4194448733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1079416641/5000000000 : ℝ)*X 0 0+(5241998269/10000000000 : ℝ)*X 0 1+(209679949/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5385535373/10000000000 : ℝ)*X 1 0+(-1968180213/10000000000 : ℝ)*X 1 1+(5241998367/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5385535593/10000000000 : ℝ)*X 2 0+(5241998459/10000000000 : ℝ)*X 2 1+(-1968179793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4082408869/10000000000 : ℝ)*X 0 0+(440053643/1000000000 : ℝ)*X 0 1+(275033563/625000000 : ℝ)*X 0 2+(4082408869/10000000000 : ℝ)*X 1 0+(440053643/1000000000 : ℝ)*X 1 1+(275033563/625000000 : ℝ)*X 1 2+(4082408869/10000000000 : ℝ)*X 2 0+(440053643/1000000000 : ℝ)*X 2 1+(275033563/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1032161889/5000000000 : ℝ)*X 0 0+(256330621/500000000 : ℝ)*X 0 1+(542796311/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5255626581/10000000000 : ℝ)*X 1 0+(-1891987599/10000000000 : ℝ)*X 1 1+(2713981573/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((20529793/39062500 : ℝ)*X 2 0+(1356990711/2500000000 : ℝ)*X 2 1+(-945993717/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4545014043/10000000000 : ℝ)*X 0 0+(2084390977/5000000000 : ℝ)*X 0 1+(521097781/1250000000 : ℝ)*X 0 2+(4545014043/10000000000 : ℝ)*X 1 0+(2084390977/5000000000 : ℝ)*X 1 1+(521097781/1250000000 : ℝ)*X 1 2+(4545014043/10000000000 : ℝ)*X 2 0+(2084390977/5000000000 : ℝ)*X 2 1+(521097781/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-902567237/5000000000 : ℝ)*X 0 0+(5518910427/10000000000 : ℝ)*X 0 1+(5227019791/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((539599667/1000000000 : ℝ)*X 1 0+(-98705547/500000000 : ℝ)*X 1 1+(261351/500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5395996459/10000000000 : ℝ)*X 2 0+(163344369/312500000 : ℝ)*X 2 1+(-987055741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4044195383/10000000000 : ℝ)*X 0 0+(2209589881/5000000000 : ℝ)*X 0 1+(2209590091/5000000000 : ℝ)*X 0 2+(4044195383/10000000000 : ℝ)*X 1 0+(2209589881/5000000000 : ℝ)*X 1 1+(2209590091/5000000000 : ℝ)*X 1 2+(4044195383/10000000000 : ℝ)*X 2 0+(2209589881/5000000000 : ℝ)*X 2 1+(2209590091/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15923/25000 : ℝ) ≤ (-37656669126691865294773973060361/59125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (910631/5000000000000 : ℝ)*(lower1) + (1971489/1250000000000 : ℝ)*(lower2) + (4691543/2500000000000 : ℝ)*(lower3) + (23927951/25000000000000 : ℝ)*(lower4) + (1080292322620387/50000000000000 : ℝ)*(major0) + (1080292322620387/50000000000000 : ℝ)*(major1) + (1080292322620387/50000000000000 : ℝ)*(major2) + (2992303983066911/100000000000000 : ℝ)*(sp4) + (187016398332049/6250000000000 : ℝ)*(sp5) + (374033253315931/12500000000000 : ℝ)*(sp6) + (168754753735109/12500000000000 : ℝ)*(sp7) + (41609754127/100000000000000 : ℝ)*(sp13) + (4744567433/12500000000000 : ℝ)*(sp14) + (57253080873/100000000000000 : ℝ)*(sp15) + (270019056592349/20000000000000 : ℝ)*(f.failure) + (2992303983066911/100000000000000 : ℝ)*(f.sum) + (1981403770493/473000000000000000000000000 : ℝ)*base65 + (285272633796061787/236500000000000000000000000000000 : ℝ)*base68 + (76850941445938213/236500000000000000000000000000000 : ℝ)*base69 + (944656487342061787/236500000000000000000000000000000 : ℝ)*base72 + (28236307403/14781250000000000000000000 : ℝ)*base73 + (1334598855888561787/236500000000000000000000000000000 : ℝ)*base76 + (660229553749061787/236500000000000000000000000000000 : ℝ)*base78 + (1284657420498561787/236500000000000000000000000000000 : ℝ)*base80 + (9034598663/7390625000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1430953/500000000000000000000 : ℝ)*base90 + (1430953/500000000000000000000 : ℝ)*base92 + (1430953/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58431/100000 : ℝ) ≤ (276390872139847173438095847/473000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12875659/100000000000000 : ℝ)*(lower0) + (27430717/100000000000000 : ℝ)*(lower1) + (1901393/20000000000000 : ℝ)*(lower2) + (1324933/2500000000000 : ℝ)*(lower3) + (446797679801443/20000000000000 : ℝ)*(major0) + (446797679801443/20000000000000 : ℝ)*(major1) + (446797679801443/20000000000000 : ℝ)*(major2) + (1526267741646247/50000000000000 : ℝ)*(sp0) + (3052534380423553/100000000000000 : ℝ)*(sp1) + (1526266986396967/50000000000000 : ℝ)*(sp2) + (139596170920639/10000000000000 : ℝ)*(sp3) + (1102868941/100000000000000 : ℝ)*(sp5) + (871392731/50000000000000 : ℝ)*(sp7) + (1180077/78125000000 : ℝ)*(sp10) + (348990862997963/25000000000000 : ℝ)*(f.failure) + (1526267741646247/50000000000000 : ℝ)*(f.sum) + (543163741053/473000000000000000000000000 : ℝ)*base66 + (86553339492613957/94600000000000000000000000000000 : ℝ)*base67 + (750434049257413957/94600000000000000000000000000000 : ℝ)*base69 + (109269024055186043/94600000000000000000000000000000 : ℝ)*base72 + (177509091277/473000000000000000000000000 : ℝ)*base73 + (100121055911586043/94600000000000000000000000000000 : ℝ)*base76 + (121472272935413957/94600000000000000000000000000000 : ℝ)*base77 + (257863234600186043/94600000000000000000000000000000 : ℝ)*base80 + (3098428230459/473000000000000000000000000 : ℝ)*base81 + (1052111/625000000000000000000 : ℝ)*base90 + (1052111/625000000000000000000 : ℝ)*base92 + (1052111/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (15971/20000 : ℝ) ≤ (1073085144208053489266366967309/1343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2671711/25000000000000 : ℝ)*(upper0) + (18302323/100000000000000 : ℝ)*(lower1) + (21852903/20000000000000 : ℝ)*(lower3) + (38618447/50000000000000 : ℝ)*(upper4) + (304064628216283/12500000000000 : ℝ)*(major0) + (304064628216283/12500000000000 : ℝ)*(major1) + (304064628216283/12500000000000 : ℝ)*(major2) + (78156987/156250000000 : ℝ)*(sp1) + (2596291631/50000000000000 : ℝ)*(sp2) + (9020527737/50000000000000 : ℝ)*(sp3) + (3318395861817237/100000000000000 : ℝ)*(sp8) + (3318345841345557/100000000000000 : ℝ)*(sp9) + (1659195334616987/50000000000000 : ℝ)*(sp10) + (1520000982219859/100000000000000 : ℝ)*(sp11) + (1520019023275333/100000000000000 : ℝ)*(f.failure) + (3318395861817237/100000000000000 : ℝ)*(f.sum) + (37555392009/8600000000000000000000000 : ℝ)*base65 + (13185730850145353/5375000000000000000000000000000 : ℝ)*base68 + (20596531440104647/5375000000000000000000000000000 : ℝ)*base69 + (22117371672604647/5375000000000000000000000000000 : ℝ)*base71 + (231530462203/43000000000000000000000000 : ℝ)*base73 + (10759508880604647/5375000000000000000000000000000 : ℝ)*base75 + (27418878012979647/5375000000000000000000000000000 : ℝ)*base77 + (53666091681604647/5375000000000000000000000000000 : ℝ)*base79 + (128303751/215000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (7510001/2500000000000000000000 : ℝ)*base90 + (7510001/2500000000000000000000 : ℝ)*base92 + (7510001/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-2679/3125 : ℝ) ≤ (-3167808316560641408062335533721/3695312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (14300921/20000000000000 : ℝ)*(lower0) + (31578157/100000000000000 : ℝ)*(lower1) + (4294159/100000000000000 : ℝ)*(upper3) + (207420047/100000000000000 : ℝ)*(lower4) + (154411979173139/6250000000000 : ℝ)*(major0) + (154411979173139/6250000000000 : ℝ)*(major1) + (154411979173139/6250000000000 : ℝ)*(major2) + (129179129537/100000000000000 : ℝ)*(sp6) + (10141978813/25000000000000 : ℝ)*(sp7) + (889056267/50000000000000 : ℝ)*(sp8) + (1712972828391379/50000000000000 : ℝ)*(sp12) + (856486858723823/25000000000000 : ℝ)*(sp13) + (685163651153151/20000000000000 : ℝ)*(sp14) + (1543770345847567/100000000000000 : ℝ)*(sp15) + (1543810913762819/100000000000000 : ℝ)*(f.failure) + (856486858723823/25000000000000 : ℝ)*(f.sum) + (323620867997/473000000000000000000000000 : ℝ)*base66 + (219589187442808939/29562500000000000000000000000000 : ℝ)*base68 + (540288618590691061/29562500000000000000000000000000 : ℝ)*base69 + (349435711562621439/29562500000000000000000000000000 : ℝ)*base72 + (379170419893/236500000000000000000000000 : ℝ)*base73 + (43737952508433939/29562500000000000000000000000000 : ℝ)*base76 + (265297713166246439/29562500000000000000000000000000 : ℝ)*base78 + (283041208500371439/29562500000000000000000000000000 : ℝ)*base80 + (12345921552461/473000000000000000000000000 : ℝ)*base81 + (3840457/2500000000000000000000 : ℝ)*base89 + (3840457/2500000000000000000000 : ℝ)*base91 + (3840457/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1470_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40008003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15473/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10743/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15923/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58431/100000 : ℝ) else (15971/20000 : ℝ) ≤ X j i ∧ X j i ≤ (2679/3125 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1470_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1470_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40008003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10741/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15923/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58431/100000 : ℝ) else (15971/20000 : ℝ) ≤ X j i ∧ X j i ≤ (2679/3125 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1470_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1470_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40008003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10741/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15923/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58431/100000 : ℝ) else (15971/20000 : ℝ) ≤ X j i ∧ X j i ≤ (2679/3125 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1470_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

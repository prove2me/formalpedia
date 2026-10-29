-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1601_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:39:07.371702+00:00
-- url     : https://prove2.me/submissions/6a1818ba-edbe-44ab-ba37-68596097e3c0

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
theorem support_rectangle_w1601_s3_0 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-215881387/1250000000 : ℝ)*x 0 + (5462965189/10000000000 : ℝ)*x 1 + (5179249607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215881387/1250000000 : ℝ)^4723 ≤ (10621043300451/100000000000000 : ℝ)^3699 := by
    have hnat : (215881387 : ℕ)^4723*100000000000000^3699 ≤ 10621043300451^3699*1250000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215881387 1250000000 10621043300451 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462965189/10000000000 : ℝ)^4723 ≤ (23105232166177/50000000000000 : ℝ)^3699 := by
    have hnat : (5462965189 : ℕ)^4723*50000000000000^3699 ≤ 23105232166177^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462965189 10000000000 23105232166177 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179249607/10000000000 : ℝ)^4723 ≤ (43168492344163/100000000000000 : ℝ)^3699 := by
    have hnat : (5179249607 : ℕ)^4723*100000000000000^3699 ≤ 43168492344163^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179249607 10000000000 43168492344163 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215881387/1250000000 : ℝ), (5462965189/10000000000 : ℝ), (5179249607/10000000000 : ℝ)] ![(10621043300451/100000000000000 : ℝ), (23105232166177/50000000000000 : ℝ), (43168492344163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215881387/1250000000 : ℝ)|^4723 ≤ (10621043300451/100000000000000 : ℝ)^3699
        have hw : |(-215881387/1250000000 : ℝ)|=(215881387/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462965189/10000000000 : ℝ)|^4723 ≤ (23105232166177/50000000000000 : ℝ)^3699
        have hw : |(5462965189/10000000000 : ℝ)|=(5462965189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179249607/10000000000 : ℝ)|^4723 ≤ (43168492344163/100000000000000 : ℝ)^3699
        have hw : |(5179249607/10000000000 : ℝ)|=(5179249607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s3_1 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355023247/10000000000 : ℝ)*x 0 + (-374686067/2000000000 : ℝ)*x 1 + (5179249481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355023247/10000000000 : ℝ)^4723 ≤ (11261959186433/25000000000000 : ℝ)^3699 := by
    have hnat : (5355023247 : ℕ)^4723*25000000000000^3699 ≤ 11261959186433^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355023247 10000000000 11261959186433 25000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (374686067/2000000000 : ℝ)^4723 ≤ (2945918059951/25000000000000 : ℝ)^3699 := by
    have hnat : (374686067 : ℕ)^4723*25000000000000^3699 ≤ 2945918059951^3699*2000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374686067 2000000000 2945918059951 25000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179249481/10000000000 : ℝ)^4723 ≤ (43168491003239/100000000000000 : ℝ)^3699 := by
    have hnat : (5179249481 : ℕ)^4723*100000000000000^3699 ≤ 43168491003239^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179249481 10000000000 43168491003239 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355023247/10000000000 : ℝ), (-374686067/2000000000 : ℝ), (5179249481/10000000000 : ℝ)] ![(11261959186433/25000000000000 : ℝ), (2945918059951/25000000000000 : ℝ), (43168491003239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355023247/10000000000 : ℝ)|^4723 ≤ (11261959186433/25000000000000 : ℝ)^3699
        have hw : |(5355023247/10000000000 : ℝ)|=(5355023247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-374686067/2000000000 : ℝ)|^4723 ≤ (2945918059951/25000000000000 : ℝ)^3699
        have hw : |(-374686067/2000000000 : ℝ)|=(374686067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179249481/10000000000 : ℝ)|^4723 ≤ (43168491003239/100000000000000 : ℝ)^3699
        have hw : |(5179249481/10000000000 : ℝ)|=(5179249481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s3_2 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355023769/10000000000 : ℝ)*x 0 + (5179249037/10000000000 : ℝ)*x 1 + (-74937209/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355023769/10000000000 : ℝ)^4723 ≤ (22523921176277/50000000000000 : ℝ)^3699 := by
    have hnat : (5355023769 : ℕ)^4723*50000000000000^3699 ≤ 22523921176277^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355023769 10000000000 22523921176277 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179249037/10000000000 : ℝ)^4723 ≤ (21584243139039/50000000000000 : ℝ)^3699 := by
    have hnat : (5179249037 : ℕ)^4723*50000000000000^3699 ≤ 21584243139039^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179249037 10000000000 21584243139039 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74937209/400000000 : ℝ)^4723 ≤ (589183567819/5000000000000 : ℝ)^3699 := by
    have hnat : (74937209 : ℕ)^4723*5000000000000^3699 ≤ 589183567819^3699*400000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74937209 400000000 589183567819 5000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355023769/10000000000 : ℝ), (5179249037/10000000000 : ℝ), (-74937209/400000000 : ℝ)] ![(22523921176277/50000000000000 : ℝ), (21584243139039/50000000000000 : ℝ), (589183567819/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355023769/10000000000 : ℝ)|^4723 ≤ (22523921176277/50000000000000 : ℝ)^3699
        have hw : |(5355023769/10000000000 : ℝ)|=(5355023769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179249037/10000000000 : ℝ)|^4723 ≤ (21584243139039/50000000000000 : ℝ)^3699
        have hw : |(5179249037/10000000000 : ℝ)|=(5179249037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-74937209/400000000 : ℝ)|^4723 ≤ (589183567819/5000000000000 : ℝ)^3699
        have hw : |(-74937209/400000000 : ℝ)|=(74937209/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s3_3 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2109965899/5000000000 : ℝ)*x 0 + (3886442937/10000000000 : ℝ)*x 1 + (4575375419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109965899/5000000000 : ℝ)^4723 ≤ (6646731567311/20000000000000 : ℝ)^3699 := by
    have hnat : (2109965899 : ℕ)^4723*20000000000000^3699 ≤ 6646731567311^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109965899 5000000000 6646731567311 20000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3886442937/10000000000 : ℝ)^4723 ≤ (934926419197/3125000000000 : ℝ)^3699 := by
    have hnat : (3886442937 : ℕ)^4723*3125000000000^3699 ≤ 934926419197^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3886442937 10000000000 934926419197 3125000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4575375419/10000000000 : ℝ)^4723 ≤ (36848696737653/100000000000000 : ℝ)^3699 := by
    have hnat : (4575375419 : ℕ)^4723*100000000000000^3699 ≤ 36848696737653^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4575375419 10000000000 36848696737653 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2109965899/5000000000 : ℝ), (3886442937/10000000000 : ℝ), (4575375419/10000000000 : ℝ)] ![(6646731567311/20000000000000 : ℝ), (934926419197/3125000000000 : ℝ), (36848696737653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2109965899/5000000000 : ℝ)|^4723 ≤ (6646731567311/20000000000000 : ℝ)^3699
        have hw : |(2109965899/5000000000 : ℝ)|=(2109965899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3886442937/10000000000 : ℝ)|^4723 ≤ (934926419197/3125000000000 : ℝ)^3699
        have hw : |(3886442937/10000000000 : ℝ)|=(3886442937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4575375419/10000000000 : ℝ)|^4723 ≤ (36848696737653/100000000000000 : ℝ)^3699
        have hw : |(4575375419/10000000000 : ℝ)|=(4575375419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s3_4 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-431781027/2500000000 : ℝ)*x 0 + (518135961/1000000000 : ℝ)*x 1 + (1365208199/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431781027/2500000000 : ℝ)^4723 ≤ (1327702076781/12500000000000 : ℝ)^3699 := by
    have hnat : (431781027 : ℕ)^4723*12500000000000^3699 ≤ 1327702076781^3699*2500000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431781027 2500000000 1327702076781 12500000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518135961/1000000000 : ℝ)^4723 ≤ (43190948799893/100000000000000 : ℝ)^3699 := by
    have hnat : (518135961 : ℕ)^4723*100000000000000^3699 ≤ 43190948799893^3699*1000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518135961 1000000000 43190948799893 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365208199/2500000000 : ℝ)^4723 ≤ (23093717289293/50000000000000 : ℝ)^3699 := by
    have hnat : (1365208199 : ℕ)^4723*50000000000000^3699 ≤ 23093717289293^3699*2500000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365208199 2500000000 23093717289293 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431781027/2500000000 : ℝ), (518135961/1000000000 : ℝ), (1365208199/2500000000 : ℝ)] ![(1327702076781/12500000000000 : ℝ), (43190948799893/100000000000000 : ℝ), (23093717289293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431781027/2500000000 : ℝ)|^4723 ≤ (1327702076781/12500000000000 : ℝ)^3699
        have hw : |(-431781027/2500000000 : ℝ)|=(431781027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518135961/1000000000 : ℝ)|^4723 ≤ (43190948799893/100000000000000 : ℝ)^3699
        have hw : |(518135961/1000000000 : ℝ)|=(518135961/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365208199/2500000000 : ℝ)|^4723 ≤ (23093717289293/50000000000000 : ℝ)^3699
        have hw : |(1365208199/2500000000 : ℝ)|=(1365208199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s3_5 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279801621/10000000000 : ℝ)*x 0 + (-1591846891/10000000000 : ℝ)*x 1 + (218433309/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279801621/10000000000 : ℝ)^4723 ≤ (44241454790301/100000000000000 : ℝ)^3699 := by
    have hnat : (5279801621 : ℕ)^4723*100000000000000^3699 ≤ 44241454790301^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279801621 10000000000 44241454790301 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1591846891/10000000000 : ℝ)^4723 ≤ (9571111392791/100000000000000 : ℝ)^3699 := by
    have hnat : (1591846891 : ℕ)^4723*100000000000000^3699 ≤ 9571111392791^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1591846891 10000000000 9571111392791 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218433309/400000000 : ℝ)^4723 ≤ (46187433811831/100000000000000 : ℝ)^3699 := by
    have hnat : (218433309 : ℕ)^4723*100000000000000^3699 ≤ 46187433811831^3699*400000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218433309 400000000 46187433811831 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279801621/10000000000 : ℝ), (-1591846891/10000000000 : ℝ), (218433309/400000000 : ℝ)] ![(44241454790301/100000000000000 : ℝ), (9571111392791/100000000000000 : ℝ), (46187433811831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279801621/10000000000 : ℝ)|^4723 ≤ (44241454790301/100000000000000 : ℝ)^3699
        have hw : |(5279801621/10000000000 : ℝ)|=(5279801621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1591846891/10000000000 : ℝ)|^4723 ≤ (9571111392791/100000000000000 : ℝ)^3699
        have hw : |(-1591846891/10000000000 : ℝ)|=(1591846891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218433309/400000000 : ℝ)|^4723 ≤ (46187433811831/100000000000000 : ℝ)^3699
        have hw : |(218433309/400000000 : ℝ)|=(218433309/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s3_6 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527980159/1000000000 : ℝ)*x 0 + (2730416407/5000000000 : ℝ)*x 1 + (-198980851/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527980159/1000000000 : ℝ)^4723 ≤ (44241454458631/100000000000000 : ℝ)^3699 := by
    have hnat : (527980159 : ℕ)^4723*100000000000000^3699 ≤ 44241454458631^3699*1000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527980159 1000000000 44241454458631 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730416407/5000000000 : ℝ)^4723 ≤ (1847497390919/4000000000000 : ℝ)^3699 := by
    have hnat : (2730416407 : ℕ)^4723*4000000000000^3699 ≤ 1847497390919^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730416407 5000000000 1847497390919 4000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198980851/1250000000 : ℝ)^4723 ≤ (1914222151119/20000000000000 : ℝ)^3699 := by
    have hnat : (198980851 : ℕ)^4723*20000000000000^3699 ≤ 1914222151119^3699*1250000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198980851 1250000000 1914222151119 20000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527980159/1000000000 : ℝ), (2730416407/5000000000 : ℝ), (-198980851/1250000000 : ℝ)] ![(44241454458631/100000000000000 : ℝ), (1847497390919/4000000000000 : ℝ), (1914222151119/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527980159/1000000000 : ℝ)|^4723 ≤ (44241454458631/100000000000000 : ℝ)^3699
        have hw : |(527980159/1000000000 : ℝ)|=(527980159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730416407/5000000000 : ℝ)|^4723 ≤ (1847497390919/4000000000000 : ℝ)^3699
        have hw : |(2730416407/5000000000 : ℝ)|=(2730416407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-198980851/1250000000 : ℝ)|^4723 ≤ (1914222151119/20000000000000 : ℝ)^3699
        have hw : |(-198980851/1250000000 : ℝ)|=(198980851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s3_7 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4220108289/10000000000 : ℝ)*x 0 + (4570251119/10000000000 : ℝ)*x 1 + (1945810851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4220108289/10000000000 : ℝ)^4723 ≤ (33235432562933/100000000000000 : ℝ)^3699 := by
    have hnat : (4220108289 : ℕ)^4723*100000000000000^3699 ≤ 33235432562933^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220108289 10000000000 33235432562933 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4570251119/10000000000 : ℝ)^4723 ≤ (36796010618371/100000000000000 : ℝ)^3699 := by
    have hnat : (4570251119 : ℕ)^4723*100000000000000^3699 ≤ 36796010618371^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4570251119 10000000000 36796010618371 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1945810851/5000000000 : ℝ)^4723 ≤ (1498427840497/5000000000000 : ℝ)^3699 := by
    have hnat : (1945810851 : ℕ)^4723*5000000000000^3699 ≤ 1498427840497^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945810851 5000000000 1498427840497 5000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4220108289/10000000000 : ℝ), (4570251119/10000000000 : ℝ), (1945810851/5000000000 : ℝ)] ![(33235432562933/100000000000000 : ℝ), (36796010618371/100000000000000 : ℝ), (1498427840497/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4220108289/10000000000 : ℝ)|^4723 ≤ (33235432562933/100000000000000 : ℝ)^3699
        have hw : |(4220108289/10000000000 : ℝ)|=(4220108289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4570251119/10000000000 : ℝ)|^4723 ≤ (36796010618371/100000000000000 : ℝ)^3699
        have hw : |(4570251119/10000000000 : ℝ)|=(4570251119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1945810851/5000000000 : ℝ)|^4723 ≤ (1498427840497/5000000000000 : ℝ)^3699
        have hw : |(1945810851/5000000000 : ℝ)|=(1945810851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1601_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85706131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16533/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2043/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (259/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4093/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16533/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2043/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16533/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2043/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16533/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2043/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16533/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2043/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16533/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2043/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16533/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2043/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2043/20000 : ℝ) ^ (4719/1024 : ℝ) ≤ (2717538195161737/100000000000000000000 : ℝ) := by
    have hpowers : (2043/20000 : ℝ)^4719 ≤ (2717538195161737/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2043 : ℕ)^4719*100000000000000000000^1024 ≤ 2717538195161737^1024*20000^4719 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2043 20000 2717538195161737 100000000000000000000 4719 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2043/20000 : ℝ)) (X := (2717538195161737/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16533/100000 : ℝ) ^ (4719/1024 : ℝ) ≤ (6248748513069209/25000000000000000000 : ℝ) := by
    have hpowers : (16533/100000 : ℝ)^4719 ≤ (6248748513069209/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16533 : ℕ)^4719*25000000000000000000^1024 ≤ 6248748513069209^1024*100000^4719 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16533 100000 6248748513069209 25000000000000000000 4719 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16533/100000 : ℝ)) (X := (6248748513069209/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002717538195161737/50000000000000000000 : ℝ) ≤ (10000117935999193/10000000000000000 : ℝ) ^ (4719/1024 : ℝ) := by
    have hpowers : (50002717538195161737/50000000000000000000 : ℝ)^1024 ≤ (10000117935999193/10000000000000000 : ℝ)^4719 := by
      have hnat : (50002717538195161737 : ℕ)^1024*10000000000000000^4719 ≤ 10000117935999193^4719*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002717538195161737 50000000000000000000 10000117935999193 10000000000000000 1024 4719 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000117935999193/10000000000000000 : ℝ)) (X := (50002717538195161737/50000000000000000000 : ℝ)) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027712532247438573/100000000000000000000 : ℝ) ≤ (10000601283210221/10000000000000000 : ℝ) ^ (4719/1024 : ℝ) := by
    have hpowers : (100027712532247438573/100000000000000000000 : ℝ)^1024 ≤ (10000601283210221/10000000000000000 : ℝ)^4719 := by
      have hnat : (100027712532247438573 : ℕ)^1024*10000000000000000^4719 ≤ 10000601283210221^4719*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027712532247438573 100000000000000000000 10000601283210221 10000000000000000 1024 4719 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000601283210221/10000000000000000 : ℝ)) (X := (100027712532247438573/100000000000000000000 : ℝ)) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506248748513069209/12500000000000000000 : ℝ) ≤ (10001084630421249/10000000000000000 : ℝ) ^ (4719/1024 : ℝ) := by
    have hpowers : (12506248748513069209/12500000000000000000 : ℝ)^1024 ≤ (10001084630421249/10000000000000000 : ℝ)^4719 := by
      have hnat : (12506248748513069209 : ℕ)^1024*10000000000000000^4719 ≤ 10001084630421249^4719*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506248748513069209 12500000000000000000 10001084630421249 10000000000000000 1024 4719 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001084630421249/10000000000000000 : ℝ)) (X := (12506248748513069209/12500000000000000000 : ℝ)) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2717538195161737/100000000000000000000 : ℝ) ≤ ((3509492796451199963/3510000000000000000 : ℝ)+2*(120836802757/157950000000000 : ℝ)*(2043/20000 : ℝ))^(4719/1024 : ℝ) := by
    rw [show (3509492796451199963/3510000000000000000 : ℝ)+2*(120836802757/157950000000000 : ℝ)*(2043/20000 : ℝ)=(10000117935999193/10000000000000000 : ℝ) by norm_num, show 1+2*(2717538195161737/100000000000000000000 : ℝ)=(50002717538195161737/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6248748513069209/25000000000000000000 : ℝ)+(2717538195161737/100000000000000000000 : ℝ) ≤ ((3509492796451199963/3510000000000000000 : ℝ)+(120836802757/157950000000000 : ℝ)*((16533/100000 : ℝ)+(2043/20000 : ℝ)))^(4719/1024 : ℝ) := by
    rw [show (3509492796451199963/3510000000000000000 : ℝ)+(120836802757/157950000000000 : ℝ)*((16533/100000 : ℝ)+(2043/20000 : ℝ))=(10000601283210221/10000000000000000 : ℝ) by norm_num, show 1+(6248748513069209/25000000000000000000 : ℝ)+(2717538195161737/100000000000000000000 : ℝ)=(100027712532247438573/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6248748513069209/25000000000000000000 : ℝ) ≤ ((3509492796451199963/3510000000000000000 : ℝ)+2*(120836802757/157950000000000 : ℝ)*(16533/100000 : ℝ))^(4719/1024 : ℝ) := by
    rw [show (3509492796451199963/3510000000000000000 : ℝ)+2*(120836802757/157950000000000 : ℝ)*(16533/100000 : ℝ)=(10001084630421249/10000000000000000 : ℝ) by norm_num, show 1+2*(6248748513069209/25000000000000000000 : ℝ)=(12506248748513069209/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3509492796451199963/3510000000000000000 : ℝ)*(X 1 0+X 2 0)+(120836802757/157950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4719/1024 : ℝ)) (lo := (2043/20000 : ℝ)) (hi := (16533/100000 : ℝ)) (c := (3509492796451199963/3510000000000000000 : ℝ)) (alpha := (120836802757/157950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3509492796451199963/3510000000000000000 : ℝ)*(X 0 1+X 2 1)+(120836802757/157950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4719/1024 : ℝ)) (lo := (2043/20000 : ℝ)) (hi := (16533/100000 : ℝ)) (c := (3509492796451199963/3510000000000000000 : ℝ)) (alpha := (120836802757/157950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3509492796451199963/3510000000000000000 : ℝ)*(X 0 2+X 1 2)+(120836802757/157950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4719/1024 : ℝ)) (lo := (2043/20000 : ℝ)) (hi := (16533/100000 : ℝ)) (c := (3509492796451199963/3510000000000000000 : ℝ)) (alpha := (120836802757/157950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-215881387/1250000000 : ℝ)*X 0 0+(5462965189/10000000000 : ℝ)*X 0 1+(5179249607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355023247/10000000000 : ℝ)*X 1 0+(-374686067/2000000000 : ℝ)*X 1 1+(5179249481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355023769/10000000000 : ℝ)*X 2 0+(5179249037/10000000000 : ℝ)*X 2 1+(-74937209/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2109965899/5000000000 : ℝ)*X 0 0+(3886442937/10000000000 : ℝ)*X 0 1+(4575375419/10000000000 : ℝ)*X 0 2+(2109965899/5000000000 : ℝ)*X 1 0+(3886442937/10000000000 : ℝ)*X 1 1+(4575375419/10000000000 : ℝ)*X 1 2+(2109965899/5000000000 : ℝ)*X 2 0+(3886442937/10000000000 : ℝ)*X 2 1+(4575375419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-431781027/2500000000 : ℝ)*X 0 0+(518135961/1000000000 : ℝ)*X 0 1+(1365208199/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279801621/10000000000 : ℝ)*X 1 0+(-1591846891/10000000000 : ℝ)*X 1 1+(218433309/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((527980159/1000000000 : ℝ)*X 2 0+(2730416407/5000000000 : ℝ)*X 2 1+(-198980851/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4220108289/10000000000 : ℝ)*X 0 0+(4570251119/10000000000 : ℝ)*X 0 1+(1945810851/5000000000 : ℝ)*X 0 2+(4220108289/10000000000 : ℝ)*X 1 0+(4570251119/10000000000 : ℝ)*X 1 1+(1945810851/5000000000 : ℝ)*X 1 2+(4220108289/10000000000 : ℝ)*X 2 0+(4570251119/10000000000 : ℝ)*X 2 1+(1945810851/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45694639944102174354043943/5484375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4158427/312500000000 : ℝ)*(base19) + (1307562219/100000000000000 : ℝ)*(base23) + (196376857/100000000000000 : ℝ)*(lower2) + (1749167/781250000000 : ℝ)*(upper3) + (5520599/6250000000000 : ℝ)*(upper5) + (77753385811263/3125000000000 : ℝ)*(major0) + (77753385811263/3125000000000 : ℝ)*(major1) + (77753385811263/3125000000000 : ℝ)*(major2) + (352466852914279/10000000000000 : ℝ)*(sp0) + (881170112942191/25000000000000 : ℝ)*(sp1) + (1762340237451593/50000000000000 : ℝ)*(sp2) + (725763273430323/50000000000000 : ℝ)*(sp3) + (6626661307/50000000000000 : ℝ)*(sp4) + (1010608571/12500000000000 : ℝ)*(sp7) + (725767315864607/50000000000000 : ℝ)*(f.failure) + (881170445616351/25000000000000 : ℝ)*(f.sum) + (4153902861247/1316250000000000000000000000 : ℝ)*base65 + (68513733258600193/32906250000000000000000000000000 : ℝ)*base68 + (108653090934524807/32906250000000000000000000000000 : ℝ)*base69 + (335348107614149807/32906250000000000000000000000000 : ℝ)*base71 + (4552544999101/2632500000000000000000000000 : ℝ)*base74 + (115931381194537693/32906250000000000000000000000000 : ℝ)*base76 + (153857919917962307/32906250000000000000000000000000 : ℝ)*base77 + (112497821250899807/32906250000000000000000000000000 : ℝ)*base79 + (436886503319/164531250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (14194483/2500000000000000000000 : ℝ)*base90 + (14194483/2500000000000000000000 : ℝ)*base92 + (14194483/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (561515423888130735674890873/87750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (425835831/50000000000000 : ℝ)*(base19) + (499141943/50000000000000 : ℝ)*(base23) + (112605001/100000000000000 : ℝ)*(upper3) + (34783147/50000000000000 : ℝ)*(lower4) + (115688157/100000000000000 : ℝ)*(upper5) + (1262929530041619/50000000000000 : ℝ)*(major0) + (1262929530041619/50000000000000 : ℝ)*(major1) + (1262929530041619/50000000000000 : ℝ)*(major2) + (8827871759/100000000000000 : ℝ)*(sp1) + (5672464753/50000000000000 : ℝ)*(sp2) + (894539982491679/25000000000000 : ℝ)*(sp4) + (3494287353929/97656250000 : ℝ)*(sp5) + (894536896688331/25000000000000 : ℝ)*(sp6) + (368389494224637/25000000000000 : ℝ)*(sp7) + (368389494224637/25000000000000 : ℝ)*(f.failure) + (894539982491679/25000000000000 : ℝ)*(f.sum) + (1605441217799/329062500000000000000000000 : ℝ)*base65 + (1919719500042019709/526500000000000000000000000000000 : ℝ)*base68 + (2658552032532019709/526500000000000000000000000000000 : ℝ)*base70 + (1995373700800519709/526500000000000000000000000000000 : ℝ)*base72 + (11635568164471/5265000000000000000000000000 : ℝ)*base74 + (7983178548721519709/526500000000000000000000000000000 : ℝ)*base76 + (2056273421403019709/526500000000000000000000000000000 : ℝ)*base78 + (2593333444539019709/526500000000000000000000000000000 : ℝ)*base80 + (10943490196433/2632500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (7149447/1250000000000000000000 : ℝ)*base89 + (7149447/1250000000000000000000 : ℝ)*base91 + (7149447/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1601_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85706131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16533/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2043/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (259/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1601_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1601_s4_0 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1727194429/10000000000 : ℝ)*x 0 + (5462249599/10000000000 : ℝ)*x 1 + (258993503/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1727194429/10000000000 : ℝ)^4723 ≤ (10622168803787/100000000000000 : ℝ)^3699 := by
    have hnat : (1727194429 : ℕ)^4723*100000000000000^3699 ≤ 10622168803787^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727194429 10000000000 10622168803787 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462249599/10000000000 : ℝ)^4723 ≤ (46202735713289/100000000000000 : ℝ)^3699 := by
    have hnat : (5462249599 : ℕ)^4723*100000000000000^3699 ≤ 46202735713289^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462249599 10000000000 46202735713289 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258993503/500000000 : ℝ)^4723 ≤ (21587547736291/50000000000000 : ℝ)^3699 := by
    have hnat : (258993503 : ℕ)^4723*50000000000000^3699 ≤ 21587547736291^3699*500000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258993503 500000000 21587547736291 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1727194429/10000000000 : ℝ), (5462249599/10000000000 : ℝ), (258993503/500000000 : ℝ)] ![(10622168803787/100000000000000 : ℝ), (46202735713289/100000000000000 : ℝ), (21587547736291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1727194429/10000000000 : ℝ)|^4723 ≤ (10622168803787/100000000000000 : ℝ)^3699
        have hw : |(-1727194429/10000000000 : ℝ)|=(1727194429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462249599/10000000000 : ℝ)|^4723 ≤ (46202735713289/100000000000000 : ℝ)^3699
        have hw : |(5462249599/10000000000 : ℝ)|=(5462249599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258993503/500000000 : ℝ)|^4723 ≤ (21587547736291/50000000000000 : ℝ)^3699
        have hw : |(258993503/500000000 : ℝ)|=(258993503/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s4_1 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669354099/1250000000 : ℝ)*x 0 + (-117053917/625000000 : ℝ)*x 1 + (5179870059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669354099/1250000000 : ℝ)^4723 ≤ (5630723883961/12500000000000 : ℝ)^3699 := by
    have hnat : (669354099 : ℕ)^4723*12500000000000^3699 ≤ 5630723883961^3699*1250000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669354099 1250000000 5630723883961 12500000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (117053917/625000000 : ℝ)^4723 ≤ (11779113455001/100000000000000 : ℝ)^3699 := by
    have hnat : (117053917 : ℕ)^4723*100000000000000^3699 ≤ 11779113455001^3699*625000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117053917 625000000 11779113455001 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179870059/10000000000 : ℝ)^4723 ≤ (43175095461939/100000000000000 : ℝ)^3699 := by
    have hnat : (5179870059 : ℕ)^4723*100000000000000^3699 ≤ 43175095461939^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179870059 10000000000 43175095461939 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669354099/1250000000 : ℝ), (-117053917/625000000 : ℝ), (5179870059/10000000000 : ℝ)] ![(5630723883961/12500000000000 : ℝ), (11779113455001/100000000000000 : ℝ), (43175095461939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669354099/1250000000 : ℝ)|^4723 ≤ (5630723883961/12500000000000 : ℝ)^3699
        have hw : |(669354099/1250000000 : ℝ)|=(669354099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-117053917/625000000 : ℝ)|^4723 ≤ (11779113455001/100000000000000 : ℝ)^3699
        have hw : |(-117053917/625000000 : ℝ)|=(117053917/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179870059/10000000000 : ℝ)|^4723 ≤ (43175095461939/100000000000000 : ℝ)^3699
        have hw : |(5179870059/10000000000 : ℝ)|=(5179870059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s4_2 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354832791/10000000000 : ℝ)*x 0 + (5179870059/10000000000 : ℝ)*x 1 + (-117053917/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354832791/10000000000 : ℝ)^4723 ≤ (45045791060947/100000000000000 : ℝ)^3699 := by
    have hnat : (5354832791 : ℕ)^4723*100000000000000^3699 ≤ 45045791060947^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354832791 10000000000 45045791060947 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179870059/10000000000 : ℝ)^4723 ≤ (43175095461939/100000000000000 : ℝ)^3699 := by
    have hnat : (5179870059 : ℕ)^4723*100000000000000^3699 ≤ 43175095461939^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179870059 10000000000 43175095461939 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117053917/625000000 : ℝ)^4723 ≤ (11779113455001/100000000000000 : ℝ)^3699 := by
    have hnat : (117053917 : ℕ)^4723*100000000000000^3699 ≤ 11779113455001^3699*625000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117053917 625000000 11779113455001 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354832791/10000000000 : ℝ), (5179870059/10000000000 : ℝ), (-117053917/625000000 : ℝ)] ![(45045791060947/100000000000000 : ℝ), (43175095461939/100000000000000 : ℝ), (11779113455001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354832791/10000000000 : ℝ)|^4723 ≤ (45045791060947/100000000000000 : ℝ)^3699
        have hw : |(5354832791/10000000000 : ℝ)|=(5354832791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179870059/10000000000 : ℝ)|^4723 ≤ (43175095461939/100000000000000 : ℝ)^3699
        have hw : |(5179870059/10000000000 : ℝ)|=(5179870059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-117053917/625000000 : ℝ)|^4723 ≤ (11779113455001/100000000000000 : ℝ)^3699
        have hw : |(-117053917/625000000 : ℝ)|=(117053917/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s4_3 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2110012271/5000000000 : ℝ)*x 0 + (3888055987/10000000000 : ℝ)*x 1 + (114343569/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110012271/5000000000 : ℝ)^4723 ≤ (33234590432387/100000000000000 : ℝ)^3699 := by
    have hnat : (2110012271 : ℕ)^4723*100000000000000^3699 ≤ 33234590432387^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110012271 5000000000 33234590432387 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3888055987/10000000000 : ℝ)^4723 ≤ (1496675048569/5000000000000 : ℝ)^3699 := by
    have hnat : (3888055987 : ℕ)^4723*5000000000000^3699 ≤ 1496675048569^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3888055987 10000000000 1496675048569 5000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114343569/250000000 : ℝ)^4723 ≤ (7366381715947/20000000000000 : ℝ)^3699 := by
    have hnat : (114343569 : ℕ)^4723*20000000000000^3699 ≤ 7366381715947^3699*250000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114343569 250000000 7366381715947 20000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2110012271/5000000000 : ℝ), (3888055987/10000000000 : ℝ), (114343569/250000000 : ℝ)] ![(33234590432387/100000000000000 : ℝ), (1496675048569/5000000000000 : ℝ), (7366381715947/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2110012271/5000000000 : ℝ)|^4723 ≤ (33234590432387/100000000000000 : ℝ)^3699
        have hw : |(2110012271/5000000000 : ℝ)|=(2110012271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3888055987/10000000000 : ℝ)|^4723 ≤ (1496675048569/5000000000000 : ℝ)^3699
        have hw : |(3888055987/10000000000 : ℝ)|=(3888055987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(114343569/250000000 : ℝ)|^4723 ≤ (7366381715947/20000000000000 : ℝ)^3699
        have hw : |(114343569/250000000 : ℝ)|=(114343569/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s4_4 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1727266249/10000000000 : ℝ)*x 0 + (2590980301/5000000000 : ℝ)*x 1 + (1092027421/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1727266249/10000000000 : ℝ)^4723 ≤ (5311366385259/50000000000000 : ℝ)^3699 := by
    have hnat : (1727266249 : ℕ)^4723*50000000000000^3699 ≤ 5311366385259^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727266249 10000000000 5311366385259 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590980301/5000000000 : ℝ)^4723 ≤ (337479261983/781250000000 : ℝ)^3699 := by
    have hnat : (2590980301 : ℕ)^4723*781250000000^3699 ≤ 337479261983^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590980301 5000000000 337479261983 781250000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092027421/2000000000 : ℝ)^4723 ≤ (1154498042097/2500000000000 : ℝ)^3699 := by
    have hnat : (1092027421 : ℕ)^4723*2500000000000^3699 ≤ 1154498042097^3699*2000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092027421 2000000000 1154498042097 2500000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1727266249/10000000000 : ℝ), (2590980301/5000000000 : ℝ), (1092027421/2000000000 : ℝ)] ![(5311366385259/50000000000000 : ℝ), (337479261983/781250000000 : ℝ), (1154498042097/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1727266249/10000000000 : ℝ)|^4723 ≤ (5311366385259/50000000000000 : ℝ)^3699
        have hw : |(-1727266249/10000000000 : ℝ)|=(1727266249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590980301/5000000000 : ℝ)|^4723 ≤ (337479261983/781250000000 : ℝ)^3699
        have hw : |(2590980301/5000000000 : ℝ)|=(2590980301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092027421/2000000000 : ℝ)|^4723 ≤ (1154498042097/2500000000000 : ℝ)^3699
        have hw : |(1092027421/2000000000 : ℝ)|=(1092027421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s4_5 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279966479/10000000000 : ℝ)*x 0 + (-796297809/5000000000 : ℝ)*x 1 + (1092027419/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279966479/10000000000 : ℝ)^4723 ≤ (44243218622687/100000000000000 : ℝ)^3699 := by
    have hnat : (5279966479 : ℕ)^4723*100000000000000^3699 ≤ 44243218622687^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279966479 10000000000 44243218622687 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (796297809/5000000000 : ℝ)^4723 ≤ (9576859785849/100000000000000 : ℝ)^3699 := by
    have hnat : (796297809 : ℕ)^4723*100000000000000^3699 ≤ 9576859785849^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796297809 5000000000 9576859785849 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092027419/2000000000 : ℝ)^4723 ≤ (46179921575891/100000000000000 : ℝ)^3699 := by
    have hnat : (1092027419 : ℕ)^4723*100000000000000^3699 ≤ 46179921575891^3699*2000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092027419 2000000000 46179921575891 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279966479/10000000000 : ℝ), (-796297809/5000000000 : ℝ), (1092027419/2000000000 : ℝ)] ![(44243218622687/100000000000000 : ℝ), (9576859785849/100000000000000 : ℝ), (46179921575891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279966479/10000000000 : ℝ)|^4723 ≤ (44243218622687/100000000000000 : ℝ)^3699
        have hw : |(5279966479/10000000000 : ℝ)|=(5279966479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-796297809/5000000000 : ℝ)|^4723 ≤ (9576859785849/100000000000000 : ℝ)^3699
        have hw : |(-796297809/5000000000 : ℝ)|=(796297809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092027419/2000000000 : ℝ)|^4723 ≤ (46179921575891/100000000000000 : ℝ)^3699
        have hw : |(1092027419/2000000000 : ℝ)|=(1092027419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s4_6 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279966471/10000000000 : ℝ)*x 0 + (2730068549/5000000000 : ℝ)*x 1 + (-2548153/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279966471/10000000000 : ℝ)^4723 ≤ (22121609268547/50000000000000 : ℝ)^3699 := by
    have hnat : (5279966471 : ℕ)^4723*50000000000000^3699 ≤ 22121609268547^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279966471 10000000000 22121609268547 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730068549/5000000000 : ℝ)^4723 ≤ (1443122550259/3125000000000 : ℝ)^3699 := by
    have hnat : (2730068549 : ℕ)^4723*3125000000000^3699 ≤ 1443122550259^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730068549 5000000000 1443122550259 3125000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2548153/16000000 : ℝ)^4723 ≤ (1915371967919/20000000000000 : ℝ)^3699 := by
    have hnat : (2548153 : ℕ)^4723*20000000000000^3699 ≤ 1915371967919^3699*16000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548153 16000000 1915371967919 20000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279966471/10000000000 : ℝ), (2730068549/5000000000 : ℝ), (-2548153/16000000 : ℝ)] ![(22121609268547/50000000000000 : ℝ), (1443122550259/3125000000000 : ℝ), (1915371967919/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279966471/10000000000 : ℝ)|^4723 ≤ (22121609268547/50000000000000 : ℝ)^3699
        have hw : |(5279966471/10000000000 : ℝ)|=(5279966471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730068549/5000000000 : ℝ)|^4723 ≤ (1443122550259/3125000000000 : ℝ)^3699
        have hw : |(2730068549/5000000000 : ℝ)|=(2730068549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2548153/16000000 : ℝ)|^4723 ≤ (1915371967919/20000000000000 : ℝ)^3699
        have hw : |(-2548153/16000000 : ℝ)|=(2548153/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s4_7 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527524867/1250000000 : ℝ)*x 0 + (4568666411/10000000000 : ℝ)*x 1 + (3893185649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527524867/1250000000 : ℝ)^4723 ≤ (33236344082679/100000000000000 : ℝ)^3699 := by
    have hnat : (527524867 : ℕ)^4723*100000000000000^3699 ≤ 33236344082679^3699*1250000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527524867 1250000000 33236344082679 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4568666411/10000000000 : ℝ)^4723 ≤ (36779720558131/100000000000000 : ℝ)^3699 := by
    have hnat : (4568666411 : ℕ)^4723*100000000000000^3699 ≤ 36779720558131^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4568666411 10000000000 36779720558131 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3893185649/10000000000 : ℝ)^4723 ≤ (29983935346633/100000000000000 : ℝ)^3699 := by
    have hnat : (3893185649 : ℕ)^4723*100000000000000^3699 ≤ 29983935346633^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3893185649 10000000000 29983935346633 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527524867/1250000000 : ℝ), (4568666411/10000000000 : ℝ), (3893185649/10000000000 : ℝ)] ![(33236344082679/100000000000000 : ℝ), (36779720558131/100000000000000 : ℝ), (29983935346633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527524867/1250000000 : ℝ)|^4723 ≤ (33236344082679/100000000000000 : ℝ)^3699
        have hw : |(527524867/1250000000 : ℝ)|=(527524867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4568666411/10000000000 : ℝ)|^4723 ≤ (36779720558131/100000000000000 : ℝ)^3699
        have hw : |(4568666411/10000000000 : ℝ)|=(4568666411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3893185649/10000000000 : ℝ)|^4723 ≤ (29983935346633/100000000000000 : ℝ)^3699
        have hw : |(3893185649/10000000000 : ℝ)|=(3893185649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1601_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85706131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (259/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (10373/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16357/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4093/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (259/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4093/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (259/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4093/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (259/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4093/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (259/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4093/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (259/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4093/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (259/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (259/2500 : ℝ) ^ (4719/1024 : ℝ) ≤ (1449958057343823/50000000000000000000 : ℝ) := by
    have hpowers : (259/2500 : ℝ)^4719 ≤ (1449958057343823/50000000000000000000 : ℝ)^1024 := by
      have hnat : (259 : ℕ)^4719*50000000000000000000^1024 ≤ 1449958057343823^1024*2500^4719 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        259 2500 1449958057343823 50000000000000000000 4719 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (259/2500 : ℝ)) (X := (1449958057343823/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4093/25000 : ℝ) ^ (4719/1024 : ℝ) ≤ (23892834124422519/100000000000000000000 : ℝ) := by
    have hpowers : (4093/25000 : ℝ)^4719 ≤ (23892834124422519/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4093 : ℕ)^4719*100000000000000000000^1024 ≤ 23892834124422519^1024*25000^4719 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4093 25000 23892834124422519 100000000000000000000 4719 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4093/25000 : ℝ)) (X := (23892834124422519/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001449958057343823/25000000000000000000 : ℝ) ≤ (10000125850674997/10000000000000000 : ℝ) ^ (4719/1024 : ℝ) := by
    have hpowers : (25001449958057343823/25000000000000000000 : ℝ)^1024 ≤ (10000125850674997/10000000000000000 : ℝ)^4719 := by
      have hnat : (25001449958057343823 : ℕ)^1024*10000000000000000^4719 ≤ 10000125850674997^4719*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001449958057343823 25000000000000000000 10000125850674997 10000000000000000 1024 4719 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000125850674997/10000000000000000 : ℝ)) (X := (25001449958057343823/25000000000000000000 : ℝ)) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005358550047822033/20000000000000000000 : ℝ) ≤ (5000290664323451/5000000000000000 : ℝ) ^ (4719/1024 : ℝ) := by
    have hpowers : (20005358550047822033/20000000000000000000 : ℝ)^1024 ≤ (5000290664323451/5000000000000000 : ℝ)^4719 := by
      have hnat : (20005358550047822033 : ℕ)^1024*5000000000000000^4719 ≤ 5000290664323451^4719*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005358550047822033 20000000000000000000 5000290664323451 5000000000000000 1024 4719 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000290664323451/5000000000000000 : ℝ)) (X := (20005358550047822033/20000000000000000000 : ℝ)) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023892834124422519/50000000000000000000 : ℝ) ≤ (10001036806618807/10000000000000000 : ℝ) ^ (4719/1024 : ℝ) := by
    have hpowers : (50023892834124422519/50000000000000000000 : ℝ)^1024 ≤ (10001036806618807/10000000000000000 : ℝ)^4719 := by
      have hnat : (50023892834124422519 : ℕ)^1024*10000000000000000^4719 ≤ 10001036806618807^4719*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023892834124422519 50000000000000000000 10001036806618807 10000000000000000 1024 4719 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001036806618807/10000000000000000 : ℝ)) (X := (50023892834124422519/50000000000000000000 : ℝ)) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1449958057343823/50000000000000000000 : ℝ) ≤ ((1669758864185561399/1670000000000000000 : ℝ)+2*(10121732709/13360000000000 : ℝ)*(259/2500 : ℝ))^(4719/1024 : ℝ) := by
    rw [show (1669758864185561399/1670000000000000000 : ℝ)+2*(10121732709/13360000000000 : ℝ)*(259/2500 : ℝ)=(10000125850674997/10000000000000000 : ℝ) by norm_num, show 1+2*(1449958057343823/50000000000000000000 : ℝ)=(25001449958057343823/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23892834124422519/100000000000000000000 : ℝ)+(1449958057343823/50000000000000000000 : ℝ) ≤ ((1669758864185561399/1670000000000000000 : ℝ)+(10121732709/13360000000000 : ℝ)*((4093/25000 : ℝ)+(259/2500 : ℝ)))^(4719/1024 : ℝ) := by
    rw [show (1669758864185561399/1670000000000000000 : ℝ)+(10121732709/13360000000000 : ℝ)*((4093/25000 : ℝ)+(259/2500 : ℝ))=(5000290664323451/5000000000000000 : ℝ) by norm_num, show 1+(23892834124422519/100000000000000000000 : ℝ)+(1449958057343823/50000000000000000000 : ℝ)=(20005358550047822033/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23892834124422519/100000000000000000000 : ℝ) ≤ ((1669758864185561399/1670000000000000000 : ℝ)+2*(10121732709/13360000000000 : ℝ)*(4093/25000 : ℝ))^(4719/1024 : ℝ) := by
    rw [show (1669758864185561399/1670000000000000000 : ℝ)+2*(10121732709/13360000000000 : ℝ)*(4093/25000 : ℝ)=(10001036806618807/10000000000000000 : ℝ) by norm_num, show 1+2*(23892834124422519/100000000000000000000 : ℝ)=(50023892834124422519/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1669758864185561399/1670000000000000000 : ℝ)*(X 1 0+X 2 0)+(10121732709/13360000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4719/1024 : ℝ)) (lo := (259/2500 : ℝ)) (hi := (4093/25000 : ℝ)) (c := (1669758864185561399/1670000000000000000 : ℝ)) (alpha := (10121732709/13360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1669758864185561399/1670000000000000000 : ℝ)*(X 0 1+X 2 1)+(10121732709/13360000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4719/1024 : ℝ)) (lo := (259/2500 : ℝ)) (hi := (4093/25000 : ℝ)) (c := (1669758864185561399/1670000000000000000 : ℝ)) (alpha := (10121732709/13360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1669758864185561399/1670000000000000000 : ℝ)*(X 0 2+X 1 2)+(10121732709/13360000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4719/1024 : ℝ)) (lo := (259/2500 : ℝ)) (hi := (4093/25000 : ℝ)) (c := (1669758864185561399/1670000000000000000 : ℝ)) (alpha := (10121732709/13360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1727194429/10000000000 : ℝ)*X 0 0+(5462249599/10000000000 : ℝ)*X 0 1+(258993503/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669354099/1250000000 : ℝ)*X 1 0+(-117053917/625000000 : ℝ)*X 1 1+(5179870059/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354832791/10000000000 : ℝ)*X 2 0+(5179870059/10000000000 : ℝ)*X 2 1+(-117053917/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2110012271/5000000000 : ℝ)*X 0 0+(3888055987/10000000000 : ℝ)*X 0 1+(114343569/250000000 : ℝ)*X 0 2+(2110012271/5000000000 : ℝ)*X 1 0+(3888055987/10000000000 : ℝ)*X 1 1+(114343569/250000000 : ℝ)*X 1 2+(2110012271/5000000000 : ℝ)*X 2 0+(3888055987/10000000000 : ℝ)*X 2 1+(114343569/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1727266249/10000000000 : ℝ)*X 0 0+(2590980301/5000000000 : ℝ)*X 0 1+(1092027421/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279966479/10000000000 : ℝ)*X 1 0+(-796297809/5000000000 : ℝ)*X 1 1+(1092027419/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5279966471/10000000000 : ℝ)*X 2 0+(2730068549/5000000000 : ℝ)*X 2 1+(-2548153/16000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((527524867/1250000000 : ℝ)*X 0 0+(4568666411/10000000000 : ℝ)*X 0 1+(3893185649/10000000000 : ℝ)*X 0 2+(527524867/1250000000 : ℝ)*X 1 0+(4568666411/10000000000 : ℝ)*X 1 1+(3893185649/10000000000 : ℝ)*X 1 2+(527524867/1250000000 : ℝ)*X 2 0+(4568666411/10000000000 : ℝ)*X 2 1+(3893185649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1012223530251648807915099639/83500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2020901613/100000000000000 : ℝ)*(base19) + (1889734209/100000000000000 : ℝ)*(base23) + (34941907/50000000000000 : ℝ)*(lower2) + (301132419/100000000000000 : ℝ)*(upper3) + (40962533/20000000000000 : ℝ)*(upper5) + (624974300958397/25000000000000 : ℝ)*(major0) + (624974300958397/25000000000000 : ℝ)*(major1) + (2499897203833589/100000000000000 : ℝ)*(major2) + (177067894236733/5000000000000 : ℝ)*(sp0) + (354137986288299/10000000000000 : ℝ)*(sp1) + (1770689997025197/50000000000000 : ℝ)*(sp2) + (1458401380734093/100000000000000 : ℝ)*(sp3) + (11999524971/50000000000000 : ℝ)*(sp4) + (429562689/4000000000000 : ℝ)*(sp7) + (729206059900659/50000000000000 : ℝ)*(f.failure) + (3541381883784603/100000000000000 : ℝ)*(f.sum) + (83591758999/267200000000000000000000000 : ℝ)*base66 + (965181847533541/250000000000000000000000000000 : ℝ)*base68 + (690985046769531011/167000000000000000000000000000000 : ℝ)*base69 + (2428796946533541/250000000000000000000000000000 : ℝ)*base72 + (168506891197/1336000000000000000000000000 : ℝ)*base73 + (1378888290469531011/167000000000000000000000000000000 : ℝ)*base75 + (246718514932757597/41750000000000000000000000000000 : ℝ)*base78 + (342570037503757597/41750000000000000000000000000000 : ℝ)*base80 + (214199945997/83500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (27240329/2500000000000000000000 : ℝ)*base89 + (27240329/2500000000000000000000 : ℝ)*base91 + (2240329/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2553517930815504055403271/500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (809629523/100000000000000 : ℝ)*(base19) + (867222047/100000000000000 : ℝ)*(base23) + (257699723/100000000000000 : ℝ)*(lower1) + (13283269/12500000000000 : ℝ)*(upper3) + (3637557/12500000000000 : ℝ)*(lower4) + (105714861/100000000000000 : ℝ)*(upper5) + (2537626760360673/100000000000000 : ℝ)*(major0) + (2537626760360673/100000000000000 : ℝ)*(major1) + (2537626760360673/100000000000000 : ℝ)*(major2) + (2183093/390625000000 : ℝ)*(sp2) + (3594830228621309/100000000000000 : ℝ)*(sp4) + (1797414709495893/50000000000000 : ℝ)*(sp5) + (1797414401263727/50000000000000 : ℝ)*(sp6) + (740211560932751/50000000000000 : ℝ)*(sp7) + (740211560932751/50000000000000 : ℝ)*(f.failure) + (3594830228621309/100000000000000 : ℝ)*(f.sum) + (14063349753/4000000000000000000000000 : ℝ)*base66 + (3293567913719081/1000000000000000000000000000000 : ℝ)*base67 + (9155938010719081/1000000000000000000000000000000 : ℝ)*base69 + (4942041887719081/1000000000000000000000000000000 : ℝ)*base71 + (197809427/160000000000000000000000 : ℝ)*base73 + (23181606785719081/1000000000000000000000000000000 : ℝ)*base75 + (377532419719081/1000000000000000000000000000000 : ℝ)*base77 + (6481950767719081/1000000000000000000000000000000 : ℝ)*base79 + (19385309683/4000000000000000000000000 : ℝ)*base81 + (14396381/2500000000000000000000 : ℝ)*base89 + (14396381/2500000000000000000000 : ℝ)*base91 + (14396381/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1601_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85706131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (259/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10373/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16357/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1601_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1601_s5_0 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-26987623/156250000 : ℝ)*x 0 + (1365546313/2500000000 : ℝ)*x 1 + (5179925441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26987623/156250000 : ℝ)^4723 ≤ (2124454872897/20000000000000 : ℝ)^3699 := by
    have hnat : (26987623 : ℕ)^4723*20000000000000^3699 ≤ 2124454872897^3699*156250000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26987623 156250000 2124454872897 20000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365546313/2500000000 : ℝ)^4723 ≤ (46202040757207/100000000000000 : ℝ)^3699 := by
    have hnat : (1365546313 : ℕ)^4723*100000000000000^3699 ≤ 46202040757207^3699*2500000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365546313 2500000000 46202040757207 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179925441/10000000000 : ℝ)^4723 ≤ (43175684871713/100000000000000 : ℝ)^3699 := by
    have hnat : (5179925441 : ℕ)^4723*100000000000000^3699 ≤ 43175684871713^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179925441 10000000000 43175684871713 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-26987623/156250000 : ℝ), (1365546313/2500000000 : ℝ), (5179925441/10000000000 : ℝ)] ![(2124454872897/20000000000000 : ℝ), (46202040757207/100000000000000 : ℝ), (43175684871713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-26987623/156250000 : ℝ)|^4723 ≤ (2124454872897/20000000000000 : ℝ)^3699
        have hw : |(-26987623/156250000 : ℝ)|=(26987623/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1365546313/2500000000 : ℝ)|^4723 ≤ (46202040757207/100000000000000 : ℝ)^3699
        have hw : |(1365546313/2500000000 : ℝ)|=(1365546313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179925441/10000000000 : ℝ)|^4723 ≤ (43175684871713/100000000000000 : ℝ)^3699
        have hw : |(5179925441/10000000000 : ℝ)|=(5179925441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s5_1 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677407799/5000000000 : ℝ)*x 0 + (-58525397/312500000 : ℝ)*x 1 + (1294981279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677407799/5000000000 : ℝ)^4723 ≤ (22522803196103/50000000000000 : ℝ)^3699 := by
    have hnat : (2677407799 : ℕ)^4723*50000000000000^3699 ≤ 22522803196103^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677407799 5000000000 22522803196103 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58525397/312500000 : ℝ)^4723 ≤ (2355742438117/20000000000000 : ℝ)^3699 := by
    have hnat : (58525397 : ℕ)^4723*20000000000000^3699 ≤ 2355742438117^3699*312500000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58525397 312500000 2355742438117 20000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294981279/2500000000 : ℝ)^4723 ≤ (8635136282571/20000000000000 : ℝ)^3699 := by
    have hnat : (1294981279 : ℕ)^4723*20000000000000^3699 ≤ 8635136282571^3699*2500000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294981279 2500000000 8635136282571 20000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677407799/5000000000 : ℝ), (-58525397/312500000 : ℝ), (1294981279/2500000000 : ℝ)] ![(22522803196103/50000000000000 : ℝ), (2355742438117/20000000000000 : ℝ), (8635136282571/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677407799/5000000000 : ℝ)|^4723 ≤ (22522803196103/50000000000000 : ℝ)^3699
        have hw : |(2677407799/5000000000 : ℝ)|=(2677407799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-58525397/312500000 : ℝ)|^4723 ≤ (2355742438117/20000000000000 : ℝ)^3699
        have hw : |(-58525397/312500000 : ℝ)|=(58525397/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294981279/2500000000 : ℝ)|^4723 ≤ (8635136282571/20000000000000 : ℝ)^3699
        have hw : |(1294981279/2500000000 : ℝ)|=(1294981279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s5_2 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354815349/10000000000 : ℝ)*x 0 + (1035985061/2000000000 : ℝ)*x 1 + (-936406393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354815349/10000000000 : ℝ)^4723 ≤ (45045603717717/100000000000000 : ℝ)^3699 := by
    have hnat : (5354815349 : ℕ)^4723*100000000000000^3699 ≤ 45045603717717^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354815349 10000000000 45045603717717 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035985061/2000000000 : ℝ)^4723 ≤ (21587841712157/50000000000000 : ℝ)^3699 := by
    have hnat : (1035985061 : ℕ)^4723*50000000000000^3699 ≤ 21587841712157^3699*2000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035985061 2000000000 21587841712157 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (936406393/5000000000 : ℝ)^4723 ≤ (11778712849077/100000000000000 : ℝ)^3699 := by
    have hnat : (936406393 : ℕ)^4723*100000000000000^3699 ≤ 11778712849077^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936406393 5000000000 11778712849077 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354815349/10000000000 : ℝ), (1035985061/2000000000 : ℝ), (-936406393/5000000000 : ℝ)] ![(45045603717717/100000000000000 : ℝ), (21587841712157/50000000000000 : ℝ), (11778712849077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354815349/10000000000 : ℝ)|^4723 ≤ (45045603717717/100000000000000 : ℝ)^3699
        have hw : |(5354815349/10000000000 : ℝ)|=(5354815349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035985061/2000000000 : ℝ)|^4723 ≤ (21587841712157/50000000000000 : ℝ)^3699
        have hw : |(1035985061/2000000000 : ℝ)|=(1035985061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-936406393/5000000000 : ℝ)|^4723 ≤ (11778712849077/100000000000000 : ℝ)^3699
        have hw : |(-936406393/5000000000 : ℝ)|=(936406393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s5_3 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055008197/2500000000 : ℝ)*x 0 + (1944099977/5000000000 : ℝ)*x 1 + (2286798529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055008197/2500000000 : ℝ)^4723 ≤ (16617336675537/50000000000000 : ℝ)^3699 := by
    have hnat : (1055008197 : ℕ)^4723*50000000000000^3699 ≤ 16617336675537^3699*2500000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055008197 2500000000 16617336675537 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1944099977/5000000000 : ℝ)^4723 ≤ (1870932261929/6250000000000 : ℝ)^3699 := by
    have hnat : (1944099977 : ℕ)^4723*6250000000000^3699 ≤ 1870932261929^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944099977 5000000000 1870932261929 6250000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2286798529/5000000000 : ℝ)^4723 ≤ (36830410449043/100000000000000 : ℝ)^3699 := by
    have hnat : (2286798529 : ℕ)^4723*100000000000000^3699 ≤ 36830410449043^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286798529 5000000000 36830410449043 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055008197/2500000000 : ℝ), (1944099977/5000000000 : ℝ), (2286798529/5000000000 : ℝ)] ![(16617336675537/50000000000000 : ℝ), (1870932261929/6250000000000 : ℝ), (36830410449043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055008197/2500000000 : ℝ)|^4723 ≤ (16617336675537/50000000000000 : ℝ)^3699
        have hw : |(1055008197/2500000000 : ℝ)|=(1055008197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1944099977/5000000000 : ℝ)|^4723 ≤ (1870932261929/6250000000000 : ℝ)^3699
        have hw : |(1944099977/5000000000 : ℝ)|=(1944099977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2286798529/5000000000 : ℝ)|^4723 ≤ (36830410449043/100000000000000 : ℝ)^3699
        have hw : |(2286798529/5000000000 : ℝ)|=(2286798529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s5_4 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1727279603/10000000000 : ℝ)*x 0 + (5182013791/10000000000 : ℝ)*x 1 + (5460074969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1727279603/10000000000 : ℝ)^4723 ≤ (663927352097/6250000000000 : ℝ)^3699 := by
    have hnat : (1727279603 : ℕ)^4723*6250000000000^3699 ≤ 663927352097^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727279603 10000000000 663927352097 6250000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182013791/10000000000 : ℝ)^4723 ≤ (43197911667527/100000000000000 : ℝ)^3699 := by
    have hnat : (5182013791 : ℕ)^4723*100000000000000^3699 ≤ 43197911667527^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182013791 10000000000 43197911667527 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460074969/10000000000 : ℝ)^4723 ≤ (46179250678711/100000000000000 : ℝ)^3699 := by
    have hnat : (5460074969 : ℕ)^4723*100000000000000^3699 ≤ 46179250678711^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460074969 10000000000 46179250678711 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1727279603/10000000000 : ℝ), (5182013791/10000000000 : ℝ), (5460074969/10000000000 : ℝ)] ![(663927352097/6250000000000 : ℝ), (43197911667527/100000000000000 : ℝ), (46179250678711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1727279603/10000000000 : ℝ)|^4723 ≤ (663927352097/6250000000000 : ℝ)^3699
        have hw : |(-1727279603/10000000000 : ℝ)|=(1727279603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182013791/10000000000 : ℝ)|^4723 ≤ (43197911667527/100000000000000 : ℝ)^3699
        have hw : |(5182013791/10000000000 : ℝ)|=(5182013791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5460074969/10000000000 : ℝ)|^4723 ≤ (46179250678711/100000000000000 : ℝ)^3699
        have hw : |(5460074969/10000000000 : ℝ)|=(5460074969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s5_5 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279981009/10000000000 : ℝ)*x 0 + (-398165799/2500000000 : ℝ)*x 1 + (5460074651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279981009/10000000000 : ℝ)^4723 ≤ (8848674816271/20000000000000 : ℝ)^3699 := by
    have hnat : (5279981009 : ℕ)^4723*20000000000000^3699 ≤ 8848674816271^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279981009 10000000000 8848674816271 20000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (398165799/2500000000 : ℝ)^4723 ≤ (9577378656507/100000000000000 : ℝ)^3699 := by
    have hnat : (398165799 : ℕ)^4723*100000000000000^3699 ≤ 9577378656507^3699*2500000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398165799 2500000000 9577378656507 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460074651/10000000000 : ℝ)^4723 ≤ (23089623622321/50000000000000 : ℝ)^3699 := by
    have hnat : (5460074651 : ℕ)^4723*50000000000000^3699 ≤ 23089623622321^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460074651 10000000000 23089623622321 50000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279981009/10000000000 : ℝ), (-398165799/2500000000 : ℝ), (5460074651/10000000000 : ℝ)] ![(8848674816271/20000000000000 : ℝ), (9577378656507/100000000000000 : ℝ), (23089623622321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279981009/10000000000 : ℝ)|^4723 ≤ (8848674816271/20000000000000 : ℝ)^3699
        have hw : |(5279981009/10000000000 : ℝ)|=(5279981009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-398165799/2500000000 : ℝ)|^4723 ≤ (9577378656507/100000000000000 : ℝ)^3699
        have hw : |(-398165799/2500000000 : ℝ)|=(398165799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5460074651/10000000000 : ℝ)|^4723 ≤ (23089623622321/50000000000000 : ℝ)^3699
        have hw : |(5460074651/10000000000 : ℝ)|=(5460074651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s5_6 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639990571/5000000000 : ℝ)*x 0 + (170627323/312500000 : ℝ)*x 1 + (-318532691/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639990571/5000000000 : ℝ)^4723 ≤ (44243375504343/100000000000000 : ℝ)^3699 := by
    have hnat : (2639990571 : ℕ)^4723*100000000000000^3699 ≤ 44243375504343^3699*5000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639990571 5000000000 44243375504343 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170627323/312500000 : ℝ)^4723 ≤ (4617924384297/10000000000000 : ℝ)^3699 := by
    have hnat : (170627323 : ℕ)^4723*10000000000000^3699 ≤ 4617924384297^3699*312500000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170627323 312500000 4617924384297 10000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318532691/2000000000 : ℝ)^4723 ≤ (9577380645147/100000000000000 : ℝ)^3699 := by
    have hnat : (318532691 : ℕ)^4723*100000000000000^3699 ≤ 9577380645147^3699*2000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318532691 2000000000 9577380645147 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639990571/5000000000 : ℝ), (170627323/312500000 : ℝ), (-318532691/2000000000 : ℝ)] ![(44243375504343/100000000000000 : ℝ), (4617924384297/10000000000000 : ℝ), (9577380645147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639990571/5000000000 : ℝ)|^4723 ≤ (44243375504343/100000000000000 : ℝ)^3699
        have hw : |(2639990571/5000000000 : ℝ)|=(2639990571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(170627323/312500000 : ℝ)|^4723 ≤ (4617924384297/10000000000000 : ℝ)^3699
        have hw : |(170627323/312500000 : ℝ)|=(170627323/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-318532691/2000000000 : ℝ)|^4723 ≤ (9577380645147/100000000000000 : ℝ)^3699
        have hw : |(-318532691/2000000000 : ℝ)|=(318532691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1601_s5_7 (p : ℝ) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4220207023/10000000000 : ℝ)*x 0 + (456852497/1000000000 : ℝ)*x 1 + (486665653/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4220207023/10000000000 : ℝ)^4723 ≤ (8309106350863/25000000000000 : ℝ)^3699 := by
    have hnat : (4220207023 : ℕ)^4723*25000000000000^3699 ≤ 8309106350863^3699*10000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220207023 10000000000 8309106350863 25000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456852497/1000000000 : ℝ)^4723 ≤ (36778266686547/100000000000000 : ℝ)^3699 := by
    have hnat : (456852497 : ℕ)^4723*100000000000000^3699 ≤ 36778266686547^3699*1000000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456852497 1000000000 36778266686547 100000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (486665653/1250000000 : ℝ)^4723 ≤ (5997061578537/20000000000000 : ℝ)^3699 := by
    have hnat : (486665653 : ℕ)^4723*20000000000000^3699 ≤ 5997061578537^3699*1250000000^4723 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486665653 1250000000 5997061578537 20000000000000 4723 3699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4723/1024 : ℝ)) 4723 3699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4220207023/10000000000 : ℝ), (456852497/1000000000 : ℝ), (486665653/1250000000 : ℝ)] ![(8309106350863/25000000000000 : ℝ), (36778266686547/100000000000000 : ℝ), (5997061578537/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4220207023/10000000000 : ℝ)|^4723 ≤ (8309106350863/25000000000000 : ℝ)^3699
        have hw : |(4220207023/10000000000 : ℝ)|=(4220207023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(456852497/1000000000 : ℝ)|^4723 ≤ (36778266686547/100000000000000 : ℝ)^3699
        have hw : |(456852497/1000000000 : ℝ)|=(456852497/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(486665653/1250000000 : ℝ)|^4723 ≤ (5997061578537/20000000000000 : ℝ)^3699
        have hw : |(486665653/1250000000 : ℝ)|=(486665653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1601_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85706131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16357/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (83/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4089/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16357/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10373/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16357/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10373/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16357/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10373/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16357/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10373/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16357/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10373/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16357/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10373/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10373/100000 : ℝ) ^ (4719/1024 : ℝ) ≤ (1458361790245269/50000000000000000000 : ℝ) := by
    have hpowers : (10373/100000 : ℝ)^4719 ≤ (1458361790245269/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10373 : ℕ)^4719*50000000000000000000^1024 ≤ 1458361790245269^1024*100000^4719 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10373 100000 1458361790245269 50000000000000000000 4719 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10373/100000 : ℝ)) (X := (1458361790245269/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16357/100000 : ℝ) ^ (4719/1024 : ℝ) ≤ (5948030062714091/25000000000000000000 : ℝ) := by
    have hpowers : (16357/100000 : ℝ)^4719 ≤ (5948030062714091/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16357 : ℕ)^4719*25000000000000000000^1024 ≤ 5948030062714091^1024*100000^4719 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16357 100000 5948030062714091 25000000000000000000 4719 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16357/100000 : ℝ)) (X := (5948030062714091/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001458361790245269/25000000000000000000 : ℝ) ≤ (10000126580069409/10000000000000000 : ℝ) ^ (4719/1024 : ℝ) := by
    have hpowers : (25001458361790245269/25000000000000000000 : ℝ)^1024 ≤ (10000126580069409/10000000000000000 : ℝ)^4719 := by
      have hnat : (25001458361790245269 : ℕ)^1024*10000000000000000^4719 ≤ 10000126580069409^4719*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001458361790245269 25000000000000000000 10000126580069409 10000000000000000 1024 4719 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000126580069409/10000000000000000 : ℝ)) (X := (25001458361790245269/25000000000000000000 : ℝ)) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013354421915673451/50000000000000000000 : ℝ) ≤ (2500144877075007/2500000000000000 : ℝ) ^ (4719/1024 : ℝ) := by
    have hpowers : (50013354421915673451/50000000000000000000 : ℝ)^1024 ≤ (2500144877075007/2500000000000000 : ℝ)^4719 := by
      have hnat : (50013354421915673451 : ℕ)^1024*2500000000000000^4719 ≤ 2500144877075007^4719*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013354421915673451 50000000000000000000 2500144877075007 2500000000000000 1024 4719 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500144877075007/2500000000000000 : ℝ)) (X := (50013354421915673451/50000000000000000000 : ℝ)) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505948030062714091/12500000000000000000 : ℝ) ≤ (10001032436530647/10000000000000000 : ℝ) ^ (4719/1024 : ℝ) := by
    have hpowers : (12505948030062714091/12500000000000000000 : ℝ)^1024 ≤ (10001032436530647/10000000000000000 : ℝ)^4719 := by
      have hnat : (12505948030062714091 : ℕ)^1024*10000000000000000^4719 ≤ 10001032436530647^4719*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505948030062714091 12500000000000000000 10001032436530647 10000000000000000 1024 4719 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001032436530647/10000000000000000 : ℝ)) (X := (12505948030062714091/12500000000000000000 : ℝ)) (by norm_num) 4719 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1458361790245269/50000000000000000000 : ℝ) ≤ ((2719607318457405531/2720000000000000000 : ℝ)+2*(452928230619/598400000000000 : ℝ)*(10373/100000 : ℝ))^(4719/1024 : ℝ) := by
    rw [show (2719607318457405531/2720000000000000000 : ℝ)+2*(452928230619/598400000000000 : ℝ)*(10373/100000 : ℝ)=(10000126580069409/10000000000000000 : ℝ) by norm_num, show 1+2*(1458361790245269/50000000000000000000 : ℝ)=(25001458361790245269/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5948030062714091/25000000000000000000 : ℝ)+(1458361790245269/50000000000000000000 : ℝ) ≤ ((2719607318457405531/2720000000000000000 : ℝ)+(452928230619/598400000000000 : ℝ)*((16357/100000 : ℝ)+(10373/100000 : ℝ)))^(4719/1024 : ℝ) := by
    rw [show (2719607318457405531/2720000000000000000 : ℝ)+(452928230619/598400000000000 : ℝ)*((16357/100000 : ℝ)+(10373/100000 : ℝ))=(2500144877075007/2500000000000000 : ℝ) by norm_num, show 1+(5948030062714091/25000000000000000000 : ℝ)+(1458361790245269/50000000000000000000 : ℝ)=(50013354421915673451/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5948030062714091/25000000000000000000 : ℝ) ≤ ((2719607318457405531/2720000000000000000 : ℝ)+2*(452928230619/598400000000000 : ℝ)*(16357/100000 : ℝ))^(4719/1024 : ℝ) := by
    rw [show (2719607318457405531/2720000000000000000 : ℝ)+2*(452928230619/598400000000000 : ℝ)*(16357/100000 : ℝ)=(10001032436530647/10000000000000000 : ℝ) by norm_num, show 1+2*(5948030062714091/25000000000000000000 : ℝ)=(12505948030062714091/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2719607318457405531/2720000000000000000 : ℝ)*(X 1 0+X 2 0)+(452928230619/598400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4719/1024 : ℝ)) (lo := (10373/100000 : ℝ)) (hi := (16357/100000 : ℝ)) (c := (2719607318457405531/2720000000000000000 : ℝ)) (alpha := (452928230619/598400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2719607318457405531/2720000000000000000 : ℝ)*(X 0 1+X 2 1)+(452928230619/598400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4719/1024 : ℝ)) (lo := (10373/100000 : ℝ)) (hi := (16357/100000 : ℝ)) (c := (2719607318457405531/2720000000000000000 : ℝ)) (alpha := (452928230619/598400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2719607318457405531/2720000000000000000 : ℝ)*(X 0 2+X 1 2)+(452928230619/598400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4719/1024 : ℝ)) (lo := (10373/100000 : ℝ)) (hi := (16357/100000 : ℝ)) (c := (2719607318457405531/2720000000000000000 : ℝ)) (alpha := (452928230619/598400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-26987623/156250000 : ℝ)*X 0 0+(1365546313/2500000000 : ℝ)*X 0 1+(5179925441/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677407799/5000000000 : ℝ)*X 1 0+(-58525397/312500000 : ℝ)*X 1 1+(1294981279/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354815349/10000000000 : ℝ)*X 2 0+(1035985061/2000000000 : ℝ)*X 2 1+(-936406393/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1055008197/2500000000 : ℝ)*X 0 0+(1944099977/5000000000 : ℝ)*X 0 1+(2286798529/5000000000 : ℝ)*X 0 2+(1055008197/2500000000 : ℝ)*X 1 0+(1944099977/5000000000 : ℝ)*X 1 1+(2286798529/5000000000 : ℝ)*X 1 2+(1055008197/2500000000 : ℝ)*X 2 0+(1944099977/5000000000 : ℝ)*X 2 1+(2286798529/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1727279603/10000000000 : ℝ)*X 0 0+(5182013791/10000000000 : ℝ)*X 0 1+(5460074969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279981009/10000000000 : ℝ)*X 1 0+(-398165799/2500000000 : ℝ)*X 1 1+(5460074651/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639990571/5000000000 : ℝ)*X 2 0+(170627323/312500000 : ℝ)*X 2 1+(-318532691/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4220207023/10000000000 : ℝ)*X 0 0+(456852497/1000000000 : ℝ)*X 0 1+(486665653/1250000000 : ℝ)*X 0 2+(4220207023/10000000000 : ℝ)*X 1 0+(456852497/1000000000 : ℝ)*X 1 1+(486665653/1250000000 : ℝ)*X 1 2+(4220207023/10000000000 : ℝ)*X 2 0+(456852497/1000000000 : ℝ)*X 2 1+(486665653/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1601_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (705671860460595118198076091/187000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (128261601/20000000000000 : ℝ)*(base19) + (430235681/100000000000000 : ℝ)*(base23) + (8518763/25000000000000 : ℝ)*(lower2) + (120496063/100000000000000 : ℝ)*(upper3) + (9266507/100000000000000 : ℝ)*(lower4) + (625232188006583/25000000000000 : ℝ)*(major0) + (625232188006583/25000000000000 : ℝ)*(major1) + (625232188006583/25000000000000 : ℝ)*(major2) + (221427552624589/6250000000000 : ℝ)*(sp0) + (1771421411727851/50000000000000 : ℝ)*(sp1) + (1771421517264013/50000000000000 : ℝ)*(sp2) + (729505328730399/50000000000000 : ℝ)*(sp3) + (655692571/25000000000000 : ℝ)*(sp4) + (6359453/195312500000 : ℝ)*(sp7) + (729506956750367/50000000000000 : ℝ)*(f.failure) + (885710866190927/25000000000000 : ℝ)*(f.sum) + (84323132662317/7480000000000000000000000000 : ℝ)*base65 + (342897507992150959/44000000000000000000000000000000 : ℝ)*base67 + (351476366663849041/44000000000000000000000000000000 : ℝ)*base70 + (740609968456150959/44000000000000000000000000000000 : ℝ)*base71 + (13958103025043/7480000000000000000000000000 : ℝ)*base74 + (112042062248150959/44000000000000000000000000000000 : ℝ)*base75 + (421001392224150959/44000000000000000000000000000000 : ℝ)*base77 + (543435056720150959/44000000000000000000000000000000 : ℝ)*base79 + (17760714424883/7480000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (11599923/2500000000000000000000 : ℝ)*base90 + (11599923/2500000000000000000000 : ℝ)*base92 + (11599923/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6432853006288030317801724989/748000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1407215309/100000000000000 : ℝ)*(base19) + (1596884731/100000000000000 : ℝ)*(base23) + (318713533/100000000000000 : ℝ)*(lower1) + (104028757/100000000000000 : ℝ)*(upper3) + (79496539/100000000000000 : ℝ)*(lower4) + (114877619/50000000000000 : ℝ)*(upper5) + (2538679372119457/100000000000000 : ℝ)*(major0) + (2538679372119457/100000000000000 : ℝ)*(major1) + (2538679372119457/100000000000000 : ℝ)*(major2) + (726468741/20000000000000 : ℝ)*(sp1) + (1798160626877843/50000000000000 : ℝ)*(sp4) + (56192440846823/1562500000000 : ℝ)*(sp5) + (719263931374191/20000000000000 : ℝ)*(sp6) + (92564825238387/6250000000000 : ℝ)*(sp7) + (92564825238387/6250000000000 : ℝ)*(f.failure) + (1798160626877843/50000000000000 : ℝ)*(f.sum) + (281627865477/29920000000000000000000000000 : ℝ)*base66 + (170480133805401961/176000000000000000000000000000000 : ℝ)*base67 + (1008809867629401961/176000000000000000000000000000000 : ℝ)*base69 + (1320755732717401961/176000000000000000000000000000000 : ℝ)*base71 + (158303044209477/29920000000000000000000000000 : ℝ)*base74 + (2026136944461401961/176000000000000000000000000000000 : ℝ)*base75 + (429637830354598039/176000000000000000000000000000000 : ℝ)*base78 + (3327454569101401961/176000000000000000000000000000000 : ℝ)*base79 + (264482494922523/29920000000000000000000000000 : ℝ)*base81 + (674303/312500000000000000000 : ℝ)*base90 + (674303/312500000000000000000 : ℝ)*base92 + (674303/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1601_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85706131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16357/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (83/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4089/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1601_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1601_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85706131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16533/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2043/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (83/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4089/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1601_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1601_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1601_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4719/1024 : ℝ) ≤ p) (hpb : p ≤ (4723/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85706131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16533/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2043/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (83/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4089/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1601_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

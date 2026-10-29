-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1486_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:14:50.451519+00:00
-- url     : https://prove2.me/submissions/239f0928-c951-4d1d-9f08-4e07130df244

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
theorem support_rectangle_w1486_s3_0 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-190644359/1000000000 : ℝ)*x 0 + (5441039743/10000000000 : ℝ)*x 1 + (5212256049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (190644359/1000000000 : ℝ)^4469 ≤ (11648661248307/100000000000000 : ℝ)^3445 := by
    have hnat : (190644359 : ℕ)^4469*100000000000000^3445 ≤ 11648661248307^3445*1000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190644359 1000000000 11648661248307 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441039743/10000000000 : ℝ)^4469 ≤ (1418944399023/3125000000000 : ℝ)^3445 := by
    have hnat : (5441039743 : ℕ)^4469*3125000000000^3445 ≤ 1418944399023^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441039743 10000000000 1418944399023 3125000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5212256049/10000000000 : ℝ)^4469 ≤ (10736279491209/25000000000000 : ℝ)^3445 := by
    have hnat : (5212256049 : ℕ)^4469*25000000000000^3445 ≤ 10736279491209^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212256049 10000000000 10736279491209 25000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-190644359/1000000000 : ℝ), (5441039743/10000000000 : ℝ), (5212256049/10000000000 : ℝ)] ![(11648661248307/100000000000000 : ℝ), (1418944399023/3125000000000 : ℝ), (10736279491209/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-190644359/1000000000 : ℝ)|^4469 ≤ (11648661248307/100000000000000 : ℝ)^3445
        have hw : |(-190644359/1000000000 : ℝ)|=(190644359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441039743/10000000000 : ℝ)|^4469 ≤ (1418944399023/3125000000000 : ℝ)^3445
        have hw : |(5441039743/10000000000 : ℝ)|=(5441039743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5212256049/10000000000 : ℝ)|^4469 ≤ (10736279491209/25000000000000 : ℝ)^3445
        have hw : |(5212256049/10000000000 : ℝ)|=(5212256049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s3_1 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354141791/10000000000 : ℝ)*x 0 + (-404757219/2000000000 : ℝ)*x 1 + (5212256093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354141791/10000000000 : ℝ)^4469 ≤ (8893546794507/20000000000000 : ℝ)^3445 := by
    have hnat : (5354141791 : ℕ)^4469*20000000000000^3445 ≤ 8893546794507^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354141791 10000000000 8893546794507 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404757219/2000000000 : ℝ)^4469 ≤ (1573393447221/12500000000000 : ℝ)^3445 := by
    have hnat : (404757219 : ℕ)^4469*12500000000000^3445 ≤ 1573393447221^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404757219 2000000000 1573393447221 12500000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5212256093/10000000000 : ℝ)^4469 ≤ (21472559217561/50000000000000 : ℝ)^3445 := by
    have hnat : (5212256093 : ℕ)^4469*50000000000000^3445 ≤ 21472559217561^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212256093 10000000000 21472559217561 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354141791/10000000000 : ℝ), (-404757219/2000000000 : ℝ), (5212256093/10000000000 : ℝ)] ![(8893546794507/20000000000000 : ℝ), (1573393447221/12500000000000 : ℝ), (21472559217561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354141791/10000000000 : ℝ)|^4469 ≤ (8893546794507/20000000000000 : ℝ)^3445
        have hw : |(5354141791/10000000000 : ℝ)|=(5354141791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-404757219/2000000000 : ℝ)|^4469 ≤ (1573393447221/12500000000000 : ℝ)^3445
        have hw : |(-404757219/2000000000 : ℝ)|=(404757219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5212256093/10000000000 : ℝ)|^4469 ≤ (21472559217561/50000000000000 : ℝ)^3445
        have hw : |(5212256093/10000000000 : ℝ)|=(5212256093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s3_2 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338535387/2500000000 : ℝ)*x 0 + (260612813/500000000 : ℝ)*x 1 + (-1011893099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338535387/2500000000 : ℝ)^4469 ≤ (44467731354457/100000000000000 : ℝ)^3445 := by
    have hnat : (1338535387 : ℕ)^4469*100000000000000^3445 ≤ 44467731354457^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338535387 2500000000 44467731354457 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260612813/500000000 : ℝ)^4469 ≤ (4294512022007/10000000000000 : ℝ)^3445 := by
    have hnat : (260612813 : ℕ)^4469*10000000000000^3445 ≤ 4294512022007^3445*500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260612813 500000000 4294512022007 10000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1011893099/5000000000 : ℝ)^4469 ≤ (6293574204403/50000000000000 : ℝ)^3445 := by
    have hnat : (1011893099 : ℕ)^4469*50000000000000^3445 ≤ 6293574204403^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011893099 5000000000 6293574204403 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338535387/2500000000 : ℝ), (260612813/500000000 : ℝ), (-1011893099/5000000000 : ℝ)] ![(44467731354457/100000000000000 : ℝ), (4294512022007/10000000000000 : ℝ), (6293574204403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338535387/2500000000 : ℝ)|^4469 ≤ (44467731354457/100000000000000 : ℝ)^3445
        have hw : |(1338535387/2500000000 : ℝ)|=(1338535387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260612813/500000000 : ℝ)|^4469 ≤ (4294512022007/10000000000000 : ℝ)^3445
        have hw : |(260612813/500000000 : ℝ)|=(260612813/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1011893099/5000000000 : ℝ)|^4469 ≤ (6293574204403/50000000000000 : ℝ)^3445
        have hw : |(-1011893099/5000000000 : ℝ)|=(1011893099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s3_3 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070403593/2500000000 : ℝ)*x 0 + (806707229/2000000000 : ℝ)*x 1 + (2271415873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070403593/2500000000 : ℝ)^4469 ≤ (6654810548841/20000000000000 : ℝ)^3445 := by
    have hnat : (1070403593 : ℕ)^4469*20000000000000^3445 ≤ 6654810548841^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070403593 2500000000 6654810548841 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (806707229/2000000000 : ℝ)^4469 ≤ (30794921912719/100000000000000 : ℝ)^3445 := by
    have hnat : (806707229 : ℕ)^4469*100000000000000^3445 ≤ 30794921912719^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806707229 2000000000 30794921912719 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2271415873/5000000000 : ℝ)^4469 ≤ (7186205066041/20000000000000 : ℝ)^3445 := by
    have hnat : (2271415873 : ℕ)^4469*20000000000000^3445 ≤ 7186205066041^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271415873 5000000000 7186205066041 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070403593/2500000000 : ℝ), (806707229/2000000000 : ℝ), (2271415873/5000000000 : ℝ)] ![(6654810548841/20000000000000 : ℝ), (30794921912719/100000000000000 : ℝ), (7186205066041/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070403593/2500000000 : ℝ)|^4469 ≤ (6654810548841/20000000000000 : ℝ)^3445
        have hw : |(1070403593/2500000000 : ℝ)|=(1070403593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(806707229/2000000000 : ℝ)|^4469 ≤ (30794921912719/100000000000000 : ℝ)^3445
        have hw : |(806707229/2000000000 : ℝ)|=(806707229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2271415873/5000000000 : ℝ)|^4469 ≤ (7186205066041/20000000000000 : ℝ)^3445
        have hw : |(2271415873/5000000000 : ℝ)|=(2271415873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s3_4 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1906477183/10000000000 : ℝ)*x 0 + (1042694377/2000000000 : ℝ)*x 1 + (1087962931/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1906477183/10000000000 : ℝ)^4469 ≤ (5824463759421/50000000000000 : ℝ)^3445 := by
    have hnat : (1906477183 : ℕ)^4469*50000000000000^3445 ≤ 5824463759421^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906477183 10000000000 5824463759421 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042694377/2000000000 : ℝ)^4469 ≤ (42958113651747/100000000000000 : ℝ)^3445 := by
    have hnat : (1042694377 : ℕ)^4469*100000000000000^3445 ≤ 42958113651747^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042694377 2000000000 42958113651747 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087962931/2000000000 : ℝ)^4469 ≤ (45392958820187/100000000000000 : ℝ)^3445 := by
    have hnat : (1087962931 : ℕ)^4469*100000000000000^3445 ≤ 45392958820187^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087962931 2000000000 45392958820187 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1906477183/10000000000 : ℝ), (1042694377/2000000000 : ℝ), (1087962931/2000000000 : ℝ)] ![(5824463759421/50000000000000 : ℝ), (42958113651747/100000000000000 : ℝ), (45392958820187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1906477183/10000000000 : ℝ)|^4469 ≤ (5824463759421/50000000000000 : ℝ)^3445
        have hw : |(-1906477183/10000000000 : ℝ)|=(1906477183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042694377/2000000000 : ℝ)|^4469 ≤ (42958113651747/100000000000000 : ℝ)^3445
        have hw : |(1042694377/2000000000 : ℝ)|=(1042694377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087962931/2000000000 : ℝ)|^4469 ≤ (45392958820187/100000000000000 : ℝ)^3445
        have hw : |(1087962931/2000000000 : ℝ)|=(1087962931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s3_5 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661791049/1250000000 : ℝ)*x 0 + (-179622769/1000000000 : ℝ)*x 1 + (5439814743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661791049/1250000000 : ℝ)^4469 ≤ (21912189116667/50000000000000 : ℝ)^3445 := by
    have hnat : (661791049 : ℕ)^4469*50000000000000^3445 ≤ 21912189116667^3445*1250000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661791049 1250000000 21912189116667 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179622769/1000000000 : ℝ)^4469 ≤ (1347832747331/12500000000000 : ℝ)^3445 := by
    have hnat : (179622769 : ℕ)^4469*12500000000000^3445 ≤ 1347832747331^3445*1000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179622769 1000000000 1347832747331 12500000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439814743/10000000000 : ℝ)^4469 ≤ (22696479886391/50000000000000 : ℝ)^3445 := by
    have hnat : (5439814743 : ℕ)^4469*50000000000000^3445 ≤ 22696479886391^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439814743 10000000000 22696479886391 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661791049/1250000000 : ℝ), (-179622769/1000000000 : ℝ), (5439814743/10000000000 : ℝ)] ![(21912189116667/50000000000000 : ℝ), (1347832747331/12500000000000 : ℝ), (22696479886391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661791049/1250000000 : ℝ)|^4469 ≤ (21912189116667/50000000000000 : ℝ)^3445
        have hw : |(661791049/1250000000 : ℝ)|=(661791049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-179622769/1000000000 : ℝ)|^4469 ≤ (1347832747331/12500000000000 : ℝ)^3445
        have hw : |(-179622769/1000000000 : ℝ)|=(179622769/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439814743/10000000000 : ℝ)|^4469 ≤ (22696479886391/50000000000000 : ℝ)^3445
        have hw : |(5439814743/10000000000 : ℝ)|=(5439814743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s3_6 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294328513/10000000000 : ℝ)*x 0 + (543981457/1000000000 : ℝ)*x 1 + (-449056941/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294328513/10000000000 : ℝ)^4469 ≤ (43824379532639/100000000000000 : ℝ)^3445 := by
    have hnat : (5294328513 : ℕ)^4469*100000000000000^3445 ≤ 43824379532639^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294328513 10000000000 43824379532639 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543981457/1000000000 : ℝ)^4469 ≤ (45392957900067/100000000000000 : ℝ)^3445 := by
    have hnat : (543981457 : ℕ)^4469*100000000000000^3445 ≤ 45392957900067^3445*1000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543981457 1000000000 45392957900067 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449056941/2500000000 : ℝ)^4469 ≤ (10782662554907/100000000000000 : ℝ)^3445 := by
    have hnat : (449056941 : ℕ)^4469*100000000000000^3445 ≤ 10782662554907^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449056941 2500000000 10782662554907 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294328513/10000000000 : ℝ), (543981457/1000000000 : ℝ), (-449056941/2500000000 : ℝ)] ![(43824379532639/100000000000000 : ℝ), (45392957900067/100000000000000 : ℝ), (10782662554907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294328513/10000000000 : ℝ)|^4469 ≤ (43824379532639/100000000000000 : ℝ)^3445
        have hw : |(5294328513/10000000000 : ℝ)|=(5294328513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543981457/1000000000 : ℝ)|^4469 ≤ (45392957900067/100000000000000 : ℝ)^3445
        have hw : |(543981457/1000000000 : ℝ)|=(543981457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-449056941/2500000000 : ℝ)|^4469 ≤ (10782662554907/100000000000000 : ℝ)^3445
        have hw : |(-449056941/2500000000 : ℝ)|=(449056941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s3_7 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070422369/2500000000 : ℝ)*x 0 + (908025033/2000000000 : ℝ)*x 1 + (4036263127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070422369/2500000000 : ℝ)^4469 ≤ (2079675618557/6250000000000 : ℝ)^3445 := by
    have hnat : (1070422369 : ℕ)^4469*6250000000000^3445 ≤ 2079675618557^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070422369 2500000000 2079675618557 6250000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (908025033/2000000000 : ℝ)^4469 ≤ (35903257198987/100000000000000 : ℝ)^3445 := by
    have hnat : (908025033 : ℕ)^4469*100000000000000^3445 ≤ 35903257198987^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908025033 2000000000 35903257198987 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4036263127/10000000000 : ℝ)^4469 ≤ (1926370805177/6250000000000 : ℝ)^3445 := by
    have hnat : (4036263127 : ℕ)^4469*6250000000000^3445 ≤ 1926370805177^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4036263127 10000000000 1926370805177 6250000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070422369/2500000000 : ℝ), (908025033/2000000000 : ℝ), (4036263127/10000000000 : ℝ)] ![(2079675618557/6250000000000 : ℝ), (35903257198987/100000000000000 : ℝ), (1926370805177/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070422369/2500000000 : ℝ)|^4469 ≤ (2079675618557/6250000000000 : ℝ)^3445
        have hw : |(1070422369/2500000000 : ℝ)|=(1070422369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(908025033/2000000000 : ℝ)|^4469 ≤ (35903257198987/100000000000000 : ℝ)^3445
        have hw : |(908025033/2000000000 : ℝ)|=(908025033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4036263127/10000000000 : ℝ)|^4469 ≤ (1926370805177/6250000000000 : ℝ)^3445
        have hw : |(4036263127/10000000000 : ℝ)|=(4036263127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1486_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2013/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2559/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10727/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15569/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2013/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2559/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2013/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2559/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2013/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2559/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2013/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2559/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2013/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2559/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2013/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2559/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2559/25000 : ℝ) ^ (4467/1024 : ℝ) ≤ (4807138869429657/100000000000000000000 : ℝ) := by
    have hpowers : (2559/25000 : ℝ)^4467 ≤ (4807138869429657/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2559 : ℕ)^4467*100000000000000000000^1024 ≤ 4807138869429657^1024*25000^4467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2559 25000 4807138869429657 100000000000000000000 4467 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2559/25000 : ℝ)) (X := (4807138869429657/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2013/12500 : ℝ) ^ (4467/1024 : ℝ) ≤ (17352954829249573/50000000000000000000 : ℝ) := by
    have hpowers : (2013/12500 : ℝ)^4467 ≤ (17352954829249573/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2013 : ℕ)^4467*50000000000000000000^1024 ≤ 17352954829249573^1024*12500^4467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2013 12500 17352954829249573 50000000000000000000 4467 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2013/12500 : ℝ)) (X := (17352954829249573/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004807138869429657/50000000000000000000 : ℝ) ≤ (2000044077258343/2000000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (50004807138869429657/50000000000000000000 : ℝ)^1024 ≤ (2000044077258343/2000000000000000 : ℝ)^4467 := by
      have hnat : (50004807138869429657 : ℕ)^1024*2000000000000000^4467 ≤ 2000044077258343^4467*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004807138869429657 50000000000000000000 2000044077258343 2000000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000044077258343/2000000000000000 : ℝ)) (X := (50004807138869429657/50000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039513048527928803/100000000000000000000 : ℝ) ≤ (10000905645888353/10000000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (100039513048527928803/100000000000000000000 : ℝ)^1024 ≤ (10000905645888353/10000000000000000 : ℝ)^4467 := by
      have hnat : (100039513048527928803 : ℕ)^1024*10000000000000000^4467 ≤ 10000905645888353^4467*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039513048527928803 100000000000000000000 10000905645888353 10000000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000905645888353/10000000000000000 : ℝ)) (X := (100039513048527928803/100000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017352954829249573/25000000000000000000 : ℝ) ≤ (10001590905484991/10000000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (25017352954829249573/25000000000000000000 : ℝ)^1024 ≤ (10001590905484991/10000000000000000 : ℝ)^4467 := by
      have hnat : (25017352954829249573 : ℕ)^1024*10000000000000000^4467 ≤ 10001590905484991^4467*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017352954829249573 25000000000000000000 10001590905484991 10000000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001590905484991/10000000000000000 : ℝ)) (X := (25017352954829249573/25000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4807138869429657/100000000000000000000 : ℝ) ≤ ((1629646238674928069/1630000000000000000 : ℝ)+2*(38069977591/32600000000000 : ℝ)*(2559/25000 : ℝ))^(4467/1024 : ℝ) := by
    rw [show (1629646238674928069/1630000000000000000 : ℝ)+2*(38069977591/32600000000000 : ℝ)*(2559/25000 : ℝ)=(2000044077258343/2000000000000000 : ℝ) by norm_num, show 1+2*(4807138869429657/100000000000000000000 : ℝ)=(50004807138869429657/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17352954829249573/50000000000000000000 : ℝ)+(4807138869429657/100000000000000000000 : ℝ) ≤ ((1629646238674928069/1630000000000000000 : ℝ)+(38069977591/32600000000000 : ℝ)*((2013/12500 : ℝ)+(2559/25000 : ℝ)))^(4467/1024 : ℝ) := by
    rw [show (1629646238674928069/1630000000000000000 : ℝ)+(38069977591/32600000000000 : ℝ)*((2013/12500 : ℝ)+(2559/25000 : ℝ))=(10000905645888353/10000000000000000 : ℝ) by norm_num, show 1+(17352954829249573/50000000000000000000 : ℝ)+(4807138869429657/100000000000000000000 : ℝ)=(100039513048527928803/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17352954829249573/50000000000000000000 : ℝ) ≤ ((1629646238674928069/1630000000000000000 : ℝ)+2*(38069977591/32600000000000 : ℝ)*(2013/12500 : ℝ))^(4467/1024 : ℝ) := by
    rw [show (1629646238674928069/1630000000000000000 : ℝ)+2*(38069977591/32600000000000 : ℝ)*(2013/12500 : ℝ)=(10001590905484991/10000000000000000 : ℝ) by norm_num, show 1+2*(17352954829249573/50000000000000000000 : ℝ)=(25017352954829249573/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1629646238674928069/1630000000000000000 : ℝ)*(X 1 0+X 2 0)+(38069977591/32600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (2559/25000 : ℝ)) (hi := (2013/12500 : ℝ)) (c := (1629646238674928069/1630000000000000000 : ℝ)) (alpha := (38069977591/32600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1629646238674928069/1630000000000000000 : ℝ)*(X 0 1+X 2 1)+(38069977591/32600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (2559/25000 : ℝ)) (hi := (2013/12500 : ℝ)) (c := (1629646238674928069/1630000000000000000 : ℝ)) (alpha := (38069977591/32600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1629646238674928069/1630000000000000000 : ℝ)*(X 0 2+X 1 2)+(38069977591/32600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (2559/25000 : ℝ)) (hi := (2013/12500 : ℝ)) (c := (1629646238674928069/1630000000000000000 : ℝ)) (alpha := (38069977591/32600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-190644359/1000000000 : ℝ)*X 0 0+(5441039743/10000000000 : ℝ)*X 0 1+(5212256049/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354141791/10000000000 : ℝ)*X 1 0+(-404757219/2000000000 : ℝ)*X 1 1+(5212256093/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338535387/2500000000 : ℝ)*X 2 0+(260612813/500000000 : ℝ)*X 2 1+(-1011893099/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1070403593/2500000000 : ℝ)*X 0 0+(806707229/2000000000 : ℝ)*X 0 1+(2271415873/5000000000 : ℝ)*X 0 2+(1070403593/2500000000 : ℝ)*X 1 0+(806707229/2000000000 : ℝ)*X 1 1+(2271415873/5000000000 : ℝ)*X 1 2+(1070403593/2500000000 : ℝ)*X 2 0+(806707229/2000000000 : ℝ)*X 2 1+(2271415873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1906477183/10000000000 : ℝ)*X 0 0+(1042694377/2000000000 : ℝ)*X 0 1+(1087962931/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661791049/1250000000 : ℝ)*X 1 0+(-179622769/1000000000 : ℝ)*X 1 1+(5439814743/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294328513/10000000000 : ℝ)*X 2 0+(543981457/1000000000 : ℝ)*X 2 1+(-449056941/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1070422369/2500000000 : ℝ)*X 0 0+(908025033/2000000000 : ℝ)*X 0 1+(4036263127/10000000000 : ℝ)*X 0 2+(1070422369/2500000000 : ℝ)*X 1 0+(908025033/2000000000 : ℝ)*X 1 1+(4036263127/10000000000 : ℝ)*X 1 2+(1070422369/2500000000 : ℝ)*X 2 0+(908025033/2000000000 : ℝ)*X 2 1+(4036263127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45034322278941806031298377/20375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (269823301/25000000000000 : ℝ)*(base19) + (737252417/100000000000000 : ℝ)*(base23) + (10003101/50000000000000 : ℝ)*(upper2) + (229594821/100000000000000 : ℝ)*(upper3) + (19385009/20000000000000 : ℝ)*(upper4) + (1583620631719689/50000000000000 : ℝ)*(major0) + (1583620631719689/50000000000000 : ℝ)*(major1) + (1583620631719689/50000000000000 : ℝ)*(major2) + (2185480132341927/50000000000000 : ℝ)*(sp0) + (43709726489733/1000000000000 : ℝ)*(sp1) + (546371623876761/12500000000000 : ℝ)*(sp2) + (78540052512269/4000000000000 : ℝ)*(sp3) + (269271653/2000000000000 : ℝ)*(sp4) + (7412129737/100000000000000 : ℝ)*(sp7) + (981754362468231/50000000000000 : ℝ)*(f.failure) + (546371716033313/12500000000000 : ℝ)*(f.sum) + (751389402931/815000000000000000000000000 : ℝ)*base66 + (711638698893000541/81500000000000000000000000000000 : ℝ)*base67 + (627175640638500541/81500000000000000000000000000000 : ℝ)*base69 + (767721431628000541/81500000000000000000000000000000 : ℝ)*base71 + (1350833743251/815000000000000000000000000 : ℝ)*base74 + (972617603862500541/81500000000000000000000000000000 : ℝ)*base75 + (83215824177999459/81500000000000000000000000000000 : ℝ)*base78 + (73250331091000541/81500000000000000000000000000000 : ℝ)*base79 + (233674404853/101875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (16731651/5000000000000000000000 : ℝ)*base90 + (16731651/5000000000000000000000 : ℝ)*base92 + (16731651/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (355058665879109213755061301/40750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1936645501/100000000000000 : ℝ)*(base19) + (407293909/20000000000000 : ℝ)*(base23) + (13022083/100000000000000 : ℝ)*(upper2) + (23277907/10000000000000 : ℝ)*(upper3) + (299453381/100000000000000 : ℝ)*(upper5) + (1600687481042757/50000000000000 : ℝ)*(major0) + (1600687481042757/50000000000000 : ℝ)*(major1) + (1600687481042757/50000000000000 : ℝ)*(major2) + (30288730399/100000000000000 : ℝ)*(sp1) + (14005015169/50000000000000 : ℝ)*(sp2) + (4418079964767743/100000000000000 : ℝ)*(sp4) + (1104511934847961/25000000000000 : ℝ)*(sp5) + (220902495913393/5000000000000 : ℝ)*(sp6) + (248083708620843/12500000000000 : ℝ)*(sp7) + (248083708620843/12500000000000 : ℝ)*(f.failure) + (4418079964767743/100000000000000 : ℝ)*(f.sum) + (268788572881/407500000000000000000000000 : ℝ)*base65 + (623713428335296233/81500000000000000000000000000000 : ℝ)*base67 + (102113115538296233/81500000000000000000000000000000 : ℝ)*base69 + (13820915473703767/81500000000000000000000000000000 : ℝ)*base72 + (1216359602481/407500000000000000000000000 : ℝ)*base73 + (242187997482703767/81500000000000000000000000000000 : ℝ)*base76 + (632039204845796233/81500000000000000000000000000000 : ℝ)*base77 + (25851390547796233/81500000000000000000000000000000 : ℝ)*base79 + (3386672588673/815000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1754103/1250000000000000000000 : ℝ)*base90 + (1754103/1250000000000000000000 : ℝ)*base92 + (1754103/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1486_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2013/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2559/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10727/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15569/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1486_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1486_s4_0 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-476758181/2500000000 : ℝ)*x 0 + (5437218637/10000000000 : ℝ)*x 1 + (5215688603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (476758181/2500000000 : ℝ)^4469 ≤ (11653331144387/100000000000000 : ℝ)^3445 := by
    have hnat : (476758181 : ℕ)^4469*100000000000000^3445 ≤ 11653331144387^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476758181 2500000000 11653331144387 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437218637/10000000000 : ℝ)^4469 ≤ (22682429536587/50000000000000 : ℝ)^3445 := by
    have hnat : (5437218637 : ℕ)^4469*50000000000000^3445 ≤ 22682429536587^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437218637 10000000000 22682429536587 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215688603/10000000000 : ℝ)^4469 ≤ (21490904884319/50000000000000 : ℝ)^3445 := by
    have hnat : (5215688603 : ℕ)^4469*50000000000000^3445 ≤ 21490904884319^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215688603 10000000000 21490904884319 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-476758181/2500000000 : ℝ), (5437218637/10000000000 : ℝ), (5215688603/10000000000 : ℝ)] ![(11653331144387/100000000000000 : ℝ), (22682429536587/50000000000000 : ℝ), (21490904884319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-476758181/2500000000 : ℝ)|^4469 ≤ (11653331144387/100000000000000 : ℝ)^3445
        have hw : |(-476758181/2500000000 : ℝ)|=(476758181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437218637/10000000000 : ℝ)|^4469 ≤ (22682429536587/50000000000000 : ℝ)^3445
        have hw : |(5437218637/10000000000 : ℝ)|=(5437218637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215688603/10000000000 : ℝ)|^4469 ≤ (21490904884319/50000000000000 : ℝ)^3445
        have hw : |(5215688603/10000000000 : ℝ)|=(5215688603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s4_1 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676573431/5000000000 : ℝ)*x 0 + (-404112651/2000000000 : ℝ)*x 1 + (325980681/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676573431/5000000000 : ℝ)^4469 ≤ (277856343257/625000000000 : ℝ)^3445 := by
    have hnat : (2676573431 : ℕ)^4469*625000000000^3445 ≤ 277856343257^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676573431 5000000000 277856343257 625000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404112651/2000000000 : ℝ)^4469 ≤ (785071924137/6250000000000 : ℝ)^3445 := by
    have hnat : (404112651 : ℕ)^4469*6250000000000^3445 ≤ 785071924137^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404112651 2000000000 785071924137 6250000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325980681/625000000 : ℝ)^4469 ≤ (42981834281739/100000000000000 : ℝ)^3445 := by
    have hnat : (325980681 : ℕ)^4469*100000000000000^3445 ≤ 42981834281739^3445*625000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325980681 625000000 42981834281739 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676573431/5000000000 : ℝ), (-404112651/2000000000 : ℝ), (325980681/625000000 : ℝ)] ![(277856343257/625000000000 : ℝ), (785071924137/6250000000000 : ℝ), (42981834281739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676573431/5000000000 : ℝ)|^4469 ≤ (277856343257/625000000000 : ℝ)^3445
        have hw : |(2676573431/5000000000 : ℝ)|=(2676573431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-404112651/2000000000 : ℝ)|^4469 ≤ (785071924137/6250000000000 : ℝ)^3445
        have hw : |(-404112651/2000000000 : ℝ)|=(404112651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(325980681/625000000 : ℝ)|^4469 ≤ (42981834281739/100000000000000 : ℝ)^3445
        have hw : |(325980681/625000000 : ℝ)|=(325980681/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s4_2 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676574079/5000000000 : ℝ)*x 0 + (2607844433/5000000000 : ℝ)*x 1 + (-1010282107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676574079/5000000000 : ℝ)^4469 ≤ (4445702888343/10000000000000 : ℝ)^3445 := by
    have hnat : (2676574079 : ℕ)^4469*10000000000000^3445 ≤ 4445702888343^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676574079 5000000000 4445702888343 10000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607844433/5000000000 : ℝ)^4469 ≤ (21490906290107/50000000000000 : ℝ)^3445 := by
    have hnat : (2607844433 : ℕ)^4469*50000000000000^3445 ≤ 21490906290107^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607844433 5000000000 21490906290107 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1010282107/5000000000 : ℝ)^4469 ≤ (628057926003/5000000000000 : ℝ)^3445 := by
    have hnat : (1010282107 : ℕ)^4469*5000000000000^3445 ≤ 628057926003^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010282107 5000000000 628057926003 5000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676574079/5000000000 : ℝ), (2607844433/5000000000 : ℝ), (-1010282107/5000000000 : ℝ)] ![(4445702888343/10000000000000 : ℝ), (21490906290107/50000000000000 : ℝ), (628057926003/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676574079/5000000000 : ℝ)|^4469 ≤ (4445702888343/10000000000000 : ℝ)^3445
        have hw : |(2676574079/5000000000 : ℝ)|=(2676574079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607844433/5000000000 : ℝ)|^4469 ≤ (21490906290107/50000000000000 : ℝ)^3445
        have hw : |(2607844433/5000000000 : ℝ)|=(2607844433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1010282107/5000000000 : ℝ)|^4469 ≤ (628057926003/5000000000000 : ℝ)^3445
        have hw : |(-1010282107/5000000000 : ℝ)|=(1010282107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s4_3 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (428198347/1000000000 : ℝ)*x 0 + (4041567539/10000000000 : ℝ)*x 1 + (283419509/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428198347/1000000000 : ℝ)^4469 ≤ (8319443450757/25000000000000 : ℝ)^3445 := by
    have hnat : (428198347 : ℕ)^4469*25000000000000^3445 ≤ 8319443450757^3445*1000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428198347 1000000000 8319443450757 25000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4041567539/10000000000 : ℝ)^4469 ≤ (7718622258939/25000000000000 : ℝ)^3445 := by
    have hnat : (4041567539 : ℕ)^4469*25000000000000^3445 ≤ 7718622258939^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4041567539 10000000000 7718622258939 25000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283419509/625000000 : ℝ)^4469 ≤ (8961934286199/25000000000000 : ℝ)^3445 := by
    have hnat : (283419509 : ℕ)^4469*25000000000000^3445 ≤ 8961934286199^3445*625000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283419509 625000000 8961934286199 25000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(428198347/1000000000 : ℝ), (4041567539/10000000000 : ℝ), (283419509/625000000 : ℝ)] ![(8319443450757/25000000000000 : ℝ), (7718622258939/25000000000000 : ℝ), (8961934286199/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(428198347/1000000000 : ℝ)|^4469 ≤ (8319443450757/25000000000000 : ℝ)^3445
        have hw : |(428198347/1000000000 : ℝ)|=(428198347/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4041567539/10000000000 : ℝ)|^4469 ≤ (7718622258939/25000000000000 : ℝ)^3445
        have hw : |(4041567539/10000000000 : ℝ)|=(4041567539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283419509/625000000 : ℝ)|^4469 ≤ (8961934286199/25000000000000 : ℝ)^3445
        have hw : |(283419509/625000000 : ℝ)|=(283419509/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s4_4 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1907062743/10000000000 : ℝ)*x 0 + (1043365931/2000000000 : ℝ)*x 1 + (1359017387/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1907062743/10000000000 : ℝ)^4469 ≤ (2330713821573/20000000000000 : ℝ)^3445 := by
    have hnat : (1907062743 : ℕ)^4469*20000000000000^3445 ≤ 2330713821573^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1907062743 10000000000 2330713821573 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043365931/2000000000 : ℝ)^4469 ≤ (42994008473613/100000000000000 : ℝ)^3445 := by
    have hnat : (1043365931 : ℕ)^4469*100000000000000^3445 ≤ 42994008473613^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043365931 2000000000 42994008473613 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359017387/2500000000 : ℝ)^4469 ≤ (9070484481709/20000000000000 : ℝ)^3445 := by
    have hnat : (1359017387 : ℕ)^4469*20000000000000^3445 ≤ 9070484481709^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359017387 2500000000 9070484481709 20000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1907062743/10000000000 : ℝ), (1043365931/2000000000 : ℝ), (1359017387/2500000000 : ℝ)] ![(2330713821573/20000000000000 : ℝ), (42994008473613/100000000000000 : ℝ), (9070484481709/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1907062743/10000000000 : ℝ)|^4469 ≤ (2330713821573/20000000000000 : ℝ)^3445
        have hw : |(-1907062743/10000000000 : ℝ)|=(1907062743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043365931/2000000000 : ℝ)|^4469 ≤ (42994008473613/100000000000000 : ℝ)^3445
        have hw : |(1043365931/2000000000 : ℝ)|=(1043365931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359017387/2500000000 : ℝ)|^4469 ≤ (9070484481709/20000000000000 : ℝ)^3445
        have hw : |(1359017387/2500000000 : ℝ)|=(1359017387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s4_5 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165476059/312500000 : ℝ)*x 0 + (-900091811/5000000000 : ℝ)*x 1 + (5436069347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165476059/312500000 : ℝ)^4469 ≤ (21917050877549/50000000000000 : ℝ)^3445 := by
    have hnat : (165476059 : ℕ)^4469*50000000000000^3445 ≤ 21917050877549^3445*312500000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165476059 312500000 21917050877549 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900091811/5000000000 : ℝ)^4469 ≤ (10813478002767/100000000000000 : ℝ)^3445 := by
    have hnat : (900091811 : ℕ)^4469*100000000000000^3445 ≤ 10813478002767^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900091811 5000000000 10813478002767 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436069347/10000000000 : ℝ)^4469 ≤ (22676210116589/50000000000000 : ℝ)^3445 := by
    have hnat : (5436069347 : ℕ)^4469*50000000000000^3445 ≤ 22676210116589^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436069347 10000000000 22676210116589 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165476059/312500000 : ℝ), (-900091811/5000000000 : ℝ), (5436069347/10000000000 : ℝ)] ![(21917050877549/50000000000000 : ℝ), (10813478002767/100000000000000 : ℝ), (22676210116589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165476059/312500000 : ℝ)|^4469 ≤ (21917050877549/50000000000000 : ℝ)^3445
        have hw : |(165476059/312500000 : ℝ)|=(165476059/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-900091811/5000000000 : ℝ)|^4469 ≤ (10813478002767/100000000000000 : ℝ)^3445
        have hw : |(-900091811/5000000000 : ℝ)|=(900091811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436069347/10000000000 : ℝ)|^4469 ≤ (22676210116589/50000000000000 : ℝ)^3445
        have hw : |(5436069347/10000000000 : ℝ)|=(5436069347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s4_6 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059046703/2000000000 : ℝ)*x 0 + (1087213931/2000000000 : ℝ)*x 1 + (-450045927/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059046703/2000000000 : ℝ)^4469 ≤ (10958524437399/25000000000000 : ℝ)^3445 := by
    have hnat : (1059046703 : ℕ)^4469*25000000000000^3445 ≤ 10958524437399^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059046703 2000000000 10958524437399 25000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087213931/2000000000 : ℝ)^4469 ≤ (45352423566577/100000000000000 : ℝ)^3445 := by
    have hnat : (1087213931 : ℕ)^4469*100000000000000^3445 ≤ 45352423566577^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087213931 2000000000 45352423566577 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450045927/2500000000 : ℝ)^4469 ≤ (10813478672911/100000000000000 : ℝ)^3445 := by
    have hnat : (450045927 : ℕ)^4469*100000000000000^3445 ≤ 10813478672911^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450045927 2500000000 10813478672911 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059046703/2000000000 : ℝ), (1087213931/2000000000 : ℝ), (-450045927/2500000000 : ℝ)] ![(10958524437399/25000000000000 : ℝ), (45352423566577/100000000000000 : ℝ), (10813478672911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059046703/2000000000 : ℝ)|^4469 ≤ (10958524437399/25000000000000 : ℝ)^3445
        have hw : |(1059046703/2000000000 : ℝ)|=(1059046703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087213931/2000000000 : ℝ)|^4469 ≤ (45352423566577/100000000000000 : ℝ)^3445
        have hw : |(1087213931/2000000000 : ℝ)|=(1087213931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-450045927/2500000000 : ℝ)|^4469 ≤ (10813478672911/100000000000000 : ℝ)^3445
        have hw : |(-450045927/2500000000 : ℝ)|=(450045927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s4_7 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (856409903/2000000000 : ℝ)*x 0 + (4532175251/10000000000 : ℝ)*x 1 + (2022062551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (856409903/2000000000 : ℝ)^4469 ≤ (1331137585811/4000000000000 : ℝ)^3445 := by
    have hnat : (856409903 : ℕ)^4469*4000000000000^3445 ≤ 1331137585811^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856409903 2000000000 1331137585811 4000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4532175251/10000000000 : ℝ)^4469 ≤ (8955430905253/25000000000000 : ℝ)^3445 := by
    have hnat : (4532175251 : ℕ)^4469*25000000000000^3445 ≤ 8955430905253^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532175251 10000000000 8955430905253 25000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2022062551/5000000000 : ℝ)^4469 ≤ (15449918358709/50000000000000 : ℝ)^3445 := by
    have hnat : (2022062551 : ℕ)^4469*50000000000000^3445 ≤ 15449918358709^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022062551 5000000000 15449918358709 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(856409903/2000000000 : ℝ), (4532175251/10000000000 : ℝ), (2022062551/5000000000 : ℝ)] ![(1331137585811/4000000000000 : ℝ), (8955430905253/25000000000000 : ℝ), (15449918358709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(856409903/2000000000 : ℝ)|^4469 ≤ (1331137585811/4000000000000 : ℝ)^3445
        have hw : |(856409903/2000000000 : ℝ)|=(856409903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4532175251/10000000000 : ℝ)|^4469 ≤ (8955430905253/25000000000000 : ℝ)^3445
        have hw : |(4532175251/10000000000 : ℝ)|=(4532175251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2022062551/5000000000 : ℝ)|^4469 ≤ (15449918358709/50000000000000 : ℝ)^3445
        have hw : |(2022062551/5000000000 : ℝ)|=(2022062551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1486_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15569/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10727/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (27/250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15569/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10727/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15569/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10727/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15569/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10727/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15569/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10727/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15569/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10727/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15569/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10727/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10727/100000 : ℝ) ^ (4467/1024 : ℝ) ≤ (5897267922410617/100000000000000000000 : ℝ) := by
    have hpowers : (10727/100000 : ℝ)^4467 ≤ (5897267922410617/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10727 : ℕ)^4467*100000000000000000000^1024 ≤ 5897267922410617^1024*100000^4467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10727 100000 5897267922410617 100000000000000000000 4467 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10727/100000 : ℝ)) (X := (5897267922410617/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15569/100000 : ℝ) ^ (4467/1024 : ℝ) ≤ (14974942069227249/50000000000000000000 : ℝ) := by
    have hpowers : (15569/100000 : ℝ)^4467 ≤ (14974942069227249/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15569 : ℕ)^4467*50000000000000000000^1024 ≤ 14974942069227249^1024*100000^4467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15569 100000 14974942069227249 50000000000000000000 4467 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15569/100000 : ℝ)) (X := (14974942069227249/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005897267922410617/50000000000000000000 : ℝ) ≤ (10000270361669311/10000000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (50005897267922410617/50000000000000000000 : ℝ)^1024 ≤ (10000270361669311/10000000000000000 : ℝ)^4467 := by
      have hnat : (50005897267922410617 : ℕ)^1024*10000000000000000^4467 ≤ 10000270361669311^4467*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005897267922410617 50000000000000000000 10000270361669311 10000000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000270361669311/10000000000000000 : ℝ)) (X := (50005897267922410617/50000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007169430412173023/20000000000000000000 : ℝ) ≤ (2000164326902639/2000000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (20007169430412173023/20000000000000000000 : ℝ)^1024 ≤ (2000164326902639/2000000000000000 : ℝ)^4467 := by
      have hnat : (20007169430412173023 : ℕ)^1024*2000000000000000^4467 ≤ 2000164326902639^4467*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007169430412173023 20000000000000000000 2000164326902639 2000000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000164326902639/2000000000000000 : ℝ)) (X := (20007169430412173023/20000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014974942069227249/25000000000000000000 : ℝ) ≤ (10001372907357079/10000000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (25014974942069227249/25000000000000000000 : ℝ)^1024 ≤ (10001372907357079/10000000000000000 : ℝ)^4467 := by
      have hnat : (25014974942069227249 : ℕ)^1024*10000000000000000^4467 ≤ 10001372907357079^4467*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014974942069227249 25000000000000000000 10001372907357079 10000000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001372907357079/10000000000000000 : ℝ)) (X := (25014974942069227249/25000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5897267922410617/100000000000000000000 : ℝ) ≤ ((8068247013935019421/8070000000000000000 : ℝ)+2*(45939403657/40350000000000 : ℝ)*(10727/100000 : ℝ))^(4467/1024 : ℝ) := by
    rw [show (8068247013935019421/8070000000000000000 : ℝ)+2*(45939403657/40350000000000 : ℝ)*(10727/100000 : ℝ)=(10000270361669311/10000000000000000 : ℝ) by norm_num, show 1+2*(5897267922410617/100000000000000000000 : ℝ)=(50005897267922410617/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14974942069227249/50000000000000000000 : ℝ)+(5897267922410617/100000000000000000000 : ℝ) ≤ ((8068247013935019421/8070000000000000000 : ℝ)+(45939403657/40350000000000 : ℝ)*((15569/100000 : ℝ)+(10727/100000 : ℝ)))^(4467/1024 : ℝ) := by
    rw [show (8068247013935019421/8070000000000000000 : ℝ)+(45939403657/40350000000000 : ℝ)*((15569/100000 : ℝ)+(10727/100000 : ℝ))=(2000164326902639/2000000000000000 : ℝ) by norm_num, show 1+(14974942069227249/50000000000000000000 : ℝ)+(5897267922410617/100000000000000000000 : ℝ)=(20007169430412173023/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14974942069227249/50000000000000000000 : ℝ) ≤ ((8068247013935019421/8070000000000000000 : ℝ)+2*(45939403657/40350000000000 : ℝ)*(15569/100000 : ℝ))^(4467/1024 : ℝ) := by
    rw [show (8068247013935019421/8070000000000000000 : ℝ)+2*(45939403657/40350000000000 : ℝ)*(15569/100000 : ℝ)=(10001372907357079/10000000000000000 : ℝ) by norm_num, show 1+2*(14974942069227249/50000000000000000000 : ℝ)=(25014974942069227249/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8068247013935019421/8070000000000000000 : ℝ)*(X 1 0+X 2 0)+(45939403657/40350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (10727/100000 : ℝ)) (hi := (15569/100000 : ℝ)) (c := (8068247013935019421/8070000000000000000 : ℝ)) (alpha := (45939403657/40350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8068247013935019421/8070000000000000000 : ℝ)*(X 0 1+X 2 1)+(45939403657/40350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (10727/100000 : ℝ)) (hi := (15569/100000 : ℝ)) (c := (8068247013935019421/8070000000000000000 : ℝ)) (alpha := (45939403657/40350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8068247013935019421/8070000000000000000 : ℝ)*(X 0 2+X 1 2)+(45939403657/40350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (10727/100000 : ℝ)) (hi := (15569/100000 : ℝ)) (c := (8068247013935019421/8070000000000000000 : ℝ)) (alpha := (45939403657/40350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-476758181/2500000000 : ℝ)*X 0 0+(5437218637/10000000000 : ℝ)*X 0 1+(5215688603/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676573431/5000000000 : ℝ)*X 1 0+(-404112651/2000000000 : ℝ)*X 1 1+(325980681/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676574079/5000000000 : ℝ)*X 2 0+(2607844433/5000000000 : ℝ)*X 2 1+(-1010282107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((428198347/1000000000 : ℝ)*X 0 0+(4041567539/10000000000 : ℝ)*X 0 1+(283419509/625000000 : ℝ)*X 0 2+(428198347/1000000000 : ℝ)*X 1 0+(4041567539/10000000000 : ℝ)*X 1 1+(283419509/625000000 : ℝ)*X 1 2+(428198347/1000000000 : ℝ)*X 2 0+(4041567539/10000000000 : ℝ)*X 2 1+(283419509/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1907062743/10000000000 : ℝ)*X 0 0+(1043365931/2000000000 : ℝ)*X 0 1+(1359017387/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165476059/312500000 : ℝ)*X 1 0+(-900091811/5000000000 : ℝ)*X 1 1+(5436069347/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1059046703/2000000000 : ℝ)*X 2 0+(1087213931/2000000000 : ℝ)*X 2 1+(-450045927/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((856409903/2000000000 : ℝ)*X 0 0+(4532175251/10000000000 : ℝ)*X 0 1+(2022062551/5000000000 : ℝ)*X 0 2+(856409903/2000000000 : ℝ)*X 1 0+(4532175251/10000000000 : ℝ)*X 1 1+(2022062551/5000000000 : ℝ)*X 1 2+(856409903/2000000000 : ℝ)*X 2 0+(4532175251/10000000000 : ℝ)*X 2 1+(2022062551/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (449145781959380856443860809/67250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (395159277/25000000000000 : ℝ)*(base19) + (2245438507/100000000000000 : ℝ)*(base23) + (12692661/5000000000000 : ℝ)*(lower2) + (1033160809/100000000000000 : ℝ)*(upper3) + (12348897/50000000000000 : ℝ)*(lower4) + (1635493524054371/50000000000000 : ℝ)*(major0) + (1635493524054371/50000000000000 : ℝ)*(major1) + (1635493524054371/50000000000000 : ℝ)*(major2) + (141066071379013/3125000000000 : ℝ)*(sp0) + (1128536776425113/25000000000000 : ℝ)*(sp1) + (1128536610224763/25000000000000 : ℝ)*(sp2) + (1013903218937727/50000000000000 : ℝ)*(sp3) + (34402209143/100000000000000 : ℝ)*(sp4) + (18749379533/100000000000000 : ℝ)*(sp7) + (1013912593627493/50000000000000 : ℝ)*(f.failure) + (112853717158439/2500000000000 : ℝ)*(f.sum) + (7169350019741/2017500000000000000000000000 : ℝ)*base66 + (293968851194446397/134500000000000000000000000000000 : ℝ)*base67 + (436024952518446397/134500000000000000000000000000000 : ℝ)*base69 + (456992174784053603/134500000000000000000000000000000 : ℝ)*base72 + (583210675027/4035000000000000000000000000 : ℝ)*base74 + (719770889608446397/134500000000000000000000000000000 : ℝ)*base75 + (341586412408053603/134500000000000000000000000000000 : ℝ)*base78 + (1497026915756946397/134500000000000000000000000000000 : ℝ)*base79 + (14321686456751/2017500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (82313753/5000000000000000000000 : ℝ)*base90 + (82313753/5000000000000000000000 : ℝ)*base92 + (82313753/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7948778702745257167852153/1345000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (125460389/10000000000000 : ℝ)*(base19) + (1133296687/100000000000000 : ℝ)*(base23) + (62171011/50000000000000 : ℝ)*(upper3) + (14525337/12500000000000 : ℝ)*(lower4) + (14435889/6250000000000 : ℝ)*(upper5) + (33050901037969/1000000000000 : ℝ)*(major0) + (33050901037969/1000000000000 : ℝ)*(major1) + (33050901037969/1000000000000 : ℝ)*(major2) + (16179899329/100000000000000 : ℝ)*(sp1) + (7200088367/50000000000000 : ℝ)*(sp2) + (285075804762307/6250000000000 : ℝ)*(sp4) + (4561195441693693/100000000000000 : ℝ)*(sp5) + (4561197342723491/100000000000000 : ℝ)*(sp6) + (2048967134401121/100000000000000 : ℝ)*(sp7) + (2048967134401121/100000000000000 : ℝ)*(f.failure) + (285075804762307/6250000000000 : ℝ)*(f.sum) + (425453850773/807000000000000000000000000 : ℝ)*base66 + (22429812676941983/2690000000000000000000000000000 : ℝ)*base67 + (22942544465911983/2690000000000000000000000000000 : ℝ)*base69 + (21345343034401983/2690000000000000000000000000000 : ℝ)*base71 + (130124553031/80700000000000000000000000 : ℝ)*base73 + (46163965487401983/2690000000000000000000000000000 : ℝ)*base75 + (27785652654451983/2690000000000000000000000000000 : ℝ)*base77 + (21634154015531983/2690000000000000000000000000000 : ℝ)*base79 + (294270445727/403500000000000000000000000 : ℝ)*base81 + (119294341/10000000000000000000000 : ℝ)*base90 + (119294341/10000000000000000000000 : ℝ)*base92 + (119294341/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1486_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15569/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10727/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (27/250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1486_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1486_s5_0 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-4767781/25000000 : ℝ)*x 0 + (5436704449/10000000000 : ℝ)*x 1 + (5216150093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4767781/25000000 : ℝ)^4469 ≤ (11653962746087/100000000000000 : ℝ)^3445 := by
    have hnat : (4767781 : ℕ)^4469*100000000000000^3445 ≤ 11653962746087^3445*25000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4767781 25000000 11653962746087 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436704449/10000000000 : ℝ)^4469 ≤ (45359293886577/100000000000000 : ℝ)^3445 := by
    have hnat : (5436704449 : ℕ)^4469*100000000000000^3445 ≤ 45359293886577^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436704449 10000000000 45359293886577 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216150093/10000000000 : ℝ)^4469 ≤ (21493371674333/50000000000000 : ℝ)^3445 := by
    have hnat : (5216150093 : ℕ)^4469*50000000000000^3445 ≤ 21493371674333^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216150093 10000000000 21493371674333 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4767781/25000000 : ℝ), (5436704449/10000000000 : ℝ), (5216150093/10000000000 : ℝ)] ![(11653962746087/100000000000000 : ℝ), (45359293886577/100000000000000 : ℝ), (21493371674333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4767781/25000000 : ℝ)|^4469 ≤ (11653962746087/100000000000000 : ℝ)^3445
        have hw : |(-4767781/25000000 : ℝ)|=(4767781/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436704449/10000000000 : ℝ)|^4469 ≤ (45359293886577/100000000000000 : ℝ)^3445
        have hw : |(5436704449/10000000000 : ℝ)|=(5436704449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216150093/10000000000 : ℝ)|^4469 ≤ (21493371674333/50000000000000 : ℝ)^3445
        have hw : |(5216150093/10000000000 : ℝ)|=(5216150093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s5_1 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353013661/10000000000 : ℝ)*x 0 + (-505033119/2500000000 : ℝ)*x 1 + (16300469/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353013661/10000000000 : ℝ)^4469 ≤ (44455579900479/100000000000000 : ℝ)^3445 := by
    have hnat : (5353013661 : ℕ)^4469*100000000000000^3445 ≤ 44455579900479^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353013661 10000000000 44455579900479 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505033119/2500000000 : ℝ)^4469 ≤ (12557676873747/100000000000000 : ℝ)^3445 := by
    have hnat : (505033119 : ℕ)^4469*100000000000000^3445 ≤ 12557676873747^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505033119 2500000000 12557676873747 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16300469/31250000 : ℝ)^4469 ≤ (42986743209687/100000000000000 : ℝ)^3445 := by
    have hnat : (16300469 : ℕ)^4469*100000000000000^3445 ≤ 42986743209687^3445*31250000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16300469 31250000 42986743209687 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353013661/10000000000 : ℝ), (-505033119/2500000000 : ℝ), (16300469/31250000 : ℝ)] ![(44455579900479/100000000000000 : ℝ), (12557676873747/100000000000000 : ℝ), (42986743209687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353013661/10000000000 : ℝ)|^4469 ≤ (44455579900479/100000000000000 : ℝ)^3445
        have hw : |(5353013661/10000000000 : ℝ)|=(5353013661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-505033119/2500000000 : ℝ)|^4469 ≤ (12557676873747/100000000000000 : ℝ)^3445
        have hw : |(-505033119/2500000000 : ℝ)|=(505033119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16300469/31250000 : ℝ)|^4469 ≤ (42986743209687/100000000000000 : ℝ)^3445
        have hw : |(16300469/31250000 : ℝ)|=(16300469/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s5_2 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676506833/5000000000 : ℝ)*x 0 + (2608075041/5000000000 : ℝ)*x 1 + (-2020132467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676506833/5000000000 : ℝ)^4469 ≤ (22227789977173/50000000000000 : ℝ)^3445 := by
    have hnat : (2676506833 : ℕ)^4469*50000000000000^3445 ≤ 22227789977173^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676506833 5000000000 22227789977173 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608075041/5000000000 : ℝ)^4469 ≤ (42986743231069/100000000000000 : ℝ)^3445 := by
    have hnat : (2608075041 : ℕ)^4469*100000000000000^3445 ≤ 42986743231069^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608075041 5000000000 42986743231069 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2020132467/10000000000 : ℝ)^4469 ≤ (12557676801171/100000000000000 : ℝ)^3445 := by
    have hnat : (2020132467 : ℕ)^4469*100000000000000^3445 ≤ 12557676801171^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020132467 10000000000 12557676801171 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676506833/5000000000 : ℝ), (2608075041/5000000000 : ℝ), (-2020132467/10000000000 : ℝ)] ![(22227789977173/50000000000000 : ℝ), (42986743231069/100000000000000 : ℝ), (12557676801171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676506833/5000000000 : ℝ)|^4469 ≤ (22227789977173/50000000000000 : ℝ)^3445
        have hw : |(2676506833/5000000000 : ℝ)|=(2676506833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608075041/5000000000 : ℝ)|^4469 ≤ (42986743231069/100000000000000 : ℝ)^3445
        have hw : |(2608075041/5000000000 : ℝ)|=(2608075041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2020132467/10000000000 : ℝ)|^4469 ≤ (12557676801171/100000000000000 : ℝ)^3445
        have hw : |(-2020132467/10000000000 : ℝ)|=(2020132467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s5_3 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535253679/1250000000 : ℝ)*x 0 + (101066173/250000000 : ℝ)*x 1 + (4533623811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535253679/1250000000 : ℝ)^4469 ≤ (1331129487011/4000000000000 : ℝ)^3445 := by
    have hnat : (535253679 : ℕ)^4469*4000000000000^3445 ≤ 1331129487011^3445*1250000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535253679 1250000000 1331129487011 4000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (101066173/250000000 : ℝ)^4469 ≤ (30885186062271/100000000000000 : ℝ)^3445 := by
    have hnat : (101066173 : ℕ)^4469*100000000000000^3445 ≤ 30885186062271^3445*250000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101066173 250000000 30885186062271 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4533623811/10000000000 : ℝ)^4469 ≤ (17918288376301/50000000000000 : ℝ)^3445 := by
    have hnat : (4533623811 : ℕ)^4469*50000000000000^3445 ≤ 17918288376301^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533623811 10000000000 17918288376301 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535253679/1250000000 : ℝ), (101066173/250000000 : ℝ), (4533623811/10000000000 : ℝ)] ![(1331129487011/4000000000000 : ℝ), (30885186062271/100000000000000 : ℝ), (17918288376301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535253679/1250000000 : ℝ)|^4469 ≤ (1331129487011/4000000000000 : ℝ)^3445
        have hw : |(535253679/1250000000 : ℝ)|=(535253679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(101066173/250000000 : ℝ)|^4469 ≤ (30885186062271/100000000000000 : ℝ)^3445
        have hw : |(101066173/250000000 : ℝ)|=(101066173/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4533623811/10000000000 : ℝ)|^4469 ≤ (17918288376301/50000000000000 : ℝ)^3445
        have hw : |(4533623811/10000000000 : ℝ)|=(4533623811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s5_4 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1907142513/10000000000 : ℝ)*x 0 + (2608640121/5000000000 : ℝ)*x 1 + (2717783/5000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1907142513/10000000000 : ℝ)^4469 ≤ (5827100728839/50000000000000 : ℝ)^3445 := by
    have hnat : (1907142513 : ℕ)^4469*50000000000000^3445 ≤ 5827100728839^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1907142513 10000000000 5827100728839 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608640121/5000000000 : ℝ)^4469 ≤ (4299882580633/10000000000000 : ℝ)^3445 := by
    have hnat : (2608640121 : ℕ)^4469*10000000000000^3445 ≤ 4299882580633^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608640121 5000000000 4299882580633 10000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717783/5000000 : ℝ)^4469 ≤ (1813878908887/4000000000000 : ℝ)^3445 := by
    have hnat : (2717783 : ℕ)^4469*4000000000000^3445 ≤ 1813878908887^3445*5000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717783 5000000 1813878908887 4000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1907142513/10000000000 : ℝ), (2608640121/5000000000 : ℝ), (2717783/5000000 : ℝ)] ![(5827100728839/50000000000000 : ℝ), (4299882580633/10000000000000 : ℝ), (1813878908887/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1907142513/10000000000 : ℝ)|^4469 ≤ (5827100728839/50000000000000 : ℝ)^3445
        have hw : |(-1907142513/10000000000 : ℝ)|=(1907142513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608640121/5000000000 : ℝ)|^4469 ≤ (4299882580633/10000000000000 : ℝ)^3445
        have hw : |(2608640121/5000000000 : ℝ)|=(2608640121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717783/5000000 : ℝ)|^4469 ≤ (1813878908887/4000000000000 : ℝ)^3445
        have hw : |(2717783/5000000 : ℝ)|=(2717783/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s5_5 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295354467/10000000000 : ℝ)*x 0 + (-360143337/2000000000 : ℝ)*x 1 + (43484527/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295354467/10000000000 : ℝ)^4469 ≤ (43835396610401/100000000000000 : ℝ)^3445 := by
    have hnat : (5295354467 : ℕ)^4469*100000000000000^3445 ≤ 43835396610401^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295354467 10000000000 43835396610401 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (360143337/2000000000 : ℝ)^4469 ≤ (5408816005599/50000000000000 : ℝ)^3445 := by
    have hnat : (360143337 : ℕ)^4469*50000000000000^3445 ≤ 5408816005599^3445*2000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360143337 2000000000 5408816005599 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43484527/80000000 : ℝ)^4469 ≤ (11336742842343/25000000000000 : ℝ)^3445 := by
    have hnat : (43484527 : ℕ)^4469*25000000000000^3445 ≤ 11336742842343^3445*80000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43484527 80000000 11336742842343 25000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295354467/10000000000 : ℝ), (-360143337/2000000000 : ℝ), (43484527/80000000 : ℝ)] ![(43835396610401/100000000000000 : ℝ), (5408816005599/50000000000000 : ℝ), (11336742842343/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295354467/10000000000 : ℝ)|^4469 ≤ (43835396610401/100000000000000 : ℝ)^3445
        have hw : |(5295354467/10000000000 : ℝ)|=(5295354467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-360143337/2000000000 : ℝ)|^4469 ≤ (5408816005599/50000000000000 : ℝ)^3445
        have hw : |(-360143337/2000000000 : ℝ)|=(360143337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43484527/80000000 : ℝ)|^4469 ≤ (11336742842343/25000000000000 : ℝ)^3445
        have hw : |(43484527/80000000 : ℝ)|=(43484527/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s5_6 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323838603/2500000000 : ℝ)*x 0 + (5435565921/10000000000 : ℝ)*x 1 + (-225089587/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323838603/2500000000 : ℝ)^4469 ≤ (21917698009887/50000000000000 : ℝ)^3445 := by
    have hnat : (1323838603 : ℕ)^4469*50000000000000^3445 ≤ 21917698009887^3445*2500000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323838603 2500000000 21917698009887 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435565921/10000000000 : ℝ)^4469 ≤ (45346971867203/100000000000000 : ℝ)^3445 := by
    have hnat : (5435565921 : ℕ)^4469*100000000000000^3445 ≤ 45346971867203^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435565921 10000000000 45346971867203 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225089587/1250000000 : ℝ)^4469 ≤ (10817632096921/100000000000000 : ℝ)^3445 := by
    have hnat : (225089587 : ℕ)^4469*100000000000000^3445 ≤ 10817632096921^3445*1250000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225089587 1250000000 10817632096921 100000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323838603/2500000000 : ℝ), (5435565921/10000000000 : ℝ), (-225089587/1250000000 : ℝ)] ![(21917698009887/50000000000000 : ℝ), (45346971867203/100000000000000 : ℝ), (10817632096921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323838603/2500000000 : ℝ)|^4469 ≤ (21917698009887/50000000000000 : ℝ)^3445
        have hw : |(1323838603/2500000000 : ℝ)|=(1323838603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435565921/10000000000 : ℝ)|^4469 ≤ (45346971867203/100000000000000 : ℝ)^3445
        have hw : |(5435565921/10000000000 : ℝ)|=(5435565921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-225089587/1250000000 : ℝ)|^4469 ≤ (10817632096921/100000000000000 : ℝ)^3445
        have hw : |(-225089587/1250000000 : ℝ)|=(225089587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1486_s5_7 (p : ℝ) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2141048297/5000000000 : ℝ)*x 0 + (4531107821/10000000000 : ℝ)*x 1 + (505647667/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141048297/5000000000 : ℝ)^4469 ≤ (16639457140453/50000000000000 : ℝ)^3445 := by
    have hnat : (2141048297 : ℕ)^4469*50000000000000^3445 ≤ 16639457140453^3445*5000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141048297 5000000000 16639457140453 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4531107821/10000000000 : ℝ)^4469 ≤ (17905389696737/50000000000000 : ℝ)^3445 := by
    have hnat : (4531107821 : ℕ)^4469*50000000000000^3445 ≤ 17905389696737^3445*10000000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531107821 10000000000 17905389696737 50000000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (505647667/1250000000 : ℝ)^4469 ≤ (3863788288597/12500000000000 : ℝ)^3445 := by
    have hnat : (505647667 : ℕ)^4469*12500000000000^3445 ≤ 3863788288597^3445*1250000000^4469 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505647667 1250000000 3863788288597 12500000000000 4469 3445 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4469/1024 : ℝ)) 4469 3445 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2141048297/5000000000 : ℝ), (4531107821/10000000000 : ℝ), (505647667/1250000000 : ℝ)] ![(16639457140453/50000000000000 : ℝ), (17905389696737/50000000000000 : ℝ), (3863788288597/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2141048297/5000000000 : ℝ)|^4469 ≤ (16639457140453/50000000000000 : ℝ)^3445
        have hw : |(2141048297/5000000000 : ℝ)|=(2141048297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4531107821/10000000000 : ℝ)|^4469 ≤ (17905389696737/50000000000000 : ℝ)^3445
        have hw : |(4531107821/10000000000 : ℝ)|=(4531107821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(505647667/1250000000 : ℝ)|^4469 ≤ (3863788288597/12500000000000 : ℝ)^3445
        have hw : |(505647667/1250000000 : ℝ)|=(505647667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1486_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (27/250 : ℝ)*pair X i i ≤ pair X i h) :
    (1081/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7739/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (27/250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (27/250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (27/250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (27/250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (27/250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (27/250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (27/250 : ℝ) ^ (4467/1024 : ℝ) ≤ (3037175739006489/50000000000000000000 : ℝ) := by
    have hpowers : (27/250 : ℝ)^4467 ≤ (3037175739006489/50000000000000000000 : ℝ)^1024 := by
      have hnat : (27 : ℕ)^4467*50000000000000000000^1024 ≤ 3037175739006489^1024*250^4467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27 250 3037175739006489 50000000000000000000 4467 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27/250 : ℝ)) (X := (3037175739006489/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4467/1024 : ℝ) ≤ (7321080824272711/25000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4467 ≤ (7321080824272711/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4467*25000000000000000000^1024 ≤ 7321080824272711^1024*100000^4467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 7321080824272711 25000000000000000000 4467 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (7321080824272711/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003037175739006489/25000000000000000000 : ℝ) ≤ (500013923986377/500000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (25003037175739006489/25000000000000000000 : ℝ)^1024 ≤ (500013923986377/500000000000000 : ℝ)^4467 := by
      have hnat : (25003037175739006489 : ℕ)^1024*500000000000000^4467 ≤ 500013923986377^4467*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003037175739006489 25000000000000000000 500013923986377 500000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500013923986377/500000000000000 : ℝ)) (X := (25003037175739006489/25000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017679337387551911/50000000000000000000 : ℝ) ≤ (2500202609974159/2500000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (50017679337387551911/50000000000000000000 : ℝ)^1024 ≤ (2500202609974159/2500000000000000 : ℝ)^4467 := by
      have hnat : (50017679337387551911 : ℕ)^1024*2500000000000000^4467 ≤ 2500202609974159^4467*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017679337387551911 50000000000000000000 2500202609974159 2500000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500202609974159/2500000000000000 : ℝ)) (X := (50017679337387551911/50000000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507321080824272711/12500000000000000000 : ℝ) ≤ (2500335600016433/2500000000000000 : ℝ) ^ (4467/1024 : ℝ) := by
    have hpowers : (12507321080824272711/12500000000000000000 : ℝ)^1024 ≤ (2500335600016433/2500000000000000 : ℝ)^4467 := by
      have hnat : (12507321080824272711 : ℕ)^1024*2500000000000000^4467 ≤ 2500335600016433^4467*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507321080824272711 12500000000000000000 2500335600016433 2500000000000000 1024 4467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500335600016433/2500000000000000 : ℝ)) (X := (12507321080824272711/12500000000000000000 : ℝ)) (by norm_num) 4467 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3037175739006489/50000000000000000000 : ℝ) ≤ ((260443419176610897/260500000000000000 : ℝ)+2*(66495021137/58612500000000 : ℝ)*(27/250 : ℝ))^(4467/1024 : ℝ) := by
    rw [show (260443419176610897/260500000000000000 : ℝ)+2*(66495021137/58612500000000 : ℝ)*(27/250 : ℝ)=(500013923986377/500000000000000 : ℝ) by norm_num, show 1+2*(3037175739006489/50000000000000000000 : ℝ)=(25003037175739006489/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7321080824272711/25000000000000000000 : ℝ)+(3037175739006489/50000000000000000000 : ℝ) ≤ ((260443419176610897/260500000000000000 : ℝ)+(66495021137/58612500000000 : ℝ)*((15489/100000 : ℝ)+(27/250 : ℝ)))^(4467/1024 : ℝ) := by
    rw [show (260443419176610897/260500000000000000 : ℝ)+(66495021137/58612500000000 : ℝ)*((15489/100000 : ℝ)+(27/250 : ℝ))=(2500202609974159/2500000000000000 : ℝ) by norm_num, show 1+(7321080824272711/25000000000000000000 : ℝ)+(3037175739006489/50000000000000000000 : ℝ)=(50017679337387551911/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7321080824272711/25000000000000000000 : ℝ) ≤ ((260443419176610897/260500000000000000 : ℝ)+2*(66495021137/58612500000000 : ℝ)*(15489/100000 : ℝ))^(4467/1024 : ℝ) := by
    rw [show (260443419176610897/260500000000000000 : ℝ)+2*(66495021137/58612500000000 : ℝ)*(15489/100000 : ℝ)=(2500335600016433/2500000000000000 : ℝ) by norm_num, show 1+2*(7321080824272711/25000000000000000000 : ℝ)=(12507321080824272711/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (260443419176610897/260500000000000000 : ℝ)*(X 1 0+X 2 0)+(66495021137/58612500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (27/250 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (260443419176610897/260500000000000000 : ℝ)) (alpha := (66495021137/58612500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (260443419176610897/260500000000000000 : ℝ)*(X 0 1+X 2 1)+(66495021137/58612500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (27/250 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (260443419176610897/260500000000000000 : ℝ)) (alpha := (66495021137/58612500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (260443419176610897/260500000000000000 : ℝ)*(X 0 2+X 1 2)+(66495021137/58612500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4467/1024 : ℝ)) (lo := (27/250 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (260443419176610897/260500000000000000 : ℝ)) (alpha := (66495021137/58612500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-4767781/25000000 : ℝ)*X 0 0+(5436704449/10000000000 : ℝ)*X 0 1+(5216150093/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353013661/10000000000 : ℝ)*X 1 0+(-505033119/2500000000 : ℝ)*X 1 1+(16300469/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676506833/5000000000 : ℝ)*X 2 0+(2608075041/5000000000 : ℝ)*X 2 1+(-2020132467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((535253679/1250000000 : ℝ)*X 0 0+(101066173/250000000 : ℝ)*X 0 1+(4533623811/10000000000 : ℝ)*X 0 2+(535253679/1250000000 : ℝ)*X 1 0+(101066173/250000000 : ℝ)*X 1 1+(4533623811/10000000000 : ℝ)*X 1 2+(535253679/1250000000 : ℝ)*X 2 0+(101066173/250000000 : ℝ)*X 2 1+(4533623811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1907142513/10000000000 : ℝ)*X 0 0+(2608640121/5000000000 : ℝ)*X 0 1+(2717783/5000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295354467/10000000000 : ℝ)*X 1 0+(-360143337/2000000000 : ℝ)*X 1 1+(43484527/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323838603/2500000000 : ℝ)*X 2 0+(5435565921/10000000000 : ℝ)*X 2 1+(-225089587/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2141048297/5000000000 : ℝ)*X 0 0+(4531107821/10000000000 : ℝ)*X 0 1+(505647667/1250000000 : ℝ)*X 0 2+(2141048297/5000000000 : ℝ)*X 1 0+(4531107821/10000000000 : ℝ)*X 1 1+(505647667/1250000000 : ℝ)*X 1 2+(2141048297/5000000000 : ℝ)*X 2 0+(4531107821/10000000000 : ℝ)*X 2 1+(505647667/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1486_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5653626712437525647937887/781500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1283588297/100000000000000 : ℝ)*(base19) + (1194595729/100000000000000 : ℝ)*(base23) + (24952439/50000000000000 : ℝ)*(lower2) + (3528357/2000000000000 : ℝ)*(upper3) + (117049029/100000000000000 : ℝ)*(upper5) + (131416877834981/4000000000000 : ℝ)*(major0) + (131416877834981/4000000000000 : ℝ)*(major1) + (131416877834981/4000000000000 : ℝ)*(major2) + (2267024987173811/50000000000000 : ℝ)*(sp0) + (4534068367420047/100000000000000 : ℝ)*(sp1) + (906813691282523/20000000000000 : ℝ)*(sp2) + (407352871231197/20000000000000 : ℝ)*(sp3) + (9838330361/50000000000000 : ℝ)*(sp4) + (1205430059/12500000000000 : ℝ)*(sp7) + (2036773999596457/100000000000000 : ℝ)*(f.failure) + (566758706376043/12500000000000 : ℝ)*(f.sum) + (373935595399/2344500000000000000000000000 : ℝ)*base66 + (94485365335479613/9378000000000000000000000000000 : ℝ)*base67 + (63652399827177613/9378000000000000000000000000000 : ℝ)*base69 + (88556666499381613/9378000000000000000000000000000 : ℝ)*base71 + (842280487369/234450000000000000000000000 : ℝ)*base74 + (5785809360314387/9378000000000000000000000000000 : ℝ)*base76 + (140008739742687613/9378000000000000000000000000000 : ℝ)*base77 + (6988068019695613/9378000000000000000000000000000 : ℝ)*base79 + (7787250503539/2344500000000000000000000000 : ℝ)*base82 + (75849197/10000000000000000000000 : ℝ)*base90 + (75849197/10000000000000000000000 : ℝ)*base92 + (75849197/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2766430255083712615727193/814062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (253336013/50000000000000 : ℝ)*(base19) + (11175707/2000000000000 : ℝ)*(base23) + (1020241/2000000000000 : ℝ)*(upper3) + (25880367/50000000000000 : ℝ)*(lower4) + (46665947/50000000000000 : ℝ)*(upper5) + (414942168189573/12500000000000 : ℝ)*(major0) + (414942168189573/12500000000000 : ℝ)*(major1) + (414942168189573/12500000000000 : ℝ)*(major2) + (43791953/781250000000 : ℝ)*(sp1) + (2892125301/50000000000000 : ℝ)*(sp2) + (4581150978467291/100000000000000 : ℝ)*(sp4) + (4581144866425281/100000000000000 : ℝ)*(sp5) + (2290572317715669/50000000000000 : ℝ)*(sp6) + (128620224955571/6250000000000 : ℝ)*(sp7) + (128620224955571/6250000000000 : ℝ)*(f.failure) + (4581150978467291/100000000000000 : ℝ)*(f.sum) + (4577275815791/2605000000000000000000000000 : ℝ)*base65 + (6313798181100519/3256250000000000000000000000000 : ℝ)*base68 + (13762061780963019/3256250000000000000000000000000 : ℝ)*base70 + (21815949199831769/3256250000000000000000000000000 : ℝ)*base72 + (10171100980761/2605000000000000000000000000 : ℝ)*base73 + (20406044580931769/3256250000000000000000000000000 : ℝ)*base76 + (14976712310938019/3256250000000000000000000000000 : ℝ)*base78 + (3059261306149481/3256250000000000000000000000000 : ℝ)*base79 + (461318376037/1302500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2797791/625000000000000000000 : ℝ)*base90 + (2797791/625000000000000000000 : ℝ)*base92 + (2797791/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1486_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (27/250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1081/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1486_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1486_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2013/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2559/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1081/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1486_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1486_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1486_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4467/1024 : ℝ) ≤ p) (hpb : p ≤ (4469/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161305179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2013/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2559/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1081/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1486_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

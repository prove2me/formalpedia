-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1198_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:02:13.636032+00:00
-- url     : https://prove2.me/submissions/a04681f2-b23d-4d9f-b5fc-627f10c724a9

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
theorem support_rectangle_w1198_s3_0 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-534289929/2500000000 : ℝ)*x 0 + (2711826557/5000000000 : ℝ)*x 1 + (2618537897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534289929/2500000000 : ℝ)^8391 ≤ (6492735172297/50000000000000 : ℝ)^6343 := by
    have hnat : (534289929 : ℕ)^8391*50000000000000^6343 ≤ 6492735172297^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534289929 2500000000 6492735172297 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711826557/5000000000 : ℝ)^8391 ≤ (44514473563029/100000000000000 : ℝ)^6343 := by
    have hnat : (2711826557 : ℕ)^8391*100000000000000^6343 ≤ 44514473563029^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711826557 5000000000 44514473563029 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2618537897/5000000000 : ℝ)^8391 ≤ (1700002243327/4000000000000 : ℝ)^6343 := by
    have hnat : (2618537897 : ℕ)^8391*4000000000000^6343 ≤ 1700002243327^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618537897 5000000000 1700002243327 4000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-534289929/2500000000 : ℝ), (2711826557/5000000000 : ℝ), (2618537897/5000000000 : ℝ)] ![(6492735172297/50000000000000 : ℝ), (44514473563029/100000000000000 : ℝ), (1700002243327/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-534289929/2500000000 : ℝ)|^8391 ≤ (6492735172297/50000000000000 : ℝ)^6343
        have hw : |(-534289929/2500000000 : ℝ)|=(534289929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711826557/5000000000 : ℝ)|^8391 ≤ (44514473563029/100000000000000 : ℝ)^6343
        have hw : |(2711826557/5000000000 : ℝ)|=(2711826557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2618537897/5000000000 : ℝ)|^8391 ≤ (1700002243327/4000000000000 : ℝ)^6343
        have hw : |(2618537897/5000000000 : ℝ)|=(2618537897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s3_1 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352477541/10000000000 : ℝ)*x 0 + (-279052489/1250000000 : ℝ)*x 1 + (5237075969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352477541/10000000000 : ℝ)^8391 ≤ (349946636137/800000000000 : ℝ)^6343 := by
    have hnat : (5352477541 : ℕ)^8391*800000000000^6343 ≤ 349946636137^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352477541 10000000000 349946636137 800000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (279052489/1250000000 : ℝ)^8391 ≤ (6878306254139/50000000000000 : ℝ)^6343 := by
    have hnat : (279052489 : ℕ)^8391*50000000000000^6343 ≤ 6878306254139^6343*1250000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279052489 1250000000 6878306254139 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5237075969/10000000000 : ℝ)^8391 ≤ (10625014490469/25000000000000 : ℝ)^6343 := by
    have hnat : (5237075969 : ℕ)^8391*25000000000000^6343 ≤ 10625014490469^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237075969 10000000000 10625014490469 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352477541/10000000000 : ℝ), (-279052489/1250000000 : ℝ), (5237075969/10000000000 : ℝ)] ![(349946636137/800000000000 : ℝ), (6878306254139/50000000000000 : ℝ), (10625014490469/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352477541/10000000000 : ℝ)|^8391 ≤ (349946636137/800000000000 : ℝ)^6343
        have hw : |(5352477541/10000000000 : ℝ)|=(5352477541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-279052489/1250000000 : ℝ)|^8391 ≤ (6878306254139/50000000000000 : ℝ)^6343
        have hw : |(-279052489/1250000000 : ℝ)|=(279052489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5237075969/10000000000 : ℝ)|^8391 ≤ (10625014490469/25000000000000 : ℝ)^6343
        have hw : |(5237075969/10000000000 : ℝ)|=(5237075969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s3_2 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352477437/10000000000 : ℝ)*x 0 + (1047415239/2000000000 : ℝ)*x 1 + (-279052469/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352477437/10000000000 : ℝ)^8391 ≤ (21871664196377/50000000000000 : ℝ)^6343 := by
    have hnat : (5352477437 : ℕ)^8391*50000000000000^6343 ≤ 21871664196377^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352477437 10000000000 21871664196377 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047415239/2000000000 : ℝ)^8391 ≤ (10625015097021/25000000000000 : ℝ)^6343 := by
    have hnat : (1047415239 : ℕ)^8391*25000000000000^6343 ≤ 10625015097021^6343*2000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047415239 2000000000 10625015097021 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279052469/1250000000 : ℝ)^8391 ≤ (13756611203987/100000000000000 : ℝ)^6343 := by
    have hnat : (279052469 : ℕ)^8391*100000000000000^6343 ≤ 13756611203987^6343*1250000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279052469 1250000000 13756611203987 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352477437/10000000000 : ℝ), (1047415239/2000000000 : ℝ), (-279052469/1250000000 : ℝ)] ![(21871664196377/50000000000000 : ℝ), (10625015097021/25000000000000 : ℝ), (13756611203987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352477437/10000000000 : ℝ)|^8391 ≤ (21871664196377/50000000000000 : ℝ)^6343
        have hw : |(5352477437/10000000000 : ℝ)|=(5352477437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1047415239/2000000000 : ℝ)|^8391 ≤ (10625015097021/25000000000000 : ℝ)^6343
        have hw : |(1047415239/2000000000 : ℝ)|=(1047415239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-279052469/1250000000 : ℝ)|^8391 ≤ (13756611203987/100000000000000 : ℝ)^6343
        have hw : |(-279052469/1250000000 : ℝ)|=(279052469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s3_3 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (174196721/400000000 : ℝ)*x 0 + (834249571/2000000000 : ℝ)*x 1 + (2273259787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174196721/400000000 : ℝ)^8391 ≤ (520277988381/1562500000000 : ℝ)^6343 := by
    have hnat : (174196721 : ℕ)^8391*1562500000000^6343 ≤ 520277988381^6343*400000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174196721 400000000 520277988381 1562500000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834249571/2000000000 : ℝ)^8391 ≤ (1572639400807/5000000000000 : ℝ)^6343 := by
    have hnat : (834249571 : ℕ)^8391*5000000000000^6343 ≤ 1572639400807^6343*2000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834249571 2000000000 1572639400807 5000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273259787/5000000000 : ℝ)^8391 ≤ (35249420713949/100000000000000 : ℝ)^6343 := by
    have hnat : (2273259787 : ℕ)^8391*100000000000000^6343 ≤ 35249420713949^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273259787 5000000000 35249420713949 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174196721/400000000 : ℝ), (834249571/2000000000 : ℝ), (2273259787/5000000000 : ℝ)] ![(520277988381/1562500000000 : ℝ), (1572639400807/5000000000000 : ℝ), (35249420713949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174196721/400000000 : ℝ)|^8391 ≤ (520277988381/1562500000000 : ℝ)^6343
        have hw : |(174196721/400000000 : ℝ)|=(174196721/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(834249571/2000000000 : ℝ)|^8391 ≤ (1572639400807/5000000000000 : ℝ)^6343
        have hw : |(834249571/2000000000 : ℝ)|=(834249571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2273259787/5000000000 : ℝ)|^8391 ≤ (35249420713949/100000000000000 : ℝ)^6343
        have hw : |(2273259787/5000000000 : ℝ)|=(2273259787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s3_4 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-534293871/2500000000 : ℝ)*x 0 + (5237773133/10000000000 : ℝ)*x 1 + (5422951909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534293871/2500000000 : ℝ)^8391 ≤ (12985597085511/100000000000000 : ℝ)^6343 := by
    have hnat : (534293871 : ℕ)^8391*100000000000000^6343 ≤ 12985597085511^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534293871 2500000000 12985597085511 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237773133/10000000000 : ℝ)^8391 ≤ (42507542481719/100000000000000 : ℝ)^6343 := by
    have hnat : (5237773133 : ℕ)^8391*100000000000000^6343 ≤ 42507542481719^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237773133 10000000000 42507542481719 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422951909/10000000000 : ℝ)^8391 ≤ (44506860414801/100000000000000 : ℝ)^6343 := by
    have hnat : (5422951909 : ℕ)^8391*100000000000000^6343 ≤ 44506860414801^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422951909 10000000000 44506860414801 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-534293871/2500000000 : ℝ), (5237773133/10000000000 : ℝ), (5422951909/10000000000 : ℝ)] ![(12985597085511/100000000000000 : ℝ), (42507542481719/100000000000000 : ℝ), (44506860414801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-534293871/2500000000 : ℝ)|^8391 ≤ (12985597085511/100000000000000 : ℝ)^6343
        have hw : |(-534293871/2500000000 : ℝ)|=(534293871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237773133/10000000000 : ℝ)|^8391 ≤ (42507542481719/100000000000000 : ℝ)^6343
        have hw : |(5237773133/10000000000 : ℝ)|=(5237773133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422951909/10000000000 : ℝ)|^8391 ≤ (44506860414801/100000000000000 : ℝ)^6343
        have hw : |(5422951909/10000000000 : ℝ)|=(5422951909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s3_5 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5305020417/10000000000 : ℝ)*x 0 + (-102327179/500000000 : ℝ)*x 1 + (5422951833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305020417/10000000000 : ℝ)^8391 ≤ (8646198891517/20000000000000 : ℝ)^6343 := by
    have hnat : (5305020417 : ℕ)^8391*20000000000000^6343 ≤ 8646198891517^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305020417 10000000000 8646198891517 20000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102327179/500000000 : ℝ)^8391 ≤ (6131072970473/50000000000000 : ℝ)^6343 := by
    have hnat : (102327179 : ℕ)^8391*50000000000000^6343 ≤ 6131072970473^6343*500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102327179 500000000 6131072970473 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422951833/10000000000 : ℝ)^8391 ≤ (11126714897417/25000000000000 : ℝ)^6343 := by
    have hnat : (5422951833 : ℕ)^8391*25000000000000^6343 ≤ 11126714897417^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422951833 10000000000 11126714897417 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305020417/10000000000 : ℝ), (-102327179/500000000 : ℝ), (5422951833/10000000000 : ℝ)] ![(8646198891517/20000000000000 : ℝ), (6131072970473/50000000000000 : ℝ), (11126714897417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305020417/10000000000 : ℝ)|^8391 ≤ (8646198891517/20000000000000 : ℝ)^6343
        have hw : |(5305020417/10000000000 : ℝ)|=(5305020417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-102327179/500000000 : ℝ)|^8391 ≤ (6131072970473/50000000000000 : ℝ)^6343
        have hw : |(-102327179/500000000 : ℝ)|=(102327179/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422951833/10000000000 : ℝ)|^8391 ≤ (11126714897417/25000000000000 : ℝ)^6343
        have hw : |(5422951833/10000000000 : ℝ)|=(5422951833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s3_6 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5305020019/10000000000 : ℝ)*x 0 + (2711476129/5000000000 : ℝ)*x 1 + (-2046543539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305020019/10000000000 : ℝ)^8391 ≤ (21615495083531/50000000000000 : ℝ)^6343 := by
    have hnat : (5305020019 : ℕ)^8391*50000000000000^6343 ≤ 21615495083531^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305020019 10000000000 21615495083531 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711476129/5000000000 : ℝ)^8391 ≤ (44506864203897/100000000000000 : ℝ)^6343 := by
    have hnat : (2711476129 : ℕ)^8391*100000000000000^6343 ≤ 44506864203897^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711476129 5000000000 44506864203897 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2046543539/10000000000 : ℝ)^8391 ≤ (3065536403993/25000000000000 : ℝ)^6343 := by
    have hnat : (2046543539 : ℕ)^8391*25000000000000^6343 ≤ 3065536403993^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046543539 10000000000 3065536403993 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305020019/10000000000 : ℝ), (2711476129/5000000000 : ℝ), (-2046543539/10000000000 : ℝ)] ![(21615495083531/50000000000000 : ℝ), (44506864203897/100000000000000 : ℝ), (3065536403993/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305020019/10000000000 : ℝ)|^8391 ≤ (21615495083531/50000000000000 : ℝ)^6343
        have hw : |(5305020019/10000000000 : ℝ)|=(5305020019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711476129/5000000000 : ℝ)|^8391 ≤ (44506864203897/100000000000000 : ℝ)^6343
        have hw : |(2711476129/5000000000 : ℝ)|=(2711476129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2046543539/10000000000 : ℝ)|^8391 ≤ (3065536403993/25000000000000 : ℝ)^6343
        have hw : |(-2046543539/10000000000 : ℝ)|=(2046543539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s3_7 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (27218437/62500000 : ℝ)*x 0 + (1136279157/2500000000 : ℝ)*x 1 + (104316447/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27218437/62500000 : ℝ)^8391 ≤ (8324528466549/25000000000000 : ℝ)^6343 := by
    have hnat : (27218437 : ℕ)^8391*25000000000000^6343 ≤ 8324528466549^6343*62500000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27218437 62500000 8324528466549 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136279157/2500000000 : ℝ)^8391 ≤ (35235032355549/100000000000000 : ℝ)^6343 := by
    have hnat : (1136279157 : ℕ)^8391*100000000000000^6343 ≤ 35235032355549^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136279157 2500000000 35235032355549 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104316447/250000000 : ℝ)^8391 ≤ (31466853758939/100000000000000 : ℝ)^6343 := by
    have hnat : (104316447 : ℕ)^8391*100000000000000^6343 ≤ 31466853758939^6343*250000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104316447 250000000 31466853758939 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27218437/62500000 : ℝ), (1136279157/2500000000 : ℝ), (104316447/250000000 : ℝ)] ![(8324528466549/25000000000000 : ℝ), (35235032355549/100000000000000 : ℝ), (31466853758939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27218437/62500000 : ℝ)|^8391 ≤ (8324528466549/25000000000000 : ℝ)^6343
        have hw : |(27218437/62500000 : ℝ)|=(27218437/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1136279157/2500000000 : ℝ)|^8391 ≤ (35235032355549/100000000000000 : ℝ)^6343
        have hw : |(1136279157/2500000000 : ℝ)|=(1136279157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104316447/250000000 : ℝ)|^8391 ≤ (31466853758939/100000000000000 : ℝ)^6343
        have hw : |(104316447/250000000 : ℝ)|=(104316447/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1198_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16341/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2329/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2159/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14743/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16341/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2329/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16341/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2329/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16341/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2329/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16341/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2329/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16341/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2329/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16341/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2329/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2329/25000 : ℝ) ^ (4195/1024 : ℝ) ≤ (2993872850933229/50000000000000000000 : ℝ) := by
    have hpowers : (2329/25000 : ℝ)^4195 ≤ (2993872850933229/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2329 : ℕ)^4195*50000000000000000000^1024 ≤ 2993872850933229^1024*25000^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2329 25000 2993872850933229 50000000000000000000 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2329/25000 : ℝ)) (X := (2993872850933229/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16341/100000 : ℝ) ^ (4195/1024 : ℝ) ≤ (59848675529161791/100000000000000000000 : ℝ) := by
    have hpowers : (16341/100000 : ℝ)^4195 ≤ (59848675529161791/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16341 : ℕ)^4195*100000000000000000000^1024 ≤ 59848675529161791^1024*100000^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16341 100000 59848675529161791 100000000000000000000 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16341/100000 : ℝ)) (X := (59848675529161791/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002993872850933229/25000000000000000000 : ℝ) ≤ (10000292308657941/10000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (25002993872850933229/25000000000000000000 : ℝ)^1024 ≤ (10000292308657941/10000000000000000 : ℝ)^4195 := by
      have hnat : (25002993872850933229 : ℕ)^1024*10000000000000000^4195 ≤ 10000292308657941^4195*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002993872850933229 25000000000000000000 10000292308657941 10000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000292308657941/10000000000000000 : ℝ)) (X := (25002993872850933229/25000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100065836421231028249/100000000000000000000 : ℝ) ≤ (10001606668096351/10000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (100065836421231028249/100000000000000000000 : ℝ)^1024 ≤ (10001606668096351/10000000000000000 : ℝ)^4195 := by
      have hnat : (100065836421231028249 : ℕ)^1024*10000000000000000^4195 ≤ 10001606668096351^4195*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100065836421231028249 100000000000000000000 10001606668096351 10000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001606668096351/10000000000000000 : ℝ)) (X := (100065836421231028249/100000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50059848675529161791/50000000000000000000 : ℝ) ≤ (10002921027534761/10000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (50059848675529161791/50000000000000000000 : ℝ)^1024 ≤ (10002921027534761/10000000000000000 : ℝ)^4195 := by
      have hnat : (50059848675529161791 : ℕ)^1024*10000000000000000^4195 ≤ 10002921027534761^4195*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50059848675529161791 50000000000000000000 10002921027534761 10000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002921027534761/10000000000000000 : ℝ)) (X := (50059848675529161791/50000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2993872850933229/50000000000000000000 : ℝ) ≤ ((14045512864653116081/14050000000000000000 : ℝ)+2*(131435943841/70250000000000 : ℝ)*(2329/25000 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (14045512864653116081/14050000000000000000 : ℝ)+2*(131435943841/70250000000000 : ℝ)*(2329/25000 : ℝ)=(10000292308657941/10000000000000000 : ℝ) by norm_num, show 1+2*(2993872850933229/50000000000000000000 : ℝ)=(25002993872850933229/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(59848675529161791/100000000000000000000 : ℝ)+(2993872850933229/50000000000000000000 : ℝ) ≤ ((14045512864653116081/14050000000000000000 : ℝ)+(131435943841/70250000000000 : ℝ)*((16341/100000 : ℝ)+(2329/25000 : ℝ)))^(4195/1024 : ℝ) := by
    rw [show (14045512864653116081/14050000000000000000 : ℝ)+(131435943841/70250000000000 : ℝ)*((16341/100000 : ℝ)+(2329/25000 : ℝ))=(10001606668096351/10000000000000000 : ℝ) by norm_num, show 1+(59848675529161791/100000000000000000000 : ℝ)+(2993872850933229/50000000000000000000 : ℝ)=(100065836421231028249/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(59848675529161791/100000000000000000000 : ℝ) ≤ ((14045512864653116081/14050000000000000000 : ℝ)+2*(131435943841/70250000000000 : ℝ)*(16341/100000 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (14045512864653116081/14050000000000000000 : ℝ)+2*(131435943841/70250000000000 : ℝ)*(16341/100000 : ℝ)=(10002921027534761/10000000000000000 : ℝ) by norm_num, show 1+2*(59848675529161791/100000000000000000000 : ℝ)=(50059848675529161791/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14045512864653116081/14050000000000000000 : ℝ)*(X 1 0+X 2 0)+(131435943841/70250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (2329/25000 : ℝ)) (hi := (16341/100000 : ℝ)) (c := (14045512864653116081/14050000000000000000 : ℝ)) (alpha := (131435943841/70250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14045512864653116081/14050000000000000000 : ℝ)*(X 0 1+X 2 1)+(131435943841/70250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (2329/25000 : ℝ)) (hi := (16341/100000 : ℝ)) (c := (14045512864653116081/14050000000000000000 : ℝ)) (alpha := (131435943841/70250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14045512864653116081/14050000000000000000 : ℝ)*(X 0 2+X 1 2)+(131435943841/70250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (2329/25000 : ℝ)) (hi := (16341/100000 : ℝ)) (c := (14045512864653116081/14050000000000000000 : ℝ)) (alpha := (131435943841/70250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-534289929/2500000000 : ℝ)*X 0 0+(2711826557/5000000000 : ℝ)*X 0 1+(2618537897/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352477541/10000000000 : ℝ)*X 1 0+(-279052489/1250000000 : ℝ)*X 1 1+(5237075969/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352477437/10000000000 : ℝ)*X 2 0+(1047415239/2000000000 : ℝ)*X 2 1+(-279052469/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((174196721/400000000 : ℝ)*X 0 0+(834249571/2000000000 : ℝ)*X 0 1+(2273259787/5000000000 : ℝ)*X 0 2+(174196721/400000000 : ℝ)*X 1 0+(834249571/2000000000 : ℝ)*X 1 1+(2273259787/5000000000 : ℝ)*X 1 2+(174196721/400000000 : ℝ)*X 2 0+(834249571/2000000000 : ℝ)*X 2 1+(2273259787/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-534293871/2500000000 : ℝ)*X 0 0+(5237773133/10000000000 : ℝ)*X 0 1+(5422951909/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305020417/10000000000 : ℝ)*X 1 0+(-102327179/500000000 : ℝ)*X 1 1+(5422951833/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305020019/10000000000 : ℝ)*X 2 0+(2711476129/5000000000 : ℝ)*X 2 1+(-2046543539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((27218437/62500000 : ℝ)*X 0 0+(1136279157/2500000000 : ℝ)*X 0 1+(104316447/250000000 : ℝ)*X 0 2+(27218437/62500000 : ℝ)*X 1 0+(1136279157/2500000000 : ℝ)*X 1 1+(104316447/250000000 : ℝ)*X 1 2+(27218437/62500000 : ℝ)*X 2 0+(1136279157/2500000000 : ℝ)*X 2 1+(104316447/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11632208082797463590546307/2810000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (460318519/100000000000000 : ℝ)*(base19) + (24304989/10000000000000 : ℝ)*(base23) + (12110253/20000000000000 : ℝ)*(lower2) + (43133/2500000000000 : ℝ)*(upper3) + (37045247/50000000000000 : ℝ)*(upper5) + (16048971423151/400000000000 : ℝ)*(major0) + (16048971423151/400000000000 : ℝ)*(major1) + (16048971423151/400000000000 : ℝ)*(major2) + (535972193350691/10000000000000 : ℝ)*(sp0) + (1339934555445089/25000000000000 : ℝ)*(sp1) + (1071947687809797/20000000000000 : ℝ)*(sp2) + (2664741815408661/100000000000000 : ℝ)*(sp3) + (3349718393/20000000000000 : ℝ)*(sp4) + (2538041047/50000000000000 : ℝ)*(sp7) + (666186722872689/25000000000000 : ℝ)*(f.failure) + (42877909456791/800000000000 : ℝ)*(f.sum) + (137829802273/56200000000000000000000000 : ℝ)*base66 + (42608107943351231/5620000000000000000000000000000 : ℝ)*base67 + (40079368784411231/5620000000000000000000000000000 : ℝ)*base69 + (26382485625628769/5620000000000000000000000000000 : ℝ)*base72 + (260034774621/56200000000000000000000000 : ℝ)*base73 + (44281345901231231/5620000000000000000000000000000 : ℝ)*base75 + (79352485317008769/5620000000000000000000000000000 : ℝ)*base78 + (73160012839551231/5620000000000000000000000000000 : ℝ)*base79 + (82495472243/140500000000000000000000000 : ℝ)*base81 + (19625567/2500000000000000000000 : ℝ)*base89 + (19625567/2500000000000000000000 : ℝ)*base91 + (19625567/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (151597354706725976862631779/87812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1155339493/100000000000000 : ℝ)*(base19) + (914754673/100000000000000 : ℝ)*(base23) + (983587/4000000000000 : ℝ)*(upper3) + (18388167/20000000000000 : ℝ)*(lower4) + (42041623/25000000000000 : ℝ)*(upper5) + (1010630534410647/25000000000000 : ℝ)*(major0) + (1010630534410647/25000000000000 : ℝ)*(major1) + (1010630534410647/25000000000000 : ℝ)*(major2) + (24918423637/100000000000000 : ℝ)*(sp1) + (2992459329/12500000000000 : ℝ)*(sp2) + (2700093610987687/50000000000000 : ℝ)*(sp4) + (1350040287053061/25000000000000 : ℝ)*(sp5) + (5400162367546069/100000000000000 : ℝ)*(sp6) + (536971399152789/20000000000000 : ℝ)*(sp7) + (536971399152789/20000000000000 : ℝ)*(f.failure) + (2700093610987687/50000000000000 : ℝ)*(f.sum) + (437217797763/219531250000000000000000000 : ℝ)*base65 + (501577519486214407/351250000000000000000000000000000 : ℝ)*base67 + (2248160640381214407/351250000000000000000000000000000 : ℝ)*base69 + (4343426181732464407/351250000000000000000000000000000 : ℝ)*base71 + (5993771317721/1756250000000000000000000000 : ℝ)*base74 + (134309640192535593/351250000000000000000000000000000 : ℝ)*base76 + (1808942772319964407/351250000000000000000000000000000 : ℝ)*base77 + (160748299111214407/351250000000000000000000000000000 : ℝ)*base79 + (22806615607391/7025000000000000000000000000 : ℝ)*base81 + (4784133/2000000000000000000000 : ℝ)*base90 + (4784133/2000000000000000000000 : ℝ)*base92 + (4784133/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1198_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16341/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2329/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2159/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1198_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1198_s4_0 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139740121/10000000000 : ℝ)*x 0 + (5399331003/10000000000 : ℝ)*x 1 + (1314927097/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139740121/10000000000 : ℝ)^8391 ≤ (13006215285933/100000000000000 : ℝ)^6343 := by
    have hnat : (2139740121 : ℕ)^8391*100000000000000^6343 ≤ 13006215285933^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139740121 10000000000 13006215285933 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399331003/10000000000 : ℝ)^8391 ≤ (22125294262297/50000000000000 : ℝ)^6343 := by
    have hnat : (5399331003 : ℕ)^8391*50000000000000^6343 ≤ 22125294262297^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399331003 10000000000 22125294262297 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314927097/2500000000 : ℝ)^8391 ≤ (42743196177351/100000000000000 : ℝ)^6343 := by
    have hnat : (1314927097 : ℕ)^8391*100000000000000^6343 ≤ 42743196177351^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314927097 2500000000 42743196177351 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139740121/10000000000 : ℝ), (5399331003/10000000000 : ℝ), (1314927097/2500000000 : ℝ)] ![(13006215285933/100000000000000 : ℝ), (22125294262297/50000000000000 : ℝ), (42743196177351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139740121/10000000000 : ℝ)|^8391 ≤ (13006215285933/100000000000000 : ℝ)^6343
        have hw : |(-2139740121/10000000000 : ℝ)|=(2139740121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399331003/10000000000 : ℝ)|^8391 ≤ (22125294262297/50000000000000 : ℝ)^6343
        have hw : |(5399331003/10000000000 : ℝ)|=(5399331003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1314927097/2500000000 : ℝ)|^8391 ≤ (42743196177351/100000000000000 : ℝ)^6343
        have hw : |(1314927097/2500000000 : ℝ)|=(1314927097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s4_1 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346371491/10000000000 : ℝ)*x 0 + (-1105327893/5000000000 : ℝ)*x 1 + (657463561/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346371491/10000000000 : ℝ)^8391 ≤ (43677327632289/100000000000000 : ℝ)^6343 := by
    have hnat : (5346371491 : ℕ)^8391*100000000000000^6343 ≤ 43677327632289^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346371491 10000000000 43677327632289 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105327893/5000000000 : ℝ)^8391 ≤ (3394868775507/25000000000000 : ℝ)^6343 := by
    have hnat : (1105327893 : ℕ)^8391*25000000000000^6343 ≤ 3394868775507^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105327893 5000000000 3394868775507 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657463561/1250000000 : ℝ)^8391 ≤ (42743197252391/100000000000000 : ℝ)^6343 := by
    have hnat : (657463561 : ℕ)^8391*100000000000000^6343 ≤ 42743197252391^6343*1250000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657463561 1250000000 42743197252391 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346371491/10000000000 : ℝ), (-1105327893/5000000000 : ℝ), (657463561/1250000000 : ℝ)] ![(43677327632289/100000000000000 : ℝ), (3394868775507/25000000000000 : ℝ), (42743197252391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346371491/10000000000 : ℝ)|^8391 ≤ (43677327632289/100000000000000 : ℝ)^6343
        have hw : |(5346371491/10000000000 : ℝ)|=(5346371491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1105327893/5000000000 : ℝ)|^8391 ≤ (3394868775507/25000000000000 : ℝ)^6343
        have hw : |(-1105327893/5000000000 : ℝ)|=(1105327893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657463561/1250000000 : ℝ)|^8391 ≤ (42743197252391/100000000000000 : ℝ)^6343
        have hw : |(657463561/1250000000 : ℝ)|=(657463561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s4_2 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346371457/10000000000 : ℝ)*x 0 + (2629854181/5000000000 : ℝ)*x 1 + (-1105327999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346371457/10000000000 : ℝ)^8391 ≤ (21838663632421/50000000000000 : ℝ)^6343 := by
    have hnat : (5346371457 : ℕ)^8391*50000000000000^6343 ≤ 21838663632421^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346371457 10000000000 21838663632421 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629854181/5000000000 : ℝ)^8391 ≤ (42743195897841/100000000000000 : ℝ)^6343 := by
    have hnat : (2629854181 : ℕ)^8391*100000000000000^6343 ≤ 42743195897841^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629854181 5000000000 42743195897841 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105327999/5000000000 : ℝ)^8391 ≤ (3394869206189/25000000000000 : ℝ)^6343 := by
    have hnat : (1105327999 : ℕ)^8391*25000000000000^6343 ≤ 3394869206189^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105327999 5000000000 3394869206189 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346371457/10000000000 : ℝ), (2629854181/5000000000 : ℝ), (-1105327999/5000000000 : ℝ)] ![(21838663632421/50000000000000 : ℝ), (42743195897841/100000000000000 : ℝ), (3394869206189/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346371457/10000000000 : ℝ)|^8391 ≤ (21838663632421/50000000000000 : ℝ)^6343
        have hw : |(5346371457/10000000000 : ℝ)|=(5346371457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629854181/5000000000 : ℝ)|^8391 ≤ (42743195897841/100000000000000 : ℝ)^6343
        have hw : |(2629854181/5000000000 : ℝ)|=(2629854181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1105327999/5000000000 : ℝ)|^8391 ≤ (3394869206189/25000000000000 : ℝ)^6343
        have hw : |(-1105327999/5000000000 : ℝ)|=(1105327999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s4_3 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4356463173/10000000000 : ℝ)*x 0 + (263641879/625000000 : ℝ)*x 1 + (44991003/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356463173/10000000000 : ℝ)^8391 ≤ (33313420912003/100000000000000 : ℝ)^6343 := by
    have hnat : (4356463173 : ℕ)^8391*100000000000000^6343 ≤ 33313420912003^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356463173 10000000000 33313420912003 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263641879/625000000 : ℝ)^8391 ≤ (31922685192679/100000000000000 : ℝ)^6343 := by
    have hnat : (263641879 : ℕ)^8391*100000000000000^6343 ≤ 31922685192679^6343*625000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263641879 625000000 31922685192679 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44991003/100000000 : ℝ)^8391 ≤ (34763893886141/100000000000000 : ℝ)^6343 := by
    have hnat : (44991003 : ℕ)^8391*100000000000000^6343 ≤ 34763893886141^6343*100000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44991003 100000000 34763893886141 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356463173/10000000000 : ℝ), (263641879/625000000 : ℝ), (44991003/100000000 : ℝ)] ![(33313420912003/100000000000000 : ℝ), (31922685192679/100000000000000 : ℝ), (34763893886141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356463173/10000000000 : ℝ)|^8391 ≤ (33313420912003/100000000000000 : ℝ)^6343
        have hw : |(4356463173/10000000000 : ℝ)|=(4356463173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263641879/625000000 : ℝ)|^8391 ≤ (31922685192679/100000000000000 : ℝ)^6343
        have hw : |(263641879/625000000 : ℝ)|=(263641879/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(44991003/100000000 : ℝ)|^8391 ≤ (34763893886141/100000000000000 : ℝ)^6343
        have hw : |(44991003/100000000 : ℝ)|=(44991003/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s4_4 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139746437/10000000000 : ℝ)*x 0 + (5260099459/10000000000 : ℝ)*x 1 + (5398938533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139746437/10000000000 : ℝ)^8391 ≤ (650313303639/5000000000000 : ℝ)^6343 := by
    have hnat : (2139746437 : ℕ)^8391*5000000000000^6343 ≤ 650313303639^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139746437 10000000000 650313303639 5000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260099459/10000000000 : ℝ)^8391 ≤ (42747400394719/100000000000000 : ℝ)^6343 := by
    have hnat : (5260099459 : ℕ)^8391*100000000000000^6343 ≤ 42747400394719^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260099459 10000000000 42747400394719 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398938533/10000000000 : ℝ)^8391 ≤ (5530791690681/12500000000000 : ℝ)^6343 := by
    have hnat : (5398938533 : ℕ)^8391*12500000000000^6343 ≤ 5530791690681^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398938533 10000000000 5530791690681 12500000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139746437/10000000000 : ℝ), (5260099459/10000000000 : ℝ), (5398938533/10000000000 : ℝ)] ![(650313303639/5000000000000 : ℝ), (42747400394719/100000000000000 : ℝ), (5530791690681/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139746437/10000000000 : ℝ)|^8391 ≤ (650313303639/5000000000000 : ℝ)^6343
        have hw : |(-2139746437/10000000000 : ℝ)|=(2139746437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260099459/10000000000 : ℝ)|^8391 ≤ (42747400394719/100000000000000 : ℝ)^6343
        have hw : |(5260099459/10000000000 : ℝ)|=(5260099459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398938533/10000000000 : ℝ)|^8391 ≤ (5530791690681/12500000000000 : ℝ)^6343
        have hw : |(5398938533/10000000000 : ℝ)|=(5398938533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s4_5 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655427933/5000000000 : ℝ)*x 0 + (-2071426531/10000000000 : ℝ)*x 1 + (2699469011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655427933/5000000000 : ℝ)^8391 ≤ (5411739123123/12500000000000 : ℝ)^6343 := by
    have hnat : (2655427933 : ℕ)^8391*12500000000000^6343 ≤ 5411739123123^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655427933 5000000000 5411739123123 12500000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071426531/10000000000 : ℝ)^8391 ≤ (12459759014101/100000000000000 : ℝ)^6343 := by
    have hnat : (2071426531 : ℕ)^8391*100000000000000^6343 ≤ 12459759014101^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071426531 10000000000 12459759014101 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699469011/5000000000 : ℝ)^8391 ≤ (2212316399273/5000000000000 : ℝ)^6343 := by
    have hnat : (2699469011 : ℕ)^8391*5000000000000^6343 ≤ 2212316399273^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699469011 5000000000 2212316399273 5000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655427933/5000000000 : ℝ), (-2071426531/10000000000 : ℝ), (2699469011/5000000000 : ℝ)] ![(5411739123123/12500000000000 : ℝ), (12459759014101/100000000000000 : ℝ), (2212316399273/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655427933/5000000000 : ℝ)|^8391 ≤ (5411739123123/12500000000000 : ℝ)^6343
        have hw : |(2655427933/5000000000 : ℝ)|=(2655427933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2071426531/10000000000 : ℝ)|^8391 ≤ (12459759014101/100000000000000 : ℝ)^6343
        have hw : |(-2071426531/10000000000 : ℝ)|=(2071426531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699469011/5000000000 : ℝ)|^8391 ≤ (2212316399273/5000000000000 : ℝ)^6343
        have hw : |(2699469011/5000000000 : ℝ)|=(2699469011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s4_6 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310855721/10000000000 : ℝ)*x 0 + (337433659/625000000 : ℝ)*x 1 + (-64732063/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310855721/10000000000 : ℝ)^8391 ≤ (43293911421299/100000000000000 : ℝ)^6343 := by
    have hnat : (5310855721 : ℕ)^8391*100000000000000^6343 ≤ 43293911421299^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310855721 10000000000 43293911421299 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337433659/625000000 : ℝ)^8391 ≤ (1382697926397/3125000000000 : ℝ)^6343 := by
    have hnat : (337433659 : ℕ)^8391*3125000000000^6343 ≤ 1382697926397^6343*625000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337433659 625000000 1382697926397 3125000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64732063/312500000 : ℝ)^8391 ≤ (6229877458077/50000000000000 : ℝ)^6343 := by
    have hnat : (64732063 : ℕ)^8391*50000000000000^6343 ≤ 6229877458077^6343*312500000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64732063 312500000 6229877458077 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310855721/10000000000 : ℝ), (337433659/625000000 : ℝ), (-64732063/312500000 : ℝ)] ![(43293911421299/100000000000000 : ℝ), (1382697926397/3125000000000 : ℝ), (6229877458077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310855721/10000000000 : ℝ)|^8391 ≤ (43293911421299/100000000000000 : ℝ)^6343
        have hw : |(5310855721/10000000000 : ℝ)|=(5310855721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337433659/625000000 : ℝ)|^8391 ≤ (1382697926397/3125000000000 : ℝ)^6343
        have hw : |(337433659/625000000 : ℝ)|=(337433659/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64732063/312500000 : ℝ)|^8391 ≤ (6229877458077/50000000000000 : ℝ)^6343
        have hw : |(-64732063/312500000 : ℝ)|=(64732063/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s4_7 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089119187/2500000000 : ℝ)*x 0 + (449831367/1000000000 : ℝ)*x 1 + (263691217/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089119187/2500000000 : ℝ)^8391 ≤ (33313558235309/100000000000000 : ℝ)^6343 := by
    have hnat : (1089119187 : ℕ)^8391*100000000000000^6343 ≤ 33313558235309^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089119187 2500000000 33313558235309 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449831367/1000000000 : ℝ)^8391 ≤ (34755853442793/100000000000000 : ℝ)^6343 := by
    have hnat : (449831367 : ℕ)^8391*100000000000000^6343 ≤ 34755853442793^6343*1000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449831367 1000000000 34755853442793 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263691217/625000000 : ℝ)^8391 ≤ (31930588314697/100000000000000 : ℝ)^6343 := by
    have hnat : (263691217 : ℕ)^8391*100000000000000^6343 ≤ 31930588314697^6343*625000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263691217 625000000 31930588314697 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089119187/2500000000 : ℝ), (449831367/1000000000 : ℝ), (263691217/625000000 : ℝ)] ![(33313558235309/100000000000000 : ℝ), (34755853442793/100000000000000 : ℝ), (31930588314697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089119187/2500000000 : ℝ)|^8391 ≤ (33313558235309/100000000000000 : ℝ)^6343
        have hw : |(1089119187/2500000000 : ℝ)|=(1089119187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(449831367/1000000000 : ℝ)|^8391 ≤ (34755853442793/100000000000000 : ℝ)^6343
        have hw : |(449831367/1000000000 : ℝ)|=(449831367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263691217/625000000 : ℝ)|^8391 ≤ (31930588314697/100000000000000 : ℝ)^6343
        have hw : |(263691217/625000000 : ℝ)|=(263691217/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1198_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2159/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11277/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2159/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2159/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2159/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2159/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2159/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2159/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2159/20000 : ℝ) ^ (4195/1024 : ℝ) ≤ (5475110121521531/50000000000000000000 : ℝ) := by
    have hpowers : (2159/20000 : ℝ)^4195 ≤ (5475110121521531/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2159 : ℕ)^4195*50000000000000000000^1024 ≤ 5475110121521531^1024*20000^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2159 20000 5475110121521531 50000000000000000000 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2159/20000 : ℝ)) (X := (5475110121521531/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14743/100000 : ℝ) ^ (4195/1024 : ℝ) ≤ (7852222533769421/20000000000000000000 : ℝ) := by
    have hpowers : (14743/100000 : ℝ)^4195 ≤ (7852222533769421/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14743 : ℕ)^4195*20000000000000000000^1024 ≤ 7852222533769421^1024*100000^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14743 100000 7852222533769421 20000000000000000000 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14743/100000 : ℝ)) (X := (7852222533769421/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005475110121521531/25000000000000000000 : ℝ) ≤ (2500133636442377/2500000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (25005475110121521531/25000000000000000000 : ℝ)^1024 ≤ (2500133636442377/2500000000000000 : ℝ)^4195 := by
      have hnat : (25005475110121521531 : ℕ)^1024*2500000000000000^4195 ≤ 2500133636442377^4195*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005475110121521531 25000000000000000000 2500133636442377 2500000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500133636442377/2500000000000000 : ℝ)) (X := (25005475110121521531/25000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050211332911890167/100000000000000000000 : ℝ) ≤ (10001225426705289/10000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (100050211332911890167/100000000000000000000 : ℝ)^1024 ≤ (10001225426705289/10000000000000000 : ℝ)^4195 := by
      have hnat : (100050211332911890167 : ℕ)^1024*10000000000000000^4195 ≤ 10001225426705289^4195*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050211332911890167 100000000000000000000 10001225426705289 10000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001225426705289/10000000000000000 : ℝ)) (X := (100050211332911890167/100000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007852222533769421/10000000000000000000 : ℝ) ≤ (1000191630764107/1000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (10007852222533769421/10000000000000000000 : ℝ)^1024 ≤ (1000191630764107/1000000000000000 : ℝ)^4195 := by
      have hnat : (10007852222533769421 : ℕ)^1024*1000000000000000^4195 ≤ 1000191630764107^4195*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007852222533769421 10000000000000000000 1000191630764107 1000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000191630764107/1000000000000000 : ℝ)) (X := (10007852222533769421/10000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5475110121521531/50000000000000000000 : ℝ) ≤ ((19733597133647252897/19740000000000000000 : ℝ)+2*(690880935781/394800000000000 : ℝ)*(2159/20000 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (19733597133647252897/19740000000000000000 : ℝ)+2*(690880935781/394800000000000 : ℝ)*(2159/20000 : ℝ)=(2500133636442377/2500000000000000 : ℝ) by norm_num, show 1+2*(5475110121521531/50000000000000000000 : ℝ)=(25005475110121521531/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7852222533769421/20000000000000000000 : ℝ)+(5475110121521531/50000000000000000000 : ℝ) ≤ ((19733597133647252897/19740000000000000000 : ℝ)+(690880935781/394800000000000 : ℝ)*((14743/100000 : ℝ)+(2159/20000 : ℝ)))^(4195/1024 : ℝ) := by
    rw [show (19733597133647252897/19740000000000000000 : ℝ)+(690880935781/394800000000000 : ℝ)*((14743/100000 : ℝ)+(2159/20000 : ℝ))=(10001225426705289/10000000000000000 : ℝ) by norm_num, show 1+(7852222533769421/20000000000000000000 : ℝ)+(5475110121521531/50000000000000000000 : ℝ)=(100050211332911890167/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7852222533769421/20000000000000000000 : ℝ) ≤ ((19733597133647252897/19740000000000000000 : ℝ)+2*(690880935781/394800000000000 : ℝ)*(14743/100000 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (19733597133647252897/19740000000000000000 : ℝ)+2*(690880935781/394800000000000 : ℝ)*(14743/100000 : ℝ)=(1000191630764107/1000000000000000 : ℝ) by norm_num, show 1+2*(7852222533769421/20000000000000000000 : ℝ)=(10007852222533769421/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19733597133647252897/19740000000000000000 : ℝ)*(X 1 0+X 2 0)+(690880935781/394800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (2159/20000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (19733597133647252897/19740000000000000000 : ℝ)) (alpha := (690880935781/394800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19733597133647252897/19740000000000000000 : ℝ)*(X 0 1+X 2 1)+(690880935781/394800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (2159/20000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (19733597133647252897/19740000000000000000 : ℝ)) (alpha := (690880935781/394800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19733597133647252897/19740000000000000000 : ℝ)*(X 0 2+X 1 2)+(690880935781/394800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (2159/20000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (19733597133647252897/19740000000000000000 : ℝ)) (alpha := (690880935781/394800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2139740121/10000000000 : ℝ)*X 0 0+(5399331003/10000000000 : ℝ)*X 0 1+(1314927097/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346371491/10000000000 : ℝ)*X 1 0+(-1105327893/5000000000 : ℝ)*X 1 1+(657463561/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346371457/10000000000 : ℝ)*X 2 0+(2629854181/5000000000 : ℝ)*X 2 1+(-1105327999/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4356463173/10000000000 : ℝ)*X 0 0+(263641879/625000000 : ℝ)*X 0 1+(44991003/100000000 : ℝ)*X 0 2+(4356463173/10000000000 : ℝ)*X 1 0+(263641879/625000000 : ℝ)*X 1 1+(44991003/100000000 : ℝ)*X 1 2+(4356463173/10000000000 : ℝ)*X 2 0+(263641879/625000000 : ℝ)*X 2 1+(44991003/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2139746437/10000000000 : ℝ)*X 0 0+(5260099459/10000000000 : ℝ)*X 0 1+(5398938533/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655427933/5000000000 : ℝ)*X 1 0+(-2071426531/10000000000 : ℝ)*X 1 1+(2699469011/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310855721/10000000000 : ℝ)*X 2 0+(337433659/625000000 : ℝ)*X 2 1+(-64732063/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089119187/2500000000 : ℝ)*X 0 0+(449831367/1000000000 : ℝ)*X 0 1+(263691217/625000000 : ℝ)*X 0 2+(1089119187/2500000000 : ℝ)*X 1 0+(449831367/1000000000 : ℝ)*X 1 1+(263691217/625000000 : ℝ)*X 1 2+(1089119187/2500000000 : ℝ)*X 2 0+(449831367/1000000000 : ℝ)*X 2 1+(263691217/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1604540279724588562703878203/164500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2560480441/100000000000000 : ℝ)*(base19) + (1182781989/50000000000000 : ℝ)*(base23) + (481960379/100000000000000 : ℝ)*(upper3) + (39928891/50000000000000 : ℝ)*(upper4) + (26453813/50000000000000 : ℝ)*(upper5) + (5361618213628701/100000000000000 : ℝ)*(major0) + (5361618213628701/100000000000000 : ℝ)*(major1) + (5361618213628701/100000000000000 : ℝ)*(major2) + (1432447709994643/20000000000000 : ℝ)*(sp0) + (3581146846434833/50000000000000 : ℝ)*(sp1) + (7162293887786129/100000000000000 : ℝ)*(sp2) + (3560900712993533/100000000000000 : ℝ)*(sp3) + (57703376891/100000000000000 : ℝ)*(sp4) + (9783944737/25000000000000 : ℝ)*(sp7) + (3560939848772481/100000000000000 : ℝ)*(f.failure) + (7162296253350107/100000000000000 : ℝ)*(f.sum) + (35122852429153/6580000000000000000000000000 : ℝ)*base66 + (2711785941388215599/658000000000000000000000000000000 : ℝ)*base67 + (2437846201594215599/658000000000000000000000000000000 : ℝ)*base69 + (6255147898474215599/658000000000000000000000000000000 : ℝ)*base71 + (8434457080853/6580000000000000000000000000 : ℝ)*base74 + (4264184297135784401/658000000000000000000000000000000 : ℝ)*base76 + (514079509348215599/658000000000000000000000000000000 : ℝ)*base77 + (2068509294116215599/658000000000000000000000000000000 : ℝ)*base79 + (4846774036707/6580000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (20715057/10000000000000000000000 : ℝ)*base90 + (20715057/10000000000000000000000 : ℝ)*base92 + (20715057/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3857503783439699758404605997/329000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1754073189/100000000000000 : ℝ)*(base19) + (114410169/5000000000000 : ℝ)*(base23) + (159395389/50000000000000 : ℝ)*(upper3) + (245356869/100000000000000 : ℝ)*(lower4) + (5381081/2000000000000 : ℝ)*(upper5) + (5391770704509233/100000000000000 : ℝ)*(major0) + (5391770704509233/100000000000000 : ℝ)*(major1) + (5391770704509233/100000000000000 : ℝ)*(major2) + (8634487853/100000000000000 : ℝ)*(sp1) + (48827711133/100000000000000 : ℝ)*(sp2) + (3601287636933219/50000000000000 : ℝ)*(sp4) + (1440512977061079/20000000000000 : ℝ)*(sp5) + (288100966318077/4000000000000 : ℝ)*(sp6) + (1790482872160413/50000000000000 : ℝ)*(sp7) + (1790482872160413/50000000000000 : ℝ)*(f.failure) + (3601287636933219/50000000000000 : ℝ)*(f.sum) + (156411106560893/19740000000000000000000000000 : ℝ)*base65 + (39574826985333148001/1974000000000000000000000000000000 : ℝ)*base67 + (28701697699797148001/1974000000000000000000000000000000 : ℝ)*base69 + (54172159660587148001/1974000000000000000000000000000000 : ℝ)*base71 + (33171981422393/19740000000000000000000000000 : ℝ)*base73 + (56158913506797148001/1974000000000000000000000000000000 : ℝ)*base75 + (15206687077725148001/1974000000000000000000000000000000 : ℝ)*base77 + (23427439269237148001/1974000000000000000000000000000000 : ℝ)*base79 + (76557182713853/19740000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (49141261/5000000000000000000000 : ℝ)*base90 + (49141261/5000000000000000000000 : ℝ)*base92 + (49141261/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1198_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2159/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11277/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1198_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1198_s5_0 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2140263103/10000000000 : ℝ)*x 0 + (5393488429/10000000000 : ℝ)*x 1 + (5265207447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140263103/10000000000 : ℝ)^8391 ≤ (81315129619/625000000000 : ℝ)^6343 := by
    have hnat : (2140263103 : ℕ)^8391*625000000000^6343 ≤ 81315129619^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140263103 10000000000 81315129619 625000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393488429/10000000000 : ℝ)^8391 ≤ (8837451210579/20000000000000 : ℝ)^6343 := by
    have hnat : (5393488429 : ℕ)^8391*20000000000000^6343 ≤ 8837451210579^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393488429 10000000000 8837451210579 20000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265207447/10000000000 : ℝ)^8391 ≤ (21401161598951/50000000000000 : ℝ)^6343 := by
    have hnat : (5265207447 : ℕ)^8391*50000000000000^6343 ≤ 21401161598951^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265207447 10000000000 21401161598951 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2140263103/10000000000 : ℝ), (5393488429/10000000000 : ℝ), (5265207447/10000000000 : ℝ)] ![(81315129619/625000000000 : ℝ), (8837451210579/20000000000000 : ℝ), (21401161598951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2140263103/10000000000 : ℝ)|^8391 ≤ (81315129619/625000000000 : ℝ)^6343
        have hw : |(-2140263103/10000000000 : ℝ)|=(2140263103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393488429/10000000000 : ℝ)|^8391 ≤ (8837451210579/20000000000000 : ℝ)^6343
        have hw : |(5393488429/10000000000 : ℝ)|=(5393488429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265207447/10000000000 : ℝ)|^8391 ≤ (21401161598951/50000000000000 : ℝ)^6343
        have hw : |(5265207447/10000000000 : ℝ)|=(5265207447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s5_1 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344898763/10000000000 : ℝ)*x 0 + (-2205336183/10000000000 : ℝ)*x 1 + (2632603733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344898763/10000000000 : ℝ)^8391 ≤ (8732282434681/20000000000000 : ℝ)^6343 := by
    have hnat : (5344898763 : ℕ)^8391*20000000000000^6343 ≤ 8732282434681^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344898763 10000000000 8732282434681 20000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205336183/10000000000 : ℝ)^8391 ≤ (13536264406919/100000000000000 : ℝ)^6343 := by
    have hnat : (2205336183 : ℕ)^8391*100000000000000^6343 ≤ 13536264406919^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205336183 10000000000 13536264406919 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632603733/5000000000 : ℝ)^8391 ≤ (10700580850557/25000000000000 : ℝ)^6343 := by
    have hnat : (2632603733 : ℕ)^8391*25000000000000^6343 ≤ 10700580850557^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632603733 5000000000 10700580850557 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344898763/10000000000 : ℝ), (-2205336183/10000000000 : ℝ), (2632603733/5000000000 : ℝ)] ![(8732282434681/20000000000000 : ℝ), (13536264406919/100000000000000 : ℝ), (10700580850557/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344898763/10000000000 : ℝ)|^8391 ≤ (8732282434681/20000000000000 : ℝ)^6343
        have hw : |(5344898763/10000000000 : ℝ)|=(5344898763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2205336183/10000000000 : ℝ)|^8391 ≤ (13536264406919/100000000000000 : ℝ)^6343
        have hw : |(-2205336183/10000000000 : ℝ)|=(2205336183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632603733/5000000000 : ℝ)|^8391 ≤ (10700580850557/25000000000000 : ℝ)^6343
        have hw : |(2632603733/5000000000 : ℝ)|=(2632603733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s5_2 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344898713/10000000000 : ℝ)*x 0 + (5265207519/10000000000 : ℝ)*x 1 + (-2205336181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344898713/10000000000 : ℝ)^8391 ≤ (4366141163309/10000000000000 : ℝ)^6343 := by
    have hnat : (5344898713 : ℕ)^8391*10000000000000^6343 ≤ 4366141163309^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344898713 10000000000 4366141163309 10000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265207519/10000000000 : ℝ)^8391 ≤ (42802323972191/100000000000000 : ℝ)^6343 := by
    have hnat : (5265207519 : ℕ)^8391*100000000000000^6343 ≤ 42802323972191^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265207519 10000000000 42802323972191 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205336181/10000000000 : ℝ)^8391 ≤ (13536264390679/100000000000000 : ℝ)^6343 := by
    have hnat : (2205336181 : ℕ)^8391*100000000000000^6343 ≤ 13536264390679^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205336181 10000000000 13536264390679 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344898713/10000000000 : ℝ), (5265207519/10000000000 : ℝ), (-2205336181/10000000000 : ℝ)] ![(4366141163309/10000000000000 : ℝ), (42802323972191/100000000000000 : ℝ), (13536264390679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344898713/10000000000 : ℝ)|^8391 ≤ (4366141163309/10000000000000 : ℝ)^6343
        have hw : |(5344898713/10000000000 : ℝ)|=(5344898713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265207519/10000000000 : ℝ)|^8391 ≤ (42802323972191/100000000000000 : ℝ)^6343
        have hw : |(5265207519/10000000000 : ℝ)|=(5265207519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2205336181/10000000000 : ℝ)|^8391 ≤ (13536264390679/100000000000000 : ℝ)^6343
        have hw : |(-2205336181/10000000000 : ℝ)|=(2205336181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s5_3 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089192457/2500000000 : ℝ)*x 0 + (2114818413/5000000000 : ℝ)*x 1 + (4487654607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089192457/2500000000 : ℝ)^8391 ≤ (33316523036191/100000000000000 : ℝ)^6343 := by
    have hnat : (1089192457 : ℕ)^8391*100000000000000^6343 ≤ 33316523036191^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089192457 2500000000 33316523036191 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114818413/5000000000 : ℝ)^8391 ≤ (32036529044389/100000000000000 : ℝ)^6343 := by
    have hnat : (2114818413 : ℕ)^8391*100000000000000^6343 ≤ 32036529044389^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114818413 5000000000 32036529044389 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487654607/10000000000 : ℝ)^8391 ≤ (34646947894617/100000000000000 : ℝ)^6343 := by
    have hnat : (4487654607 : ℕ)^8391*100000000000000^6343 ≤ 34646947894617^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487654607 10000000000 34646947894617 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089192457/2500000000 : ℝ), (2114818413/5000000000 : ℝ), (4487654607/10000000000 : ℝ)] ![(33316523036191/100000000000000 : ℝ), (32036529044389/100000000000000 : ℝ), (34646947894617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089192457/2500000000 : ℝ)|^8391 ≤ (33316523036191/100000000000000 : ℝ)^6343
        have hw : |(1089192457/2500000000 : ℝ)|=(1089192457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114818413/5000000000 : ℝ)|^8391 ≤ (32036529044389/100000000000000 : ℝ)^6343
        have hw : |(2114818413/5000000000 : ℝ)|=(2114818413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487654607/10000000000 : ℝ)|^8391 ≤ (34646947894617/100000000000000 : ℝ)^6343
        have hw : |(4487654607/10000000000 : ℝ)|=(4487654607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s5_4 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2140268181/10000000000 : ℝ)*x 0 + (1053107559/2000000000 : ℝ)*x 1 + (21067019/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140268181/10000000000 : ℝ)^8391 ≤ (406576924199/3125000000000 : ℝ)^6343 := by
    have hnat : (2140268181 : ℕ)^8391*3125000000000^6343 ≤ 406576924199^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140268181 10000000000 406576924199 3125000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053107559/2000000000 : ℝ)^8391 ≤ (42805875803089/100000000000000 : ℝ)^6343 := by
    have hnat : (1053107559 : ℕ)^8391*100000000000000^6343 ≤ 42805875803089^6343*2000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053107559 2000000000 42805875803089 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21067019/39062500 : ℝ)^8391 ≤ (4418366261071/10000000000000 : ℝ)^6343 := by
    have hnat : (21067019 : ℕ)^8391*10000000000000^6343 ≤ 4418366261071^6343*39062500^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21067019 39062500 4418366261071 10000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2140268181/10000000000 : ℝ), (1053107559/2000000000 : ℝ), (21067019/39062500 : ℝ)] ![(406576924199/3125000000000 : ℝ), (42805875803089/100000000000000 : ℝ), (4418366261071/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2140268181/10000000000 : ℝ)|^8391 ≤ (406576924199/3125000000000 : ℝ)^6343
        have hw : |(-2140268181/10000000000 : ℝ)|=(2140268181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053107559/2000000000 : ℝ)|^8391 ≤ (42805875803089/100000000000000 : ℝ)^6343
        have hw : |(1053107559/2000000000 : ℝ)|=(1053107559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21067019/39062500 : ℝ)|^8391 ≤ (4418366261071/10000000000000 : ℝ)^6343
        have hw : |(21067019/39062500 : ℝ)|=(21067019/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s5_5 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312266787/10000000000 : ℝ)*x 0 + (-259673357/1250000000 : ℝ)*x 1 + (674144607/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312266787/10000000000 : ℝ)^8391 ≤ (43309129060569/100000000000000 : ℝ)^6343 := by
    have hnat : (5312266787 : ℕ)^8391*100000000000000^6343 ≤ 43309129060569^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312266787 10000000000 43309129060569 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259673357/1250000000 : ℝ)^8391 ≤ (312680210067/2500000000000 : ℝ)^6343 := by
    have hnat : (259673357 : ℕ)^8391*2500000000000^6343 ≤ 312680210067^6343*1250000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259673357 1250000000 312680210067 2500000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674144607/1250000000 : ℝ)^8391 ≤ (5522957815501/12500000000000 : ℝ)^6343 := by
    have hnat : (674144607 : ℕ)^8391*12500000000000^6343 ≤ 5522957815501^6343*1250000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674144607 1250000000 5522957815501 12500000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312266787/10000000000 : ℝ), (-259673357/1250000000 : ℝ), (674144607/1250000000 : ℝ)] ![(43309129060569/100000000000000 : ℝ), (312680210067/2500000000000 : ℝ), (5522957815501/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312266787/10000000000 : ℝ)|^8391 ≤ (43309129060569/100000000000000 : ℝ)^6343
        have hw : |(5312266787/10000000000 : ℝ)|=(5312266787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-259673357/1250000000 : ℝ)|^8391 ≤ (312680210067/2500000000000 : ℝ)^6343
        have hw : |(-259673357/1250000000 : ℝ)|=(259673357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674144607/1250000000 : ℝ)|^8391 ≤ (5522957815501/12500000000000 : ℝ)^6343
        have hw : |(674144607/1250000000 : ℝ)|=(674144607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s5_6 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312266791/10000000000 : ℝ)*x 0 + (1078631371/2000000000 : ℝ)*x 1 + (-519346713/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312266791/10000000000 : ℝ)^8391 ≤ (43309129103709/100000000000000 : ℝ)^6343 := by
    have hnat : (5312266791 : ℕ)^8391*100000000000000^6343 ≤ 43309129103709^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312266791 10000000000 43309129103709 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078631371/2000000000 : ℝ)^8391 ≤ (44183662513171/100000000000000 : ℝ)^6343 := by
    have hnat : (1078631371 : ℕ)^8391*100000000000000^6343 ≤ 44183662513171^6343*2000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078631371 2000000000 44183662513171 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519346713/2500000000 : ℝ)^8391 ≤ (6253604185411/50000000000000 : ℝ)^6343 := by
    have hnat : (519346713 : ℕ)^8391*50000000000000^6343 ≤ 6253604185411^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519346713 2500000000 6253604185411 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312266791/10000000000 : ℝ), (1078631371/2000000000 : ℝ), (-519346713/2500000000 : ℝ)] ![(43309129103709/100000000000000 : ℝ), (44183662513171/100000000000000 : ℝ), (6253604185411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312266791/10000000000 : ℝ)|^8391 ≤ (43309129103709/100000000000000 : ℝ)^6343
        have hw : |(5312266791/10000000000 : ℝ)|=(5312266791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078631371/2000000000 : ℝ)|^8391 ≤ (44183662513171/100000000000000 : ℝ)^6343
        have hw : |(1078631371/2000000000 : ℝ)|=(1078631371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-519346713/2500000000 : ℝ)|^8391 ≤ (6253604185411/50000000000000 : ℝ)^6343
        have hw : |(-519346713/2500000000 : ℝ)|=(519346713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s5_7 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178390011/5000000000 : ℝ)*x 0 + (4486990273/10000000000 : ℝ)*x 1 + (4230303659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178390011/5000000000 : ℝ)^8391 ≤ (33316626159979/100000000000000 : ℝ)^6343 := by
    have hnat : (2178390011 : ℕ)^8391*100000000000000^6343 ≤ 33316626159979^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178390011 5000000000 33316626159979 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4486990273/10000000000 : ℝ)^8391 ≤ (34640163038083/100000000000000 : ℝ)^6343 := by
    have hnat : (4486990273 : ℕ)^8391*100000000000000^6343 ≤ 34640163038083^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486990273 10000000000 34640163038083 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230303659/10000000000 : ℝ)^8391 ≤ (32043210783659/100000000000000 : ℝ)^6343 := by
    have hnat : (4230303659 : ℕ)^8391*100000000000000^6343 ≤ 32043210783659^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230303659 10000000000 32043210783659 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178390011/5000000000 : ℝ), (4486990273/10000000000 : ℝ), (4230303659/10000000000 : ℝ)] ![(33316626159979/100000000000000 : ℝ), (34640163038083/100000000000000 : ℝ), (32043210783659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178390011/5000000000 : ℝ)|^8391 ≤ (33316626159979/100000000000000 : ℝ)^6343
        have hw : |(2178390011/5000000000 : ℝ)|=(2178390011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4486990273/10000000000 : ℝ)|^8391 ≤ (34640163038083/100000000000000 : ℝ)^6343
        have hw : |(4486990273/10000000000 : ℝ)|=(4486990273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230303659/10000000000 : ℝ)|^8391 ≤ (32043210783659/100000000000000 : ℝ)^6343
        have hw : |(4230303659/10000000000 : ℝ)|=(4230303659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1198_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11277/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2279/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (441/3125 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11277/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11277/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11277/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11277/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11277/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11277/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11277/100000 : ℝ) ^ (4195/1024 : ℝ) ≤ (6548030559941357/50000000000000000000 : ℝ) := by
    have hpowers : (11277/100000 : ℝ)^4195 ≤ (6548030559941357/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11277 : ℕ)^4195*50000000000000000000^1024 ≤ 6548030559941357^1024*100000^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11277 100000 6548030559941357 50000000000000000000 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11277/100000 : ℝ)) (X := (6548030559941357/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (4195/1024 : ℝ) ≤ (17003830032750819/50000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^4195 ≤ (17003830032750819/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2847 : ℕ)^4195*50000000000000000000^1024 ≤ 17003830032750819^1024*20000^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 17003830032750819 50000000000000000000 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (17003830032750819/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006548030559941357/25000000000000000000 : ℝ) ≤ (1000063928673451/1000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (25006548030559941357/25000000000000000000 : ℝ)^1024 ≤ (1000063928673451/1000000000000000 : ℝ)^4195 := by
      have hnat : (25006548030559941357 : ℕ)^1024*1000000000000000^4195 ≤ 1000063928673451^4195*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006548030559941357 25000000000000000000 1000063928673451 1000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000063928673451/1000000000000000 : ℝ)) (X := (25006548030559941357/25000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126471991287043261/3125000000000000000 : ℝ) ≤ (10001149597754399/10000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (3126471991287043261/3125000000000000000 : ℝ)^1024 ≤ (10001149597754399/10000000000000000 : ℝ)^4195 := by
      have hnat : (3126471991287043261 : ℕ)^1024*10000000000000000^4195 ≤ 10001149597754399^4195*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126471991287043261 3125000000000000000 10001149597754399 10000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001149597754399/10000000000000000 : ℝ)) (X := (3126471991287043261/3125000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017003830032750819/25000000000000000000 : ℝ) ≤ (625103744298393/625000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (25017003830032750819/25000000000000000000 : ℝ)^1024 ≤ (625103744298393/625000000000000 : ℝ)^4195 := by
      have hnat : (25017003830032750819 : ℕ)^1024*625000000000000^4195 ≤ 625103744298393^4195*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017003830032750819 25000000000000000000 625103744298393 625000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625103744298393/625000000000000 : ℝ)) (X := (25017003830032750819/25000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6548030559941357/50000000000000000000 : ℝ) ≤ ((4928396909236350679/4930000000000000000 : ℝ)+2*(510311019889/295800000000000 : ℝ)*(11277/100000 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (4928396909236350679/4930000000000000000 : ℝ)+2*(510311019889/295800000000000 : ℝ)*(11277/100000 : ℝ)=(1000063928673451/1000000000000000 : ℝ) by norm_num, show 1+2*(6548030559941357/50000000000000000000 : ℝ)=(25006548030559941357/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17003830032750819/50000000000000000000 : ℝ)+(6548030559941357/50000000000000000000 : ℝ) ≤ ((4928396909236350679/4930000000000000000 : ℝ)+(510311019889/295800000000000 : ℝ)*((2847/20000 : ℝ)+(11277/100000 : ℝ)))^(4195/1024 : ℝ) := by
    rw [show (4928396909236350679/4930000000000000000 : ℝ)+(510311019889/295800000000000 : ℝ)*((2847/20000 : ℝ)+(11277/100000 : ℝ))=(10001149597754399/10000000000000000 : ℝ) by norm_num, show 1+(17003830032750819/50000000000000000000 : ℝ)+(6548030559941357/50000000000000000000 : ℝ)=(3126471991287043261/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17003830032750819/50000000000000000000 : ℝ) ≤ ((4928396909236350679/4930000000000000000 : ℝ)+2*(510311019889/295800000000000 : ℝ)*(2847/20000 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (4928396909236350679/4930000000000000000 : ℝ)+2*(510311019889/295800000000000 : ℝ)*(2847/20000 : ℝ)=(625103744298393/625000000000000 : ℝ) by norm_num, show 1+2*(17003830032750819/50000000000000000000 : ℝ)=(25017003830032750819/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4928396909236350679/4930000000000000000 : ℝ)*(X 1 0+X 2 0)+(510311019889/295800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (11277/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (4928396909236350679/4930000000000000000 : ℝ)) (alpha := (510311019889/295800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4928396909236350679/4930000000000000000 : ℝ)*(X 0 1+X 2 1)+(510311019889/295800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (11277/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (4928396909236350679/4930000000000000000 : ℝ)) (alpha := (510311019889/295800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4928396909236350679/4930000000000000000 : ℝ)*(X 0 2+X 1 2)+(510311019889/295800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (11277/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (4928396909236350679/4930000000000000000 : ℝ)) (alpha := (510311019889/295800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2140263103/10000000000 : ℝ)*X 0 0+(5393488429/10000000000 : ℝ)*X 0 1+(5265207447/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344898763/10000000000 : ℝ)*X 1 0+(-2205336183/10000000000 : ℝ)*X 1 1+(2632603733/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344898713/10000000000 : ℝ)*X 2 0+(5265207519/10000000000 : ℝ)*X 2 1+(-2205336181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1089192457/2500000000 : ℝ)*X 0 0+(2114818413/5000000000 : ℝ)*X 0 1+(4487654607/10000000000 : ℝ)*X 0 2+(1089192457/2500000000 : ℝ)*X 1 0+(2114818413/5000000000 : ℝ)*X 1 1+(4487654607/10000000000 : ℝ)*X 1 2+(1089192457/2500000000 : ℝ)*X 2 0+(2114818413/5000000000 : ℝ)*X 2 1+(4487654607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2140268181/10000000000 : ℝ)*X 0 0+(1053107559/2000000000 : ℝ)*X 0 1+(21067019/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312266787/10000000000 : ℝ)*X 1 0+(-259673357/1250000000 : ℝ)*X 1 1+(674144607/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312266791/10000000000 : ℝ)*X 2 0+(1078631371/2000000000 : ℝ)*X 2 1+(-519346713/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2178390011/5000000000 : ℝ)*X 0 0+(4486990273/10000000000 : ℝ)*X 0 1+(4230303659/10000000000 : ℝ)*X 0 2+(2178390011/5000000000 : ℝ)*X 1 0+(4486990273/10000000000 : ℝ)*X 1 1+(4230303659/10000000000 : ℝ)*X 1 2+(2178390011/5000000000 : ℝ)*X 2 0+(4486990273/10000000000 : ℝ)*X 2 1+(4230303659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78948626464055552318885883/24650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (412156063/50000000000000 : ℝ)*(base19) + (697178527/100000000000000 : ℝ)*(base23) + (5794887/20000000000000 : ℝ)*(lower2) + (19854499/20000000000000 : ℝ)*(upper3) + (12549133/25000000000000 : ℝ)*(upper5) + (1167116203948841/20000000000000 : ℝ)*(major0) + (1167116203948841/20000000000000 : ℝ)*(major1) + (1167116203948841/20000000000000 : ℝ)*(major2) + (974426739660489/12500000000000 : ℝ)*(sp0) + (3897718497830869/50000000000000 : ℝ)*(sp1) + (7795437122795337/100000000000000 : ℝ)*(sp2) + (3875712530729537/100000000000000 : ℝ)*(sp3) + (23902689953/100000000000000 : ℝ)*(sp4) + (11582025527/100000000000000 : ℝ)*(sp7) + (484465514094383/12500000000000 : ℝ)*(f.failure) + (974429727496733/12500000000000 : ℝ)*(f.sum) + (17738547461291/2958000000000000000000000000 : ℝ)*base65 + (3111285036814489117/295800000000000000000000000000000 : ℝ)*base67 + (3692516065980889117/295800000000000000000000000000000 : ℝ)*base69 + (7179332215448089117/295800000000000000000000000000000 : ℝ)*base71 + (12946311618433/2958000000000000000000000000 : ℝ)*base74 + (1917820735040710883/295800000000000000000000000000000 : ℝ)*base76 + (4253553358333489117/295800000000000000000000000000000 : ℝ)*base77 + (5329071857098489117/295800000000000000000000000000000 : ℝ)*base79 + (10846125108359/2958000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (7864351/1250000000000000000000 : ℝ)*base90 + (7864351/1250000000000000000000 : ℝ)*base92 + (7864351/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1587494959088998946164359729/246500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (580881067/50000000000000 : ℝ)*(base19) + (1266536333/100000000000000 : ℝ)*(base23) + (126825397/100000000000000 : ℝ)*(upper3) + (8890591/20000000000000 : ℝ)*(lower4) + (131574519/100000000000000 : ℝ)*(upper5) + (5865809803672317/100000000000000 : ℝ)*(major0) + (5865809803672317/100000000000000 : ℝ)*(major1) + (5865809803672317/100000000000000 : ℝ)*(major2) + (7856847567/25000000000000 : ℝ)*(sp1) + (33900961179/100000000000000 : ℝ)*(sp2) + (3917909357020929/50000000000000 : ℝ)*(sp4) + (7835786124889457/100000000000000 : ℝ)*(sp5) + (3917891773272173/50000000000000 : ℝ)*(sp6) + (243487542414461/6250000000000 : ℝ)*(sp7) + (243487542414461/6250000000000 : ℝ)*(f.failure) + (3917909357020929/50000000000000 : ℝ)*(f.sum) + (9711267532451/4930000000000000000000000000 : ℝ)*base65 + (1904306579336003243/493000000000000000000000000000000 : ℝ)*base67 + (3652734864297996757/493000000000000000000000000000000 : ℝ)*base70 + (5259991436564996757/493000000000000000000000000000000 : ℝ)*base72 + (6370150143111/4930000000000000000000000000 : ℝ)*base73 + (485207284921996757/493000000000000000000000000000000 : ℝ)*base76 + (1782208309374996757/493000000000000000000000000000000 : ℝ)*base78 + (6006917684183003243/493000000000000000000000000000000 : ℝ)*base79 + (15850282659219/4930000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2610883/625000000000000000000 : ℝ)*base89 + (2610883/625000000000000000000 : ℝ)*base91 + (2610883/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1198_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11277/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (441/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1198_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1198_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16341/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2329/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (441/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1198_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1198_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1198_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16341/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2329/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (441/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1198_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

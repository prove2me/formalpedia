-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1412_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:48:51.009519+00:00
-- url     : https://prove2.me/submissions/57e35d73-280b-481a-8d95-323fd7517239

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
theorem support_rectangle_w1412_s3_0 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1983839111/10000000000 : ℝ)*x 0 + (5419034511/10000000000 : ℝ)*x 1 + (5237344151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1983839111/10000000000 : ℝ)^1093 ≤ (6048056226687/50000000000000 : ℝ)^837 := by
    have hnat : (1983839111 : ℕ)^1093*50000000000000^837 ≤ 6048056226687^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983839111 10000000000 6048056226687 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419034511/10000000000 : ℝ)^1093 ≤ (44930453958713/100000000000000 : ℝ)^837 := by
    have hnat : (5419034511 : ℕ)^1093*100000000000000^837 ≤ 44930453958713^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419034511 10000000000 44930453958713 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5237344151/10000000000 : ℝ)^1093 ≤ (21486716790919/50000000000000 : ℝ)^837 := by
    have hnat : (5237344151 : ℕ)^1093*50000000000000^837 ≤ 21486716790919^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237344151 10000000000 21486716790919 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1983839111/10000000000 : ℝ), (5419034511/10000000000 : ℝ), (5237344151/10000000000 : ℝ)] ![(6048056226687/50000000000000 : ℝ), (44930453958713/100000000000000 : ℝ), (21486716790919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1983839111/10000000000 : ℝ)|^1093 ≤ (6048056226687/50000000000000 : ℝ)^837
        have hw : |(-1983839111/10000000000 : ℝ)|=(1983839111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419034511/10000000000 : ℝ)|^1093 ≤ (44930453958713/100000000000000 : ℝ)^837
        have hw : |(5419034511/10000000000 : ℝ)|=(5419034511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5237344151/10000000000 : ℝ)|^1093 ≤ (21486716790919/50000000000000 : ℝ)^837
        have hw : |(5237344151/10000000000 : ℝ)|=(5237344151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s3_1 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1337559933/2500000000 : ℝ)*x 0 + (-207654963/1000000000 : ℝ)*x 1 + (1047468813/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337559933/2500000000 : ℝ)^1093 ≤ (44187053860937/100000000000000 : ℝ)^837 := by
    have hnat : (1337559933 : ℕ)^1093*100000000000000^837 ≤ 44187053860937^837*2500000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337559933 2500000000 44187053860937 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207654963/1000000000 : ℝ)^1093 ≤ (12839513464489/100000000000000 : ℝ)^837 := by
    have hnat : (207654963 : ℕ)^1093*100000000000000^837 ≤ 12839513464489^837*1000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207654963 1000000000 12839513464489 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047468813/2000000000 : ℝ)^1093 ≤ (42973432660367/100000000000000 : ℝ)^837 := by
    have hnat : (1047468813 : ℕ)^1093*100000000000000^837 ≤ 42973432660367^837*2000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047468813 2000000000 42973432660367 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337559933/2500000000 : ℝ), (-207654963/1000000000 : ℝ), (1047468813/2000000000 : ℝ)] ![(44187053860937/100000000000000 : ℝ), (12839513464489/100000000000000 : ℝ), (42973432660367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337559933/2500000000 : ℝ)|^1093 ≤ (44187053860937/100000000000000 : ℝ)^837
        have hw : |(1337559933/2500000000 : ℝ)|=(1337559933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-207654963/1000000000 : ℝ)|^1093 ≤ (12839513464489/100000000000000 : ℝ)^837
        have hw : |(-207654963/1000000000 : ℝ)|=(207654963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047468813/2000000000 : ℝ)|^1093 ≤ (42973432660367/100000000000000 : ℝ)^837
        have hw : |(1047468813/2000000000 : ℝ)|=(1047468813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s3_2 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5350239677/10000000000 : ℝ)*x 0 + (5237344179/10000000000 : ℝ)*x 1 + (-2076549553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350239677/10000000000 : ℝ)^1093 ≤ (44187053267767/100000000000000 : ℝ)^837 := by
    have hnat : (5350239677 : ℕ)^1093*100000000000000^837 ≤ 44187053267767^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350239677 10000000000 44187053267767 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237344179/10000000000 : ℝ)^1093 ≤ (42973433881853/100000000000000 : ℝ)^837 := by
    have hnat : (5237344179 : ℕ)^1093*100000000000000^837 ≤ 42973433881853^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237344179 10000000000 42973433881853 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2076549553/10000000000 : ℝ)^1093 ≤ (6419756421387/50000000000000 : ℝ)^837 := by
    have hnat : (2076549553 : ℕ)^1093*50000000000000^837 ≤ 6419756421387^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076549553 10000000000 6419756421387 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350239677/10000000000 : ℝ), (5237344179/10000000000 : ℝ), (-2076549553/10000000000 : ℝ)] ![(44187053267767/100000000000000 : ℝ), (42973433881853/100000000000000 : ℝ), (6419756421387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350239677/10000000000 : ℝ)|^1093 ≤ (44187053267767/100000000000000 : ℝ)^837
        have hw : |(5350239677/10000000000 : ℝ)|=(5350239677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237344179/10000000000 : ℝ)|^1093 ≤ (42973433881853/100000000000000 : ℝ)^837
        have hw : |(5237344179/10000000000 : ℝ)|=(5237344179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2076549553/10000000000 : ℝ)|^1093 ≤ (6419756421387/50000000000000 : ℝ)^837
        have hw : |(-2076549553/10000000000 : ℝ)|=(2076549553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s3_3 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4307930497/10000000000 : ℝ)*x 0 + (4116635581/10000000000 : ℝ)*x 1 + (4507245697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307930497/10000000000 : ℝ)^1093 ≤ (33297238348293/100000000000000 : ℝ)^837 := by
    have hnat : (4307930497 : ℕ)^1093*100000000000000^837 ≤ 33297238348293^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307930497 10000000000 33297238348293 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4116635581/10000000000 : ℝ)^1093 ≤ (1255187426313/4000000000000 : ℝ)^837 := by
    have hnat : (4116635581 : ℕ)^1093*4000000000000^837 ≤ 1255187426313^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4116635581 10000000000 1255187426313 4000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507245697/10000000000 : ℝ)^1093 ≤ (17661537988649/50000000000000 : ℝ)^837 := by
    have hnat : (4507245697 : ℕ)^1093*50000000000000^837 ≤ 17661537988649^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507245697 10000000000 17661537988649 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307930497/10000000000 : ℝ), (4116635581/10000000000 : ℝ), (4507245697/10000000000 : ℝ)] ![(33297238348293/100000000000000 : ℝ), (1255187426313/4000000000000 : ℝ), (17661537988649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307930497/10000000000 : ℝ)|^1093 ≤ (33297238348293/100000000000000 : ℝ)^837
        have hw : |(4307930497/10000000000 : ℝ)|=(4307930497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4116635581/10000000000 : ℝ)|^1093 ≤ (1255187426313/4000000000000 : ℝ)^837
        have hw : |(4116635581/10000000000 : ℝ)|=(4116635581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507245697/10000000000 : ℝ)|^1093 ≤ (17661537988649/50000000000000 : ℝ)^837
        have hw : |(4507245697/10000000000 : ℝ)|=(4507245697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s3_4 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-495963851/2500000000 : ℝ)*x 0 + (2619037403/5000000000 : ℝ)*x 1 + (169321857/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (495963851/2500000000 : ℝ)^1093 ≤ (12096242181957/100000000000000 : ℝ)^837 := by
    have hnat : (495963851 : ℕ)^1093*100000000000000^837 ≤ 12096242181957^837*2500000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495963851 2500000000 12096242181957 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619037403/5000000000 : ℝ)^1093 ≤ (8596252512687/20000000000000 : ℝ)^837 := by
    have hnat : (2619037403 : ℕ)^1093*20000000000000^837 ≤ 8596252512687^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619037403 5000000000 8596252512687 20000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169321857/312500000 : ℝ)^1093 ≤ (44922495236869/100000000000000 : ℝ)^837 := by
    have hnat : (169321857 : ℕ)^1093*100000000000000^837 ≤ 44922495236869^837*312500000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169321857 312500000 44922495236869 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-495963851/2500000000 : ℝ), (2619037403/5000000000 : ℝ), (169321857/312500000 : ℝ)] ![(12096242181957/100000000000000 : ℝ), (8596252512687/20000000000000 : ℝ), (44922495236869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-495963851/2500000000 : ℝ)|^1093 ≤ (12096242181957/100000000000000 : ℝ)^837
        have hw : |(-495963851/2500000000 : ℝ)|=(495963851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619037403/5000000000 : ℝ)|^1093 ≤ (8596252512687/20000000000000 : ℝ)^837
        have hw : |(2619037403/5000000000 : ℝ)|=(2619037403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169321857/312500000 : ℝ)|^1093 ≤ (44922495236869/100000000000000 : ℝ)^837
        have hw : |(169321857/312500000 : ℝ)|=(169321857/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s3_5 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (66288571/125000000 : ℝ)*x 0 + (-236949223/1250000000 : ℝ)*x 1 + (5418299659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66288571/125000000 : ℝ)^1093 ≤ (43679188511477/100000000000000 : ℝ)^837 := by
    have hnat : (66288571 : ℕ)^1093*100000000000000^837 ≤ 43679188511477^837*125000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66288571 125000000 43679188511477 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (236949223/1250000000 : ℝ)^1093 ≤ (11398313697839/100000000000000 : ℝ)^837 := by
    have hnat : (236949223 : ℕ)^1093*100000000000000^837 ≤ 11398313697839^837*1250000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236949223 1250000000 11398313697839 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418299659/10000000000 : ℝ)^1093 ≤ (44922497781141/100000000000000 : ℝ)^837 := by
    have hnat : (5418299659 : ℕ)^1093*100000000000000^837 ≤ 44922497781141^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418299659 10000000000 44922497781141 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66288571/125000000 : ℝ), (-236949223/1250000000 : ℝ), (5418299659/10000000000 : ℝ)] ![(43679188511477/100000000000000 : ℝ), (11398313697839/100000000000000 : ℝ), (44922497781141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66288571/125000000 : ℝ)|^1093 ≤ (43679188511477/100000000000000 : ℝ)^837
        have hw : |(66288571/125000000 : ℝ)|=(66288571/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-236949223/1250000000 : ℝ)|^1093 ≤ (11398313697839/100000000000000 : ℝ)^837
        have hw : |(-236949223/1250000000 : ℝ)|=(236949223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418299659/10000000000 : ℝ)|^1093 ≤ (44922497781141/100000000000000 : ℝ)^837
        have hw : |(5418299659/10000000000 : ℝ)|=(5418299659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s3_6 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2651543203/5000000000 : ℝ)*x 0 + (5418299057/10000000000 : ℝ)*x 1 + (-1895593619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651543203/5000000000 : ℝ)^1093 ≤ (873583926403/2000000000000 : ℝ)^837 := by
    have hnat : (2651543203 : ℕ)^1093*2000000000000^837 ≤ 873583926403^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651543203 5000000000 873583926403 2000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418299057/10000000000 : ℝ)^1093 ≤ (1796899650539/4000000000000 : ℝ)^837 := by
    have hnat : (5418299057 : ℕ)^1093*4000000000000^837 ≤ 1796899650539^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418299057 10000000000 1796899650539 4000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1895593619/10000000000 : ℝ)^1093 ≤ (11398312402229/100000000000000 : ℝ)^837 := by
    have hnat : (1895593619 : ℕ)^1093*100000000000000^837 ≤ 11398312402229^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895593619 10000000000 11398312402229 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651543203/5000000000 : ℝ), (5418299057/10000000000 : ℝ), (-1895593619/10000000000 : ℝ)] ![(873583926403/2000000000000 : ℝ), (1796899650539/4000000000000 : ℝ), (11398312402229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651543203/5000000000 : ℝ)|^1093 ≤ (873583926403/2000000000000 : ℝ)^837
        have hw : |(2651543203/5000000000 : ℝ)|=(2651543203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418299057/10000000000 : ℝ)|^1093 ≤ (1796899650539/4000000000000 : ℝ)^837
        have hw : |(5418299057/10000000000 : ℝ)|=(5418299057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1895593619/10000000000 : ℝ)|^1093 ≤ (11398312402229/100000000000000 : ℝ)^837
        have hw : |(-1895593619/10000000000 : ℝ)|=(1895593619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s3_7 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4307965751/10000000000 : ℝ)*x 0 + (4505674593/10000000000 : ℝ)*x 1 + (4118214929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307965751/10000000000 : ℝ)^1093 ≤ (8324398544699/25000000000000 : ℝ)^837 := by
    have hnat : (4307965751 : ℕ)^1093*25000000000000^837 ≤ 8324398544699^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307965751 10000000000 8324398544699 25000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4505674593/10000000000 : ℝ)^1093 ≤ (17653499141479/50000000000000 : ℝ)^837 := by
    have hnat : (4505674593 : ℕ)^1093*50000000000000^837 ≤ 17653499141479^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505674593 10000000000 17653499141479 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4118214929/10000000000 : ℝ)^1093 ≤ (15697703763559/50000000000000 : ℝ)^837 := by
    have hnat : (4118214929 : ℕ)^1093*50000000000000^837 ≤ 15697703763559^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4118214929 10000000000 15697703763559 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307965751/10000000000 : ℝ), (4505674593/10000000000 : ℝ), (4118214929/10000000000 : ℝ)] ![(8324398544699/25000000000000 : ℝ), (17653499141479/50000000000000 : ℝ), (15697703763559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307965751/10000000000 : ℝ)|^1093 ≤ (8324398544699/25000000000000 : ℝ)^837
        have hw : |(4307965751/10000000000 : ℝ)|=(4307965751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4505674593/10000000000 : ℝ)|^1093 ≤ (17653499141479/50000000000000 : ℝ)^837
        have hw : |(4505674593/10000000000 : ℝ)|=(4505674593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4118214929/10000000000 : ℝ)|^1093 ≤ (15697703763559/50000000000000 : ℝ)^837
        have hw : |(4118214929/10000000000 : ℝ)|=(4118214929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1412_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157493367/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15853/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (411/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (11109/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3739/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15853/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (411/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15853/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (411/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15853/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (411/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15853/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (411/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15853/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (411/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15853/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (411/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (411/4000 : ℝ) ^ (4371/1024 : ℝ) ≤ (6049739862888377/100000000000000000000 : ℝ) := by
    have hpowers : (411/4000 : ℝ)^4371 ≤ (6049739862888377/100000000000000000000 : ℝ)^1024 := by
      have hnat : (411 : ℕ)^4371*100000000000000000000^1024 ≤ 6049739862888377^1024*4000^4371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        411 4000 6049739862888377 100000000000000000000 4371 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (411/4000 : ℝ)) (X := (6049739862888377/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15853/100000 : ℝ) ^ (4371/1024 : ℝ) ≤ (9628796987203029/25000000000000000000 : ℝ) := by
    have hpowers : (15853/100000 : ℝ)^4371 ≤ (9628796987203029/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15853 : ℕ)^4371*25000000000000000000^1024 ≤ 9628796987203029^1024*100000^4371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15853 100000 9628796987203029 25000000000000000000 4371 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15853/100000 : ℝ)) (X := (9628796987203029/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006049739862888377/50000000000000000000 : ℝ) ≤ (10000283442995299/10000000000000000 : ℝ) ^ (4371/1024 : ℝ) := by
    have hpowers : (50006049739862888377/50000000000000000000 : ℝ)^1024 ≤ (10000283442995299/10000000000000000 : ℝ)^4371 := by
      have hnat : (50006049739862888377 : ℕ)^1024*10000000000000000^4371 ≤ 10000283442995299^4371*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006049739862888377 50000000000000000000 10000283442995299 10000000000000000 1024 4371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283442995299/10000000000000000 : ℝ)) (X := (50006049739862888377/50000000000000000000 : ℝ)) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044564927811700493/100000000000000000000 : ℝ) ≤ (5000521925209543/5000000000000000 : ℝ) ^ (4371/1024 : ℝ) := by
    have hpowers : (100044564927811700493/100000000000000000000 : ℝ)^1024 ≤ (5000521925209543/5000000000000000 : ℝ)^4371 := by
      have hnat : (100044564927811700493 : ℕ)^1024*5000000000000000^4371 ≤ 5000521925209543^4371*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044564927811700493 100000000000000000000 5000521925209543 5000000000000000 1024 4371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000521925209543/5000000000000000 : ℝ)) (X := (100044564927811700493/100000000000000000000 : ℝ)) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509628796987203029/12500000000000000000 : ℝ) ≤ (10001804257842873/10000000000000000 : ℝ) ^ (4371/1024 : ℝ) := by
    have hpowers : (12509628796987203029/12500000000000000000 : ℝ)^1024 ≤ (10001804257842873/10000000000000000 : ℝ)^4371 := by
      have hnat : (12509628796987203029 : ℕ)^1024*10000000000000000^4371 ≤ 10001804257842873^4371*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509628796987203029 12500000000000000000 10001804257842873 10000000000000000 1024 4371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001804257842873/10000000000000000 : ℝ)) (X := (12509628796987203029/12500000000000000000 : ℝ)) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6049739862888377/100000000000000000000 : ℝ) ≤ ((13941488668117238743/13945000000000000000 : ℝ)+2*(760407423787/557800000000000 : ℝ)*(411/4000 : ℝ))^(4371/1024 : ℝ) := by
    rw [show (13941488668117238743/13945000000000000000 : ℝ)+2*(760407423787/557800000000000 : ℝ)*(411/4000 : ℝ)=(10000283442995299/10000000000000000 : ℝ) by norm_num, show 1+2*(6049739862888377/100000000000000000000 : ℝ)=(50006049739862888377/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9628796987203029/25000000000000000000 : ℝ)+(6049739862888377/100000000000000000000 : ℝ) ≤ ((13941488668117238743/13945000000000000000 : ℝ)+(760407423787/557800000000000 : ℝ)*((15853/100000 : ℝ)+(411/4000 : ℝ)))^(4371/1024 : ℝ) := by
    rw [show (13941488668117238743/13945000000000000000 : ℝ)+(760407423787/557800000000000 : ℝ)*((15853/100000 : ℝ)+(411/4000 : ℝ))=(5000521925209543/5000000000000000 : ℝ) by norm_num, show 1+(9628796987203029/25000000000000000000 : ℝ)+(6049739862888377/100000000000000000000 : ℝ)=(100044564927811700493/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9628796987203029/25000000000000000000 : ℝ) ≤ ((13941488668117238743/13945000000000000000 : ℝ)+2*(760407423787/557800000000000 : ℝ)*(15853/100000 : ℝ))^(4371/1024 : ℝ) := by
    rw [show (13941488668117238743/13945000000000000000 : ℝ)+2*(760407423787/557800000000000 : ℝ)*(15853/100000 : ℝ)=(10001804257842873/10000000000000000 : ℝ) by norm_num, show 1+2*(9628796987203029/25000000000000000000 : ℝ)=(12509628796987203029/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13941488668117238743/13945000000000000000 : ℝ)*(X 1 0+X 2 0)+(760407423787/557800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4371/1024 : ℝ)) (lo := (411/4000 : ℝ)) (hi := (15853/100000 : ℝ)) (c := (13941488668117238743/13945000000000000000 : ℝ)) (alpha := (760407423787/557800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13941488668117238743/13945000000000000000 : ℝ)*(X 0 1+X 2 1)+(760407423787/557800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4371/1024 : ℝ)) (lo := (411/4000 : ℝ)) (hi := (15853/100000 : ℝ)) (c := (13941488668117238743/13945000000000000000 : ℝ)) (alpha := (760407423787/557800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13941488668117238743/13945000000000000000 : ℝ)*(X 0 2+X 1 2)+(760407423787/557800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4371/1024 : ℝ)) (lo := (411/4000 : ℝ)) (hi := (15853/100000 : ℝ)) (c := (13941488668117238743/13945000000000000000 : ℝ)) (alpha := (760407423787/557800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1983839111/10000000000 : ℝ)*X 0 0+(5419034511/10000000000 : ℝ)*X 0 1+(5237344151/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337559933/2500000000 : ℝ)*X 1 0+(-207654963/1000000000 : ℝ)*X 1 1+(1047468813/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350239677/10000000000 : ℝ)*X 2 0+(5237344179/10000000000 : ℝ)*X 2 1+(-2076549553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4307930497/10000000000 : ℝ)*X 0 0+(4116635581/10000000000 : ℝ)*X 0 1+(4507245697/10000000000 : ℝ)*X 0 2+(4307930497/10000000000 : ℝ)*X 1 0+(4116635581/10000000000 : ℝ)*X 1 1+(4507245697/10000000000 : ℝ)*X 1 2+(4307930497/10000000000 : ℝ)*X 2 0+(4116635581/10000000000 : ℝ)*X 2 1+(4507245697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-495963851/2500000000 : ℝ)*X 0 0+(2619037403/5000000000 : ℝ)*X 0 1+(169321857/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((66288571/125000000 : ℝ)*X 1 0+(-236949223/1250000000 : ℝ)*X 1 1+(5418299659/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651543203/5000000000 : ℝ)*X 2 0+(5418299057/10000000000 : ℝ)*X 2 1+(-1895593619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4307965751/10000000000 : ℝ)*X 0 0+(4505674593/10000000000 : ℝ)*X 0 1+(4118214929/10000000000 : ℝ)*X 0 2+(4307965751/10000000000 : ℝ)*X 1 0+(4505674593/10000000000 : ℝ)*X 1 1+(4118214929/10000000000 : ℝ)*X 1 2+(4307965751/10000000000 : ℝ)*X 2 0+(4505674593/10000000000 : ℝ)*X 2 1+(4118214929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3938752340620816450333380891/697250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1108243973/100000000000000 : ℝ)*(base19) + (126792999/12500000000000 : ℝ)*(base23) + (4767337/4000000000000 : ℝ)*(upper3) + (19967257/100000000000000 : ℝ)*(upper4) + (21444491/12500000000000 : ℝ)*(upper5) + (4032011147330907/100000000000000 : ℝ)*(major0) + (4032011147330907/100000000000000 : ℝ)*(major1) + (4032011147330907/100000000000000 : ℝ)*(major2) + (4299911910111/78125000000 : ℝ)*(sp0) + (5503906103037881/100000000000000 : ℝ)*(sp1) + (2751953098468931/50000000000000 : ℝ)*(sp2) + (1280053282599879/50000000000000 : ℝ)*(sp3) + (9983169887/50000000000000 : ℝ)*(sp4) + (8329880811/100000000000000 : ℝ)*(sp7) + (256011489508057/10000000000000 : ℝ)*(f.failure) + (2751953605640927/50000000000000 : ℝ)*(f.sum) + (153619609540019/27890000000000000000000000000 : ℝ)*base65 + (5144618224209454901/1394500000000000000000000000000000 : ℝ)*base67 + (17345862971567454901/1394500000000000000000000000000000 : ℝ)*base69 + (8453026755096454901/1394500000000000000000000000000000 : ℝ)*base71 + (63585220868819/27890000000000000000000000000 : ℝ)*base73 + (16437678100016954901/1394500000000000000000000000000000 : ℝ)*base75 + (10755816645047454901/1394500000000000000000000000000000 : ℝ)*base77 + (6219570537766454901/1394500000000000000000000000000000 : ℝ)*base79 + (197259124669299/27890000000000000000000000000 : ℝ)*base81 + (557919/1000000000000000000000 : ℝ)*base89 + (557919/1000000000000000000000 : ℝ)*base91 + (557919/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (780267346405517414641342833/348625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54245811/2500000000000 : ℝ)*(base19) + (1535821257/50000000000000 : ℝ)*(base23) + (339316343/100000000000000 : ℝ)*(upper3) + (15398291/100000000000000 : ℝ)*(lower4) + (196076937/100000000000000 : ℝ)*(upper5) + (2032387599671959/50000000000000 : ℝ)*(major0) + (2032387599671959/50000000000000 : ℝ)*(major1) + (2032387599671959/50000000000000 : ℝ)*(major2) + (21696723893/50000000000000 : ℝ)*(sp1) + (56120507173/100000000000000 : ℝ)*(sp2) + (346789498760871/6250000000000 : ℝ)*(sp4) + (554858641689371/10000000000000 : ℝ)*(sp5) + (5548572788024249/100000000000000 : ℝ)*(sp6) + (10081712280897/390625000000 : ℝ)*(sp7) + (10081712280897/390625000000 : ℝ)*(f.failure) + (346789498760871/6250000000000 : ℝ)*(f.sum) + (2525585148573/13945000000000000000000000000 : ℝ)*base65 + (3733980232968167463/697250000000000000000000000000000 : ℝ)*base68 + (5869219667768167463/697250000000000000000000000000000 : ℝ)*base70 + (2695624092490167463/697250000000000000000000000000000 : ℝ)*base72 + (13951805487687/13945000000000000000000000000 : ℝ)*base74 + (2925515313149167463/697250000000000000000000000000000 : ℝ)*base76 + (1378000132416917463/697250000000000000000000000000000 : ℝ)*base78 + (2778519553722167463/697250000000000000000000000000000 : ℝ)*base80 + (27870635910227/13945000000000000000000000000 : ℝ)*base82 + (341449/39062500000000000000 : ℝ)*base89 + (341449/39062500000000000000 : ℝ)*base91 + (341449/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1412_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157493367/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15853/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (411/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11109/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3739/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1412_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1412_s4_0 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1984829949/10000000000 : ℝ)*x 0 + (5410648789/10000000000 : ℝ)*x 1 + (5245077693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1984829949/10000000000 : ℝ)^1093 ≤ (12104002324183/100000000000000 : ℝ)^837 := by
    have hnat : (1984829949 : ℕ)^1093*100000000000000^837 ≤ 12104002324183^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984829949 10000000000 12104002324183 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410648789/10000000000 : ℝ)^1093 ≤ (44839682099583/100000000000000 : ℝ)^837 := by
    have hnat : (5410648789 : ℕ)^1093*100000000000000^837 ≤ 44839682099583^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410648789 10000000000 44839682099583 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245077693/10000000000 : ℝ)^1093 ≤ (5382039445297/12500000000000 : ℝ)^837 := by
    have hnat : (5245077693 : ℕ)^1093*12500000000000^837 ≤ 5382039445297^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245077693 10000000000 5382039445297 12500000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1984829949/10000000000 : ℝ), (5410648789/10000000000 : ℝ), (5245077693/10000000000 : ℝ)] ![(12104002324183/100000000000000 : ℝ), (44839682099583/100000000000000 : ℝ), (5382039445297/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1984829949/10000000000 : ℝ)|^1093 ≤ (12104002324183/100000000000000 : ℝ)^837
        have hw : |(-1984829949/10000000000 : ℝ)|=(1984829949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410648789/10000000000 : ℝ)|^1093 ≤ (44839682099583/100000000000000 : ℝ)^837
        have hw : |(5410648789/10000000000 : ℝ)|=(5410648789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245077693/10000000000 : ℝ)|^1093 ≤ (5382039445297/12500000000000 : ℝ)^837
        have hw : |(5245077693/10000000000 : ℝ)|=(5245077693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s4_1 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348080019/10000000000 : ℝ)*x 0 + (-2069164843/10000000000 : ℝ)*x 1 + (1311269469/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348080019/10000000000 : ℝ)^1093 ≤ (44163762989537/100000000000000 : ℝ)^837 := by
    have hnat : (5348080019 : ℕ)^1093*100000000000000^837 ≤ 44163762989537^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348080019 10000000000 44163762989537 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069164843/10000000000 : ℝ)^1093 ≤ (638995973623/5000000000000 : ℝ)^837 := by
    have hnat : (2069164843 : ℕ)^1093*5000000000000^837 ≤ 638995973623^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069164843 10000000000 638995973623 5000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311269469/2500000000 : ℝ)^1093 ≤ (43056317524067/100000000000000 : ℝ)^837 := by
    have hnat : (1311269469 : ℕ)^1093*100000000000000^837 ≤ 43056317524067^837*2500000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311269469 2500000000 43056317524067 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348080019/10000000000 : ℝ), (-2069164843/10000000000 : ℝ), (1311269469/2500000000 : ℝ)] ![(44163762989537/100000000000000 : ℝ), (638995973623/5000000000000 : ℝ), (43056317524067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348080019/10000000000 : ℝ)|^1093 ≤ (44163762989537/100000000000000 : ℝ)^837
        have hw : |(5348080019/10000000000 : ℝ)|=(5348080019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2069164843/10000000000 : ℝ)|^1093 ≤ (638995973623/5000000000000 : ℝ)^837
        have hw : |(-2069164843/10000000000 : ℝ)|=(2069164843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311269469/2500000000 : ℝ)|^1093 ≤ (43056317524067/100000000000000 : ℝ)^837
        have hw : |(1311269469/2500000000 : ℝ)|=(1311269469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s4_2 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674040007/5000000000 : ℝ)*x 0 + (5245077593/10000000000 : ℝ)*x 1 + (-82766609/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674040007/5000000000 : ℝ)^1093 ≤ (44163762935619/100000000000000 : ℝ)^837 := by
    have hnat : (2674040007 : ℕ)^1093*100000000000000^837 ≤ 44163762935619^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674040007 5000000000 44163762935619 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245077593/10000000000 : ℝ)^1093 ≤ (43056314490413/100000000000000 : ℝ)^837 := by
    have hnat : (5245077593 : ℕ)^1093*100000000000000^837 ≤ 43056314490413^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245077593 10000000000 43056314490413 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82766609/400000000 : ℝ)^1093 ≤ (798745159591/6250000000000 : ℝ)^837 := by
    have hnat : (82766609 : ℕ)^1093*6250000000000^837 ≤ 798745159591^837*400000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82766609 400000000 798745159591 6250000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674040007/5000000000 : ℝ), (5245077593/10000000000 : ℝ), (-82766609/400000000 : ℝ)] ![(44163762935619/100000000000000 : ℝ), (43056314490413/100000000000000 : ℝ), (798745159591/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674040007/5000000000 : ℝ)|^1093 ≤ (44163762935619/100000000000000 : ℝ)^837
        have hw : |(2674040007/5000000000 : ℝ)|=(2674040007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245077593/10000000000 : ℝ)|^1093 ≤ (43056314490413/100000000000000 : ℝ)^837
        have hw : |(5245077593/10000000000 : ℝ)|=(5245077593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-82766609/400000000 : ℝ)|^1093 ≤ (798745159591/6250000000000 : ℝ)^837
        have hw : |(-82766609/400000000 : ℝ)|=(82766609/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s4_3 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4308536063/10000000000 : ℝ)*x 0 + (4133889701/10000000000 : ℝ)*x 1 + (44898451/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308536063/10000000000 : ℝ)^1093 ≤ (16651675326877/50000000000000 : ℝ)^837 := by
    have hnat : (4308536063 : ℕ)^1093*50000000000000^837 ≤ 16651675326877^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308536063 10000000000 16651675326877 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4133889701/10000000000 : ℝ)^1093 ≤ (31551544425343/100000000000000 : ℝ)^837 := by
    have hnat : (4133889701 : ℕ)^1093*100000000000000^837 ≤ 31551544425343^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133889701 10000000000 31551544425343 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44898451/100000000 : ℝ)^1093 ≤ (35145104900551/100000000000000 : ℝ)^837 := by
    have hnat : (44898451 : ℕ)^1093*100000000000000^837 ≤ 35145104900551^837*100000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44898451 100000000 35145104900551 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308536063/10000000000 : ℝ), (4133889701/10000000000 : ℝ), (44898451/100000000 : ℝ)] ![(16651675326877/50000000000000 : ℝ), (31551544425343/100000000000000 : ℝ), (35145104900551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308536063/10000000000 : ℝ)|^1093 ≤ (16651675326877/50000000000000 : ℝ)^837
        have hw : |(4308536063/10000000000 : ℝ)|=(4308536063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4133889701/10000000000 : ℝ)|^1093 ≤ (31551544425343/100000000000000 : ℝ)^837
        have hw : |(4133889701/10000000000 : ℝ)|=(4133889701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(44898451/100000000 : ℝ)|^1093 ≤ (35145104900551/100000000000000 : ℝ)^837
        have hw : |(44898451/100000000 : ℝ)|=(44898451/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s4_4 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-992421079/5000000000 : ℝ)*x 0 + (1049136959/2000000000 : ℝ)*x 1 + (216401537/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (992421079/5000000000 : ℝ)^1093 ≤ (12104099549843/100000000000000 : ℝ)^837 := by
    have hnat : (992421079 : ℕ)^1093*100000000000000^837 ≤ 12104099549843^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992421079 5000000000 12104099549843 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049136959/2000000000 : ℝ)^1093 ≤ (43062823584077/100000000000000 : ℝ)^837 := by
    have hnat : (1049136959 : ℕ)^1093*100000000000000^837 ≤ 43062823584077^837*2000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049136959 2000000000 43062823584077 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216401537/400000000 : ℝ)^1093 ≤ (44833076848931/100000000000000 : ℝ)^837 := by
    have hnat : (216401537 : ℕ)^1093*100000000000000^837 ≤ 44833076848931^837*400000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216401537 400000000 44833076848931 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-992421079/5000000000 : ℝ), (1049136959/2000000000 : ℝ), (216401537/400000000 : ℝ)] ![(12104099549843/100000000000000 : ℝ), (43062823584077/100000000000000 : ℝ), (44833076848931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-992421079/5000000000 : ℝ)|^1093 ≤ (12104099549843/100000000000000 : ℝ)^837
        have hw : |(-992421079/5000000000 : ℝ)|=(992421079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049136959/2000000000 : ℝ)|^1093 ≤ (43062823584077/100000000000000 : ℝ)^837
        have hw : |(1049136959/2000000000 : ℝ)|=(1049136959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216401537/400000000 : ℝ)|^1093 ≤ (44833076848931/100000000000000 : ℝ)^837
        have hw : |(216401537/400000000 : ℝ)|=(216401537/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s4_5 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1326277241/2500000000 : ℝ)*x 0 + (-1904204019/10000000000 : ℝ)*x 1 + (1082007717/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326277241/2500000000 : ℝ)^1093 ≤ (5462618964259/12500000000000 : ℝ)^837 := by
    have hnat : (1326277241 : ℕ)^1093*12500000000000^837 ≤ 5462618964259^837*2500000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326277241 2500000000 5462618964259 12500000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1904204019/10000000000 : ℝ)^1093 ≤ (2293193938759/20000000000000 : ℝ)^837 := by
    have hnat : (1904204019 : ℕ)^1093*20000000000000^837 ≤ 2293193938759^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904204019 10000000000 2293193938759 20000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082007717/2000000000 : ℝ)^1093 ≤ (44833078580393/100000000000000 : ℝ)^837 := by
    have hnat : (1082007717 : ℕ)^1093*100000000000000^837 ≤ 44833078580393^837*2000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082007717 2000000000 44833078580393 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326277241/2500000000 : ℝ), (-1904204019/10000000000 : ℝ), (1082007717/2000000000 : ℝ)] ![(5462618964259/12500000000000 : ℝ), (2293193938759/20000000000000 : ℝ), (44833078580393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326277241/2500000000 : ℝ)|^1093 ≤ (5462618964259/12500000000000 : ℝ)^837
        have hw : |(1326277241/2500000000 : ℝ)|=(1326277241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1904204019/10000000000 : ℝ)|^1093 ≤ (2293193938759/20000000000000 : ℝ)^837
        have hw : |(-1904204019/10000000000 : ℝ)|=(1904204019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082007717/2000000000 : ℝ)|^1093 ≤ (44833078580393/100000000000000 : ℝ)^837
        have hw : |(1082007717/2000000000 : ℝ)|=(1082007717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s4_6 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652554481/5000000000 : ℝ)*x 0 + (2705019241/5000000000 : ℝ)*x 1 + (-476051041/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652554481/5000000000 : ℝ)^1093 ≤ (21850475846279/50000000000000 : ℝ)^837 := by
    have hnat : (2652554481 : ℕ)^1093*50000000000000^837 ≤ 21850475846279^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652554481 5000000000 21850475846279 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705019241/5000000000 : ℝ)^1093 ≤ (11208269366441/25000000000000 : ℝ)^837 := by
    have hnat : (2705019241 : ℕ)^1093*25000000000000^837 ≤ 11208269366441^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705019241 5000000000 11208269366441 25000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (476051041/2500000000 : ℝ)^1093 ≤ (573298541697/5000000000000 : ℝ)^837 := by
    have hnat : (476051041 : ℕ)^1093*5000000000000^837 ≤ 573298541697^837*2500000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476051041 2500000000 573298541697 5000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652554481/5000000000 : ℝ), (2705019241/5000000000 : ℝ), (-476051041/2500000000 : ℝ)] ![(21850475846279/50000000000000 : ℝ), (11208269366441/25000000000000 : ℝ), (573298541697/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652554481/5000000000 : ℝ)|^1093 ≤ (21850475846279/50000000000000 : ℝ)^837
        have hw : |(2652554481/5000000000 : ℝ)|=(2652554481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705019241/5000000000 : ℝ)|^1093 ≤ (11208269366441/25000000000000 : ℝ)^837
        have hw : |(2705019241/5000000000 : ℝ)|=(2705019241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-476051041/2500000000 : ℝ)|^1093 ≤ (573298541697/5000000000000 : ℝ)^837
        have hw : |(-476051041/2500000000 : ℝ)|=(476051041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s4_7 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2154281173/5000000000 : ℝ)*x 0 + (140266871/312500000 : ℝ)*x 1 + (4135201583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154281173/5000000000 : ℝ)^1093 ≤ (8325903987063/25000000000000 : ℝ)^837 := by
    have hnat : (2154281173 : ℕ)^1093*25000000000000^837 ≤ 8325903987063^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154281173 5000000000 8325903987063 25000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140266871/312500000 : ℝ)^1093 ≤ (4391470461157/12500000000000 : ℝ)^837 := by
    have hnat : (140266871 : ℕ)^1093*12500000000000^837 ≤ 4391470461157^837*312500000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140266871 312500000 4391470461157 12500000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4135201583/10000000000 : ℝ)^1093 ≤ (3945577543299/12500000000000 : ℝ)^837 := by
    have hnat : (4135201583 : ℕ)^1093*12500000000000^837 ≤ 3945577543299^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135201583 10000000000 3945577543299 12500000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154281173/5000000000 : ℝ), (140266871/312500000 : ℝ), (4135201583/10000000000 : ℝ)] ![(8325903987063/25000000000000 : ℝ), (4391470461157/12500000000000 : ℝ), (3945577543299/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154281173/5000000000 : ℝ)|^1093 ≤ (8325903987063/25000000000000 : ℝ)^837
        have hw : |(2154281173/5000000000 : ℝ)|=(2154281173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140266871/312500000 : ℝ)|^1093 ≤ (4391470461157/12500000000000 : ℝ)^837
        have hw : |(140266871/312500000 : ℝ)|=(140266871/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4135201583/10000000000 : ℝ)|^1093 ≤ (3945577543299/12500000000000 : ℝ)^837
        have hw : |(4135201583/10000000000 : ℝ)|=(4135201583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1412_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157493367/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3739/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5637/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14781/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3739/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3739/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3739/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3739/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3739/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3739/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11109/100000 : ℝ) ^ (4371/1024 : ℝ) ≤ (844134025041739/10000000000000000000 : ℝ) := by
    have hpowers : (11109/100000 : ℝ)^4371 ≤ (844134025041739/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11109 : ℕ)^4371*10000000000000000000^1024 ≤ 844134025041739^1024*100000^4371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11109 100000 844134025041739 10000000000000000000 4371 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11109/100000 : ℝ)) (X := (844134025041739/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3739/25000 : ℝ) ^ (4371/1024 : ℝ) ≤ (30036868187678331/100000000000000000000 : ℝ) := by
    have hpowers : (3739/25000 : ℝ)^4371 ≤ (30036868187678331/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3739 : ℕ)^4371*100000000000000000000^1024 ≤ 30036868187678331^1024*25000^4371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3739 25000 30036868187678331 100000000000000000000 4371 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3739/25000 : ℝ)) (X := (30036868187678331/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000844134025041739/5000000000000000000 : ℝ) ≤ (10000395487245367/10000000000000000 : ℝ) ^ (4371/1024 : ℝ) := by
    have hpowers : (5000844134025041739/5000000000000000000 : ℝ)^1024 ≤ (10000395487245367/10000000000000000 : ℝ)^4371 := by
      have hnat : (5000844134025041739 : ℕ)^1024*10000000000000000^4371 ≤ 10000395487245367^4371*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000844134025041739 5000000000000000000 10000395487245367 10000000000000000 1024 4371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000395487245367/10000000000000000 : ℝ)) (X := (5000844134025041739/5000000000000000000 : ℝ)) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038478208438095721/100000000000000000000 : ℝ) ≤ (10000901301352659/10000000000000000 : ℝ) ^ (4371/1024 : ℝ) := by
    have hpowers : (100038478208438095721/100000000000000000000 : ℝ)^1024 ≤ (10000901301352659/10000000000000000 : ℝ)^4371 := by
      have hnat : (100038478208438095721 : ℕ)^1024*10000000000000000^4371 ≤ 10000901301352659^4371*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038478208438095721 100000000000000000000 10000901301352659 10000000000000000 1024 4371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000901301352659/10000000000000000 : ℝ)) (X := (100038478208438095721/100000000000000000000 : ℝ)) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030036868187678331/50000000000000000000 : ℝ) ≤ (10001407115459951/10000000000000000 : ℝ) ^ (4371/1024 : ℝ) := by
    have hpowers : (50030036868187678331/50000000000000000000 : ℝ)^1024 ≤ (10001407115459951/10000000000000000 : ℝ)^4371 := by
      have hnat : (50030036868187678331 : ℕ)^1024*10000000000000000^4371 ≤ 10001407115459951^4371*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030036868187678331 50000000000000000000 10001407115459951 10000000000000000 1024 4371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001407115459951/10000000000000000 : ℝ)) (X := (50030036868187678331/50000000000000000000 : ℝ)) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(844134025041739/10000000000000000000 : ℝ) ≤ ((38460283261597113193/38470000000000000000 : ℝ)+2*(126453526823/96175000000000 : ℝ)*(11109/100000 : ℝ))^(4371/1024 : ℝ) := by
    rw [show (38460283261597113193/38470000000000000000 : ℝ)+2*(126453526823/96175000000000 : ℝ)*(11109/100000 : ℝ)=(10000395487245367/10000000000000000 : ℝ) by norm_num, show 1+2*(844134025041739/10000000000000000000 : ℝ)=(5000844134025041739/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30036868187678331/100000000000000000000 : ℝ)+(844134025041739/10000000000000000000 : ℝ) ≤ ((38460283261597113193/38470000000000000000 : ℝ)+(126453526823/96175000000000 : ℝ)*((3739/25000 : ℝ)+(11109/100000 : ℝ)))^(4371/1024 : ℝ) := by
    rw [show (38460283261597113193/38470000000000000000 : ℝ)+(126453526823/96175000000000 : ℝ)*((3739/25000 : ℝ)+(11109/100000 : ℝ))=(10000901301352659/10000000000000000 : ℝ) by norm_num, show 1+(30036868187678331/100000000000000000000 : ℝ)+(844134025041739/10000000000000000000 : ℝ)=(100038478208438095721/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30036868187678331/100000000000000000000 : ℝ) ≤ ((38460283261597113193/38470000000000000000 : ℝ)+2*(126453526823/96175000000000 : ℝ)*(3739/25000 : ℝ))^(4371/1024 : ℝ) := by
    rw [show (38460283261597113193/38470000000000000000 : ℝ)+2*(126453526823/96175000000000 : ℝ)*(3739/25000 : ℝ)=(10001407115459951/10000000000000000 : ℝ) by norm_num, show 1+2*(30036868187678331/100000000000000000000 : ℝ)=(50030036868187678331/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38460283261597113193/38470000000000000000 : ℝ)*(X 1 0+X 2 0)+(126453526823/96175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4371/1024 : ℝ)) (lo := (11109/100000 : ℝ)) (hi := (3739/25000 : ℝ)) (c := (38460283261597113193/38470000000000000000 : ℝ)) (alpha := (126453526823/96175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38460283261597113193/38470000000000000000 : ℝ)*(X 0 1+X 2 1)+(126453526823/96175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4371/1024 : ℝ)) (lo := (11109/100000 : ℝ)) (hi := (3739/25000 : ℝ)) (c := (38460283261597113193/38470000000000000000 : ℝ)) (alpha := (126453526823/96175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38460283261597113193/38470000000000000000 : ℝ)*(X 0 2+X 1 2)+(126453526823/96175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4371/1024 : ℝ)) (lo := (11109/100000 : ℝ)) (hi := (3739/25000 : ℝ)) (c := (38460283261597113193/38470000000000000000 : ℝ)) (alpha := (126453526823/96175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1984829949/10000000000 : ℝ)*X 0 0+(5410648789/10000000000 : ℝ)*X 0 1+(5245077693/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348080019/10000000000 : ℝ)*X 1 0+(-2069164843/10000000000 : ℝ)*X 1 1+(1311269469/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674040007/5000000000 : ℝ)*X 2 0+(5245077593/10000000000 : ℝ)*X 2 1+(-82766609/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4308536063/10000000000 : ℝ)*X 0 0+(4133889701/10000000000 : ℝ)*X 0 1+(44898451/100000000 : ℝ)*X 0 2+(4308536063/10000000000 : ℝ)*X 1 0+(4133889701/10000000000 : ℝ)*X 1 1+(44898451/100000000 : ℝ)*X 1 2+(4308536063/10000000000 : ℝ)*X 2 0+(4133889701/10000000000 : ℝ)*X 2 1+(44898451/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-992421079/5000000000 : ℝ)*X 0 0+(1049136959/2000000000 : ℝ)*X 0 1+(216401537/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326277241/2500000000 : ℝ)*X 1 0+(-1904204019/10000000000 : ℝ)*X 1 1+(1082007717/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652554481/5000000000 : ℝ)*X 2 0+(2705019241/5000000000 : ℝ)*X 2 1+(-476051041/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2154281173/5000000000 : ℝ)*X 0 0+(140266871/312500000 : ℝ)*X 0 1+(4135201583/10000000000 : ℝ)*X 0 2+(2154281173/5000000000 : ℝ)*X 1 0+(140266871/312500000 : ℝ)*X 1 1+(4135201583/10000000000 : ℝ)*X 1 2+(2154281173/5000000000 : ℝ)*X 2 0+(140266871/312500000 : ℝ)*X 2 1+(4135201583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8486439728696124756330569259/961750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23805727/3125000000000 : ℝ)*(base19) + (78307353/10000000000000 : ℝ)*(base23) + (4613077/12500000000000 : ℝ)*(upper2) + (64641441/25000000000000 : ℝ)*(upper3) + (4424546495226079/100000000000000 : ℝ)*(major0) + (4424546495226079/100000000000000 : ℝ)*(major1) + (4424546495226079/100000000000000 : ℝ)*(major2) + (6039725528484929/100000000000000 : ℝ)*(sp0) + (6039737750607431/100000000000000 : ℝ)*(sp1) + (188741640424167/3125000000000 : ℝ)*(sp2) + (1404672879536407/50000000000000 : ℝ)*(sp3) + (6491952883/50000000000000 : ℝ)*(sp4) + (5235743821/100000000000000 : ℝ)*(sp6) + (2106214193/25000000000000 : ℝ)*(sp7) + (1404677091964793/50000000000000 : ℝ)*(f.failure) + (1207947702478139/20000000000000 : ℝ)*(f.sum) + (98708606777993/19235000000000000000000000000 : ℝ)*base65 + (16713085477692360247/3847000000000000000000000000000000 : ℝ)*base67 + (16240296587014360247/3847000000000000000000000000000000 : ℝ)*base69 + (11390034533294360247/3847000000000000000000000000000000 : ℝ)*base71 + (8662325568793/19235000000000000000000000000 : ℝ)*base73 + (561274079991360247/3847000000000000000000000000000000 : ℝ)*base75 + (8494144520068639753/3847000000000000000000000000000000 : ℝ)*base78 + (39400491905431360247/3847000000000000000000000000000000 : ℝ)*base79 + (13555610844637/4808750000000000000000000000 : ℝ)*base81 + (54971969/5000000000000000000000 : ℝ)*base90 + (54971969/5000000000000000000000 : ℝ)*base92 + (54971969/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (540436616672776198680267399/48087500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (356394327/20000000000000 : ℝ)*(base19) + (69950869/4000000000000 : ℝ)*(base23) + (5829171/50000000000000 : ℝ)*(upper2) + (212550663/100000000000000 : ℝ)*(upper3) + (260990129/100000000000000 : ℝ)*(upper5) + (111432383868919/2500000000000 : ℝ)*(major0) + (111432383868919/2500000000000 : ℝ)*(major1) + (111432383868919/2500000000000 : ℝ)*(major2) + (8519829029/20000000000000 : ℝ)*(sp1) + (4508810147/12500000000000 : ℝ)*(sp2) + (304222117428067/5000000000000 : ℝ)*(sp4) + (6084397967444559/100000000000000 : ℝ)*(sp5) + (6084404529308439/100000000000000 : ℝ)*(sp6) + (2830147986331869/100000000000000 : ℝ)*(sp7) + (2830147986331869/100000000000000 : ℝ)*(f.failure) + (304222117428067/5000000000000 : ℝ)*(f.sum) + (3434799857627/1923500000000000000000000000 : ℝ)*base66 + (1575324976937551633/96175000000000000000000000000000 : ℝ)*base68 + (879673459788123367/96175000000000000000000000000000 : ℝ)*base69 + (204212277743973367/96175000000000000000000000000000 : ℝ)*base71 + (258164044621/48087500000000000000000000 : ℝ)*base74 + (714143634409498367/96175000000000000000000000000000 : ℝ)*base75 + (439777345371548367/96175000000000000000000000000000 : ℝ)*base77 + (175056761265101633/96175000000000000000000000000000 : ℝ)*base80 + (16522195051527/3847000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (28212923/10000000000000000000000 : ℝ)*base89 + (28212923/10000000000000000000000 : ℝ)*base91 + (28212923/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1412_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157493367/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3739/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14781/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1412_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1412_s5_0 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1984981767/10000000000 : ℝ)*x 0 + (5409307721/10000000000 : ℝ)*x 1 + (5246318689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1984981767/10000000000 : ℝ)^1093 ≤ (1513151416373/12500000000000 : ℝ)^837 := by
    have hnat : (1984981767 : ℕ)^1093*12500000000000^837 ≤ 1513151416373^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984981767 10000000000 1513151416373 12500000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409307721/10000000000 : ℝ)^1093 ≤ (44825169599961/100000000000000 : ℝ)^837 := by
    have hnat : (5409307721 : ℕ)^1093*100000000000000^837 ≤ 44825169599961^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409307721 10000000000 44825169599961 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246318689/10000000000 : ℝ)^1093 ≤ (21534809528467/50000000000000 : ℝ)^837 := by
    have hnat : (5246318689 : ℕ)^1093*50000000000000^837 ≤ 21534809528467^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246318689 10000000000 21534809528467 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1984981767/10000000000 : ℝ), (5409307721/10000000000 : ℝ), (5246318689/10000000000 : ℝ)] ![(1513151416373/12500000000000 : ℝ), (44825169599961/100000000000000 : ℝ), (21534809528467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1984981767/10000000000 : ℝ)|^1093 ≤ (1513151416373/12500000000000 : ℝ)^837
        have hw : |(-1984981767/10000000000 : ℝ)|=(1984981767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409307721/10000000000 : ℝ)|^1093 ≤ (44825169599961/100000000000000 : ℝ)^837
        have hw : |(5409307721/10000000000 : ℝ)|=(5409307721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246318689/10000000000 : ℝ)|^1093 ≤ (21534809528467/50000000000000 : ℝ)^837
        have hw : |(5246318689/10000000000 : ℝ)|=(5246318689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s5_1 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1069546811/2000000000 : ℝ)*x 0 + (-516994281/2500000000 : ℝ)*x 1 + (1049263883/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069546811/2000000000 : ℝ)^1093 ≤ (22080016148359/50000000000000 : ℝ)^837 := by
    have hnat : (1069546811 : ℕ)^1093*50000000000000^837 ≤ 22080016148359^837*2000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069546811 2000000000 22080016148359 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516994281/2500000000 : ℝ)^1093 ≤ (6385170422257/50000000000000 : ℝ)^837 := by
    have hnat : (516994281 : ℕ)^1093*50000000000000^837 ≤ 6385170422257^837*2500000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516994281 2500000000 6385170422257 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049263883/2000000000 : ℝ)^1093 ≤ (21534813419973/50000000000000 : ℝ)^837 := by
    have hnat : (1049263883 : ℕ)^1093*50000000000000^837 ≤ 21534813419973^837*2000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049263883 2000000000 21534813419973 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069546811/2000000000 : ℝ), (-516994281/2500000000 : ℝ), (1049263883/2000000000 : ℝ)] ![(22080016148359/50000000000000 : ℝ), (6385170422257/50000000000000 : ℝ), (21534813419973/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069546811/2000000000 : ℝ)|^1093 ≤ (22080016148359/50000000000000 : ℝ)^837
        have hw : |(1069546811/2000000000 : ℝ)|=(1069546811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-516994281/2500000000 : ℝ)|^1093 ≤ (6385170422257/50000000000000 : ℝ)^837
        have hw : |(-516994281/2500000000 : ℝ)|=(516994281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049263883/2000000000 : ℝ)|^1093 ≤ (21534813419973/50000000000000 : ℝ)^837
        have hw : |(1049263883/2000000000 : ℝ)|=(1049263883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s5_2 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5347734261/10000000000 : ℝ)*x 0 + (2623159447/5000000000 : ℝ)*x 1 + (-1033988771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347734261/10000000000 : ℝ)^1093 ≤ (44160034518091/100000000000000 : ℝ)^837 := by
    have hnat : (5347734261 : ℕ)^1093*100000000000000^837 ≤ 44160034518091^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347734261 10000000000 44160034518091 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623159447/5000000000 : ℝ)^1093 ≤ (43069621254617/100000000000000 : ℝ)^837 := by
    have hnat : (2623159447 : ℕ)^1093*100000000000000^837 ≤ 43069621254617^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623159447 5000000000 43069621254617 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1033988771/5000000000 : ℝ)^1093 ≤ (12770344215273/100000000000000 : ℝ)^837 := by
    have hnat : (1033988771 : ℕ)^1093*100000000000000^837 ≤ 12770344215273^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033988771 5000000000 12770344215273 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347734261/10000000000 : ℝ), (2623159447/5000000000 : ℝ), (-1033988771/5000000000 : ℝ)] ![(44160034518091/100000000000000 : ℝ), (43069621254617/100000000000000 : ℝ), (12770344215273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347734261/10000000000 : ℝ)|^1093 ≤ (44160034518091/100000000000000 : ℝ)^837
        have hw : |(5347734261/10000000000 : ℝ)|=(5347734261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623159447/5000000000 : ℝ)|^1093 ≤ (43069621254617/100000000000000 : ℝ)^837
        have hw : |(2623159447/5000000000 : ℝ)|=(2623159447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1033988771/5000000000 : ℝ)|^1093 ≤ (12770344215273/100000000000000 : ℝ)^837
        have hw : |(-1033988771/5000000000 : ℝ)|=(1033988771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s5_3 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (841529/1953125 : ℝ)*x 0 + (4136654409/10000000000 : ℝ)*x 1 + (1121764391/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (841529/1953125 : ℝ)^1093 ≤ (8326070872919/25000000000000 : ℝ)^837 := by
    have hnat : (841529 : ℕ)^1093*25000000000000^837 ≤ 8326070872919^837*1953125^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841529 1953125 8326070872919 25000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4136654409/10000000000 : ℝ)^1093 ≤ (31579102579157/100000000000000 : ℝ)^837 := by
    have hnat : (4136654409 : ℕ)^1093*100000000000000^837 ≤ 31579102579157^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4136654409 10000000000 31579102579157 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121764391/2500000000 : ℝ)^1093 ≤ (35116613917619/100000000000000 : ℝ)^837 := by
    have hnat : (1121764391 : ℕ)^1093*100000000000000^837 ≤ 35116613917619^837*2500000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121764391 2500000000 35116613917619 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(841529/1953125 : ℝ), (4136654409/10000000000 : ℝ), (1121764391/2500000000 : ℝ)] ![(8326070872919/25000000000000 : ℝ), (31579102579157/100000000000000 : ℝ), (35116613917619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(841529/1953125 : ℝ)|^1093 ≤ (8326070872919/25000000000000 : ℝ)^837
        have hw : |(841529/1953125 : ℝ)|=(841529/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4136654409/10000000000 : ℝ)|^1093 ≤ (31579102579157/100000000000000 : ℝ)^837
        have hw : |(4136654409/10000000000 : ℝ)|=(4136654409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121764391/2500000000 : ℝ)|^1093 ≤ (35116613917619/100000000000000 : ℝ)^837
        have hw : |(1121764391/2500000000 : ℝ)|=(1121764391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s5_4 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1984993357/10000000000 : ℝ)*x 0 + (5246907441/10000000000 : ℝ)*x 1 + (5408715903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1984993357/10000000000 : ℝ)^1093 ≤ (3026325907357/25000000000000 : ℝ)^837 := by
    have hnat : (1984993357 : ℕ)^1093*25000000000000^837 ≤ 3026325907357^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984993357 10000000000 3026325907357 25000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246907441/10000000000 : ℝ)^1093 ≤ (336530709557/781250000000 : ℝ)^837 := by
    have hnat : (5246907441 : ℕ)^1093*781250000000^837 ≤ 336530709557^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246907441 10000000000 336530709557 781250000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408715903/10000000000 : ℝ)^1093 ≤ (44818765533051/100000000000000 : ℝ)^837 := by
    have hnat : (5408715903 : ℕ)^1093*100000000000000^837 ≤ 44818765533051^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408715903 10000000000 44818765533051 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1984993357/10000000000 : ℝ), (5246907441/10000000000 : ℝ), (5408715903/10000000000 : ℝ)] ![(3026325907357/25000000000000 : ℝ), (336530709557/781250000000 : ℝ), (44818765533051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1984993357/10000000000 : ℝ)|^1093 ≤ (3026325907357/25000000000000 : ℝ)^837
        have hw : |(-1984993357/10000000000 : ℝ)|=(1984993357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246907441/10000000000 : ℝ)|^1093 ≤ (336530709557/781250000000 : ℝ)^837
        have hw : |(5246907441/10000000000 : ℝ)|=(5246907441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408715903/10000000000 : ℝ)|^1093 ≤ (44818765533051/100000000000000 : ℝ)^837
        have hw : |(5408715903/10000000000 : ℝ)|=(5408715903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s5_5 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305433269/10000000000 : ℝ)*x 0 + (-952790243/5000000000 : ℝ)*x 1 + (5408715903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305433269/10000000000 : ℝ)^1093 ≤ (43704440296549/100000000000000 : ℝ)^837 := by
    have hnat : (5305433269 : ℕ)^1093*100000000000000^837 ≤ 43704440296549^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305433269 10000000000 43704440296549 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (952790243/5000000000 : ℝ)^1093 ≤ (5738397071641/50000000000000 : ℝ)^837 := by
    have hnat : (952790243 : ℕ)^1093*50000000000000^837 ≤ 5738397071641^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952790243 5000000000 5738397071641 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408715903/10000000000 : ℝ)^1093 ≤ (44818765533051/100000000000000 : ℝ)^837 := by
    have hnat : (5408715903 : ℕ)^1093*100000000000000^837 ≤ 44818765533051^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408715903 10000000000 44818765533051 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305433269/10000000000 : ℝ), (-952790243/5000000000 : ℝ), (5408715903/10000000000 : ℝ)] ![(43704440296549/100000000000000 : ℝ), (5738397071641/50000000000000 : ℝ), (44818765533051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305433269/10000000000 : ℝ)|^1093 ≤ (43704440296549/100000000000000 : ℝ)^837
        have hw : |(5305433269/10000000000 : ℝ)|=(5305433269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-952790243/5000000000 : ℝ)|^1093 ≤ (5738397071641/50000000000000 : ℝ)^837
        have hw : |(-952790243/5000000000 : ℝ)|=(952790243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408715903/10000000000 : ℝ)|^1093 ≤ (44818765533051/100000000000000 : ℝ)^837
        have hw : |(5408715903/10000000000 : ℝ)|=(5408715903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s5_6 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305433267/10000000000 : ℝ)*x 0 + (2704357953/5000000000 : ℝ)*x 1 + (-952790243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305433267/10000000000 : ℝ)^1093 ≤ (8740888055007/20000000000000 : ℝ)^837 := by
    have hnat : (5305433267 : ℕ)^1093*20000000000000^837 ≤ 8740888055007^837*10000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305433267 10000000000 8740888055007 20000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704357953/5000000000 : ℝ)^1093 ≤ (44818765565513/100000000000000 : ℝ)^837 := by
    have hnat : (2704357953 : ℕ)^1093*100000000000000^837 ≤ 44818765565513^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704357953 5000000000 44818765565513 100000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (952790243/5000000000 : ℝ)^1093 ≤ (5738397071641/50000000000000 : ℝ)^837 := by
    have hnat : (952790243 : ℕ)^1093*50000000000000^837 ≤ 5738397071641^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952790243 5000000000 5738397071641 50000000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305433267/10000000000 : ℝ), (2704357953/5000000000 : ℝ), (-952790243/5000000000 : ℝ)] ![(8740888055007/20000000000000 : ℝ), (44818765565513/100000000000000 : ℝ), (5738397071641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305433267/10000000000 : ℝ)|^1093 ≤ (8740888055007/20000000000000 : ℝ)^837
        have hw : |(5305433267/10000000000 : ℝ)|=(5305433267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704357953/5000000000 : ℝ)|^1093 ≤ (44818765565513/100000000000000 : ℝ)^837
        have hw : |(2704357953/5000000000 : ℝ)|=(2704357953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-952790243/5000000000 : ℝ)|^1093 ≤ (5738397071641/50000000000000 : ℝ)^837
        have hw : |(-952790243/5000000000 : ℝ)|=(952790243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1412_s5_7 (p : ℝ) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ)) (x : Fin 3 → ℝ) :
    (269290821/625000000 : ℝ)*x 0 + (2242896369/5000000000 : ℝ)*x 1 + (1034481501/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269290821/625000000 : ℝ)^1093 ≤ (2081533272827/6250000000000 : ℝ)^837 := by
    have hnat : (269290821 : ℕ)^1093*6250000000000^837 ≤ 2081533272827^837*625000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269290821 625000000 2081533272827 6250000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242896369/5000000000 : ℝ)^1093 ≤ (1096990253373/3125000000000 : ℝ)^837 := by
    have hnat : (2242896369 : ℕ)^1093*3125000000000^837 ≤ 1096990253373^837*5000000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242896369 5000000000 1096990253373 3125000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034481501/2500000000 : ℝ)^1093 ≤ (987243110009/3125000000000 : ℝ)^837 := by
    have hnat : (1034481501 : ℕ)^1093*3125000000000^837 ≤ 987243110009^837*2500000000^1093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034481501 2500000000 987243110009 3125000000000 1093 837 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1093/256 : ℝ)) 1093 837 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269290821/625000000 : ℝ), (2242896369/5000000000 : ℝ), (1034481501/2500000000 : ℝ)] ![(2081533272827/6250000000000 : ℝ), (1096990253373/3125000000000 : ℝ), (987243110009/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269290821/625000000 : ℝ)|^1093 ≤ (2081533272827/6250000000000 : ℝ)^837
        have hw : |(269290821/625000000 : ℝ)|=(269290821/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242896369/5000000000 : ℝ)|^1093 ≤ (1096990253373/3125000000000 : ℝ)^837
        have hw : |(2242896369/5000000000 : ℝ)|=(2242896369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034481501/2500000000 : ℝ)|^1093 ≤ (987243110009/3125000000000 : ℝ)^837
        have hw : |(1034481501/2500000000 : ℝ)|=(1034481501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1412_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157493367/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11301/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14753/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14781/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5637/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14781/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5637/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14781/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5637/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14781/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5637/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14781/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5637/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14781/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5637/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5637/50000 : ℝ) ^ (4371/1024 : ℝ) ≤ (14383454911927/160000000000000000 : ℝ) := by
    have hpowers : (5637/50000 : ℝ)^4371 ≤ (14383454911927/160000000000000000 : ℝ)^1024 := by
      have hnat : (5637 : ℕ)^4371*160000000000000000^1024 ≤ 14383454911927^1024*50000^4371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5637 50000 14383454911927 160000000000000000 4371 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5637/50000 : ℝ)) (X := (14383454911927/160000000000000000 : ℝ)) (by norm_num) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14781/100000 : ℝ) ^ (4371/1024 : ℝ) ≤ (5713014570422289/20000000000000000000 : ℝ) := by
    have hpowers : (14781/100000 : ℝ)^4371 ≤ (5713014570422289/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14781 : ℕ)^4371*20000000000000000000^1024 ≤ 5713014570422289^1024*100000^4371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14781 100000 5713014570422289 20000000000000000000 4371 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14781/100000 : ℝ)) (X := (5713014570422289/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (80014383454911927/80000000000000000 : ℝ) ≤ (10000421174904751/10000000000000000 : ℝ) ^ (4371/1024 : ℝ) := by
    have hpowers : (80014383454911927/80000000000000000 : ℝ)^1024 ≤ (10000421174904751/10000000000000000 : ℝ)^4371 := by
      have hnat : (80014383454911927 : ℕ)^1024*10000000000000000^4371 ≤ 10000421174904751^4371*80000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80014383454911927 80000000000000000 10000421174904751 10000000000000000 1024 4371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000421174904751/10000000000000000 : ℝ)) (X := (80014383454911927/80000000000000000 : ℝ)) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001877736608603291/5000000000000000000 : ℝ) ≤ (10000879673246729/10000000000000000 : ℝ) ^ (4371/1024 : ℝ) := by
    have hpowers : (5001877736608603291/5000000000000000000 : ℝ)^1024 ≤ (10000879673246729/10000000000000000 : ℝ)^4371 := by
      have hnat : (5001877736608603291 : ℕ)^1024*10000000000000000^4371 ≤ 10000879673246729^4371*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001877736608603291 5000000000000000000 10000879673246729 10000000000000000 1024 4371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000879673246729/10000000000000000 : ℝ)) (X := (5001877736608603291/5000000000000000000 : ℝ)) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005713014570422289/10000000000000000000 : ℝ) ≤ (10001338171588707/10000000000000000 : ℝ) ^ (4371/1024 : ℝ) := by
    have hpowers : (10005713014570422289/10000000000000000000 : ℝ)^1024 ≤ (10001338171588707/10000000000000000 : ℝ)^4371 := by
      have hnat : (10005713014570422289 : ℕ)^1024*10000000000000000^4371 ≤ 10001338171588707^4371*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005713014570422289 10000000000000000000 10001338171588707 10000000000000000 1024 4371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001338171588707/10000000000000000 : ℝ)) (X := (10005713014570422289/10000000000000000000 : ℝ)) (by norm_num) 4371 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14383454911927/160000000000000000 : ℝ) ≤ ((11687046279925347271/11690000000000000000 : ℝ)+2*(229249170989/175350000000000 : ℝ)*(5637/50000 : ℝ))^(4371/1024 : ℝ) := by
    rw [show (11687046279925347271/11690000000000000000 : ℝ)+2*(229249170989/175350000000000 : ℝ)*(5637/50000 : ℝ)=(10000421174904751/10000000000000000 : ℝ) by norm_num, show 1+2*(14383454911927/160000000000000000 : ℝ)=(80014383454911927/80000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5713014570422289/20000000000000000000 : ℝ)+(14383454911927/160000000000000000 : ℝ) ≤ ((11687046279925347271/11690000000000000000 : ℝ)+(229249170989/175350000000000 : ℝ)*((14781/100000 : ℝ)+(5637/50000 : ℝ)))^(4371/1024 : ℝ) := by
    rw [show (11687046279925347271/11690000000000000000 : ℝ)+(229249170989/175350000000000 : ℝ)*((14781/100000 : ℝ)+(5637/50000 : ℝ))=(10000879673246729/10000000000000000 : ℝ) by norm_num, show 1+(5713014570422289/20000000000000000000 : ℝ)+(14383454911927/160000000000000000 : ℝ)=(5001877736608603291/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5713014570422289/20000000000000000000 : ℝ) ≤ ((11687046279925347271/11690000000000000000 : ℝ)+2*(229249170989/175350000000000 : ℝ)*(14781/100000 : ℝ))^(4371/1024 : ℝ) := by
    rw [show (11687046279925347271/11690000000000000000 : ℝ)+2*(229249170989/175350000000000 : ℝ)*(14781/100000 : ℝ)=(10001338171588707/10000000000000000 : ℝ) by norm_num, show 1+2*(5713014570422289/20000000000000000000 : ℝ)=(10005713014570422289/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11687046279925347271/11690000000000000000 : ℝ)*(X 1 0+X 2 0)+(229249170989/175350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4371/1024 : ℝ)) (lo := (5637/50000 : ℝ)) (hi := (14781/100000 : ℝ)) (c := (11687046279925347271/11690000000000000000 : ℝ)) (alpha := (229249170989/175350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11687046279925347271/11690000000000000000 : ℝ)*(X 0 1+X 2 1)+(229249170989/175350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4371/1024 : ℝ)) (lo := (5637/50000 : ℝ)) (hi := (14781/100000 : ℝ)) (c := (11687046279925347271/11690000000000000000 : ℝ)) (alpha := (229249170989/175350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11687046279925347271/11690000000000000000 : ℝ)*(X 0 2+X 1 2)+(229249170989/175350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4371/1024 : ℝ)) (lo := (5637/50000 : ℝ)) (hi := (14781/100000 : ℝ)) (c := (11687046279925347271/11690000000000000000 : ℝ)) (alpha := (229249170989/175350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1984981767/10000000000 : ℝ)*X 0 0+(5409307721/10000000000 : ℝ)*X 0 1+(5246318689/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069546811/2000000000 : ℝ)*X 1 0+(-516994281/2500000000 : ℝ)*X 1 1+(1049263883/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347734261/10000000000 : ℝ)*X 2 0+(2623159447/5000000000 : ℝ)*X 2 1+(-1033988771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((841529/1953125 : ℝ)*X 0 0+(4136654409/10000000000 : ℝ)*X 0 1+(1121764391/2500000000 : ℝ)*X 0 2+(841529/1953125 : ℝ)*X 1 0+(4136654409/10000000000 : ℝ)*X 1 1+(1121764391/2500000000 : ℝ)*X 1 2+(841529/1953125 : ℝ)*X 2 0+(4136654409/10000000000 : ℝ)*X 2 1+(1121764391/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1984993357/10000000000 : ℝ)*X 0 0+(5246907441/10000000000 : ℝ)*X 0 1+(5408715903/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305433269/10000000000 : ℝ)*X 1 0+(-952790243/5000000000 : ℝ)*X 1 1+(5408715903/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305433267/10000000000 : ℝ)*X 2 0+(2704357953/5000000000 : ℝ)*X 2 1+(-952790243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((269290821/625000000 : ℝ)*X 0 0+(2242896369/5000000000 : ℝ)*X 0 1+(1034481501/2500000000 : ℝ)*X 0 2+(269290821/625000000 : ℝ)*X 1 0+(2242896369/5000000000 : ℝ)*X 1 1+(1034481501/2500000000 : ℝ)*X 1 2+(269290821/625000000 : ℝ)*X 2 0+(2242896369/5000000000 : ℝ)*X 2 1+(1034481501/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1412_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (96441121748496116308899133/41750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55300153/50000000000000 : ℝ)*(base19) + (457879431/100000000000000 : ℝ)*(base23) + (5814323/4000000000000 : ℝ)*(upper3) + (88673837/100000000000000 : ℝ)*(lower4) + (2247324297795829/50000000000000 : ℝ)*(major0) + (2247324297795829/50000000000000 : ℝ)*(major1) + (2247324297795829/50000000000000 : ℝ)*(major2) + (613541007034471/10000000000000 : ℝ)*(sp0) + (3067715837513031/50000000000000 : ℝ)*(sp1) + (3067712194914503/50000000000000 : ℝ)*(sp2) + (2853859386865423/100000000000000 : ℝ)*(sp3) + (21715281657/100000000000000 : ℝ)*(sp4) + (693791793/10000000000000 : ℝ)*(sp6) + (594169261/10000000000000 : ℝ)*(sp7) + (178366583034877/6250000000000 : ℝ)*(f.failure) + (23966530412603/390625000000 : ℝ)*(f.sum) + (13229473926973/2505000000000000000000000000 : ℝ)*base66 + (1962991969557400289/250500000000000000000000000000000 : ℝ)*base68 + (2520363146626900289/250500000000000000000000000000000 : ℝ)*base70 + (4355149629345400289/250500000000000000000000000000000 : ℝ)*base72 + (4169749690063/2505000000000000000000000000 : ℝ)*base74 + (6682725572511400289/250500000000000000000000000000000 : ℝ)*base76 + (1871595051078400289/250500000000000000000000000000000 : ℝ)*base78 + (3381327552955900289/250500000000000000000000000000000 : ℝ)*base80 + (27679212469/19570312500000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (5339141/625000000000000000000 : ℝ)*base90 + (5339141/625000000000000000000 : ℝ)*base92 + (5339141/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (66801752512296892391103/5845000000000000000000000000 : ℝ) := by norm_num
    linear_combination (972308401/50000000000000 : ℝ)*(base19) + (2106986841/100000000000000 : ℝ)*(base23) + (4674653/2000000000000 : ℝ)*(upper3) + (37268991/50000000000000 : ℝ)*(lower4) + (234128001/100000000000000 : ℝ)*(upper5) + (4527404378388081/100000000000000 : ℝ)*(major0) + (4527404378388081/100000000000000 : ℝ)*(major1) + (4527404378388081/100000000000000 : ℝ)*(major2) + (40585617199/100000000000000 : ℝ)*(sp1) + (43621371787/100000000000000 : ℝ)*(sp2) + (1236028969788811/20000000000000 : ℝ)*(sp4) + (1236020463742011/20000000000000 : ℝ)*(sp5) + (6180099120585427/100000000000000 : ℝ)*(sp6) + (1437331763434863/50000000000000 : ℝ)*(sp7) + (1437331763434863/50000000000000 : ℝ)*(f.failure) + (1236028969788811/20000000000000 : ℝ)*(f.sum) + (7406763421061/5845000000000000000000000000 : ℝ)*base65 + (6174076336005876951/1169000000000000000000000000000000 : ℝ)*base67 + (5083625740888123049/1169000000000000000000000000000000 : ℝ)*base70 + (3285326028828876951/1169000000000000000000000000000000 : ℝ)*base71 + (543947682899/365312500000000000000000000 : ℝ)*base74 + (12986435828753123049/1169000000000000000000000000000000 : ℝ)*base76 + (2312644760584876951/1169000000000000000000000000000000 : ℝ)*base77 + (12776737188259123049/1169000000000000000000000000000000 : ℝ)*base80 + (16889873461627/2922500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (9053721/5000000000000000000000 : ℝ)*base89 + (9053721/5000000000000000000000 : ℝ)*base91 + (9053721/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1412_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157493367/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1412_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1412_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157493367/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15853/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (411/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1412_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1412_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1412_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4371/1024 : ℝ) ≤ p) (hpb : p ≤ (1093/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157493367/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15853/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (411/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1412_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1570_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:27:14.838977+00:00
-- url     : https://prove2.me/submissions/ca467151-3ea7-4a46-80e7-639a90b35e26

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
theorem support_rectangle_w1570_s3_0 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-357072781/2000000000 : ℝ)*x 0 + (1356865701/2500000000 : ℝ)*x 1 + (652319501/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (357072781/2000000000 : ℝ)^4637 ≤ (10955959363283/100000000000000 : ℝ)^3613 := by
    have hnat : (357072781 : ℕ)^4637*100000000000000^3613 ≤ 10955959363283^3613*2000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357072781 2000000000 10955959363283 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356865701/2500000000 : ℝ)^4637 ≤ (45643194938701/100000000000000 : ℝ)^3613 := by
    have hnat : (1356865701 : ℕ)^4637*100000000000000^3613 ≤ 45643194938701^3613*2500000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356865701 2500000000 45643194938701 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652319501/1250000000 : ℝ)^4637 ≤ (43400845684993/100000000000000 : ℝ)^3613 := by
    have hnat : (652319501 : ℕ)^4637*100000000000000^3613 ≤ 43400845684993^3613*1250000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652319501 1250000000 43400845684993 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-357072781/2000000000 : ℝ), (1356865701/2500000000 : ℝ), (652319501/1250000000 : ℝ)] ![(10955959363283/100000000000000 : ℝ), (45643194938701/100000000000000 : ℝ), (43400845684993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-357072781/2000000000 : ℝ)|^4637 ≤ (10955959363283/100000000000000 : ℝ)^3613
        have hw : |(-357072781/2000000000 : ℝ)|=(357072781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356865701/2500000000 : ℝ)|^4637 ≤ (45643194938701/100000000000000 : ℝ)^3613
        have hw : |(1356865701/2500000000 : ℝ)|=(1356865701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652319501/1250000000 : ℝ)|^4637 ≤ (43400845684993/100000000000000 : ℝ)^3613
        have hw : |(652319501/1250000000 : ℝ)|=(652319501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s3_1 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668579277/1250000000 : ℝ)*x 0 + (-378454979/2000000000 : ℝ)*x 1 + (2609278017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668579277/1250000000 : ℝ)^4637 ≤ (44794143217179/100000000000000 : ℝ)^3613 := by
    have hnat : (668579277 : ℕ)^4637*100000000000000^3613 ≤ 44794143217179^3613*1250000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668579277 1250000000 44794143217179 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (378454979/2000000000 : ℝ)^4637 ≤ (11805010805843/100000000000000 : ℝ)^3613 := by
    have hnat : (378454979 : ℕ)^4637*100000000000000^3613 ≤ 11805010805843^3613*2000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378454979 2000000000 11805010805843 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609278017/5000000000 : ℝ)^4637 ≤ (43400845962511/100000000000000 : ℝ)^3613 := by
    have hnat : (2609278017 : ℕ)^4637*100000000000000^3613 ≤ 43400845962511^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609278017 5000000000 43400845962511 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668579277/1250000000 : ℝ), (-378454979/2000000000 : ℝ), (2609278017/5000000000 : ℝ)] ![(44794143217179/100000000000000 : ℝ), (11805010805843/100000000000000 : ℝ), (43400845962511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668579277/1250000000 : ℝ)|^4637 ≤ (44794143217179/100000000000000 : ℝ)^3613
        have hw : |(668579277/1250000000 : ℝ)|=(668579277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-378454979/2000000000 : ℝ)|^4637 ≤ (11805010805843/100000000000000 : ℝ)^3613
        have hw : |(-378454979/2000000000 : ℝ)|=(378454979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609278017/5000000000 : ℝ)|^4637 ≤ (43400845962511/100000000000000 : ℝ)^3613
        have hw : |(2609278017/5000000000 : ℝ)|=(2609278017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s3_2 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337158563/2500000000 : ℝ)*x 0 + (5218556017/10000000000 : ℝ)*x 1 + (-1892274869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337158563/2500000000 : ℝ)^4637 ≤ (358353148833/800000000000 : ℝ)^3613 := by
    have hnat : (1337158563 : ℕ)^4637*800000000000^3613 ≤ 358353148833^3613*2500000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337158563 2500000000 358353148833 800000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218556017/10000000000 : ℝ)^4637 ≤ (43400845781057/100000000000000 : ℝ)^3613 := by
    have hnat : (5218556017 : ℕ)^4637*100000000000000^3613 ≤ 43400845781057^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218556017 10000000000 43400845781057 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1892274869/10000000000 : ℝ)^4637 ≤ (1180501059767/10000000000000 : ℝ)^3613 := by
    have hnat : (1892274869 : ℕ)^4637*10000000000000^3613 ≤ 1180501059767^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1892274869 10000000000 1180501059767 10000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337158563/2500000000 : ℝ), (5218556017/10000000000 : ℝ), (-1892274869/10000000000 : ℝ)] ![(358353148833/800000000000 : ℝ), (43400845781057/100000000000000 : ℝ), (1180501059767/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337158563/2500000000 : ℝ)|^4637 ≤ (358353148833/800000000000 : ℝ)^3613
        have hw : |(1337158563/2500000000 : ℝ)|=(1337158563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218556017/10000000000 : ℝ)|^4637 ≤ (43400845781057/100000000000000 : ℝ)^3613
        have hw : |(5218556017/10000000000 : ℝ)|=(5218556017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1892274869/10000000000 : ℝ)|^4637 ≤ (1180501059767/10000000000000 : ℝ)^3613
        have hw : |(-1892274869/10000000000 : ℝ)|=(1892274869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s3_3 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (848669627/2000000000 : ℝ)*x 0 + (160103229/400000000 : ℝ)*x 1 + (2247859047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848669627/2000000000 : ℝ)^4637 ≤ (3328077941039/10000000000000 : ℝ)^3613 := by
    have hnat : (848669627 : ℕ)^4637*10000000000000^3613 ≤ 3328077941039^3613*2000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848669627 2000000000 3328077941039 10000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160103229/400000000 : ℝ)^4637 ≤ (247015910847/800000000000 : ℝ)^3613 := by
    have hnat : (160103229 : ℕ)^4637*800000000000^3613 ≤ 247015910847^3613*400000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160103229 400000000 247015910847 800000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247859047/5000000000 : ℝ)^4637 ≤ (112006974131/312500000000 : ℝ)^3613 := by
    have hnat : (2247859047 : ℕ)^4637*312500000000^3613 ≤ 112006974131^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247859047 5000000000 112006974131 312500000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(848669627/2000000000 : ℝ), (160103229/400000000 : ℝ), (2247859047/5000000000 : ℝ)] ![(3328077941039/10000000000000 : ℝ), (247015910847/800000000000 : ℝ), (112006974131/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(848669627/2000000000 : ℝ)|^4637 ≤ (3328077941039/10000000000000 : ℝ)^3613
        have hw : |(848669627/2000000000 : ℝ)|=(848669627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160103229/400000000 : ℝ)|^4637 ≤ (247015910847/800000000000 : ℝ)^3613
        have hw : |(160103229/400000000 : ℝ)|=(160103229/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247859047/5000000000 : ℝ)|^4637 ≤ (112006974131/312500000000 : ℝ)^3613
        have hw : |(2247859047/5000000000 : ℝ)|=(2247859047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s3_4 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-223173993/1250000000 : ℝ)*x 0 + (5219660819/10000000000 : ℝ)*x 1 + (542634969/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223173993/1250000000 : ℝ)^4637 ≤ (10956180192373/100000000000000 : ℝ)^3613 := by
    have hnat : (223173993 : ℕ)^4637*100000000000000^3613 ≤ 10956180192373^3613*1250000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223173993 1250000000 10956180192373 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219660819/10000000000 : ℝ)^4637 ≤ (43412638513843/100000000000000 : ℝ)^3613 := by
    have hnat : (5219660819 : ℕ)^4637*100000000000000^3613 ≤ 43412638513843^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219660819 10000000000 43412638513843 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542634969/1000000000 : ℝ)^4637 ≤ (9126236255737/20000000000000 : ℝ)^3613 := by
    have hnat : (542634969 : ℕ)^4637*20000000000000^3613 ≤ 9126236255737^3613*1000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542634969 1000000000 9126236255737 20000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-223173993/1250000000 : ℝ), (5219660819/10000000000 : ℝ), (542634969/1000000000 : ℝ)] ![(10956180192373/100000000000000 : ℝ), (43412638513843/100000000000000 : ℝ), (9126236255737/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-223173993/1250000000 : ℝ)|^4637 ≤ (10956180192373/100000000000000 : ℝ)^3613
        have hw : |(-223173993/1250000000 : ℝ)|=(223173993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219660819/10000000000 : ℝ)|^4637 ≤ (43412638513843/100000000000000 : ℝ)^3613
        have hw : |(5219660819/10000000000 : ℝ)|=(5219660819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542634969/1000000000 : ℝ)|^4637 ≤ (9126236255737/20000000000000 : ℝ)^3613
        have hw : |(542634969/1000000000 : ℝ)|=(542634969/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s3_5 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293363423/10000000000 : ℝ)*x 0 + (-842240629/5000000000 : ℝ)*x 1 + (5426349651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293363423/10000000000 : ℝ)^4637 ≤ (11050234436759/25000000000000 : ℝ)^3613 := by
    have hnat : (5293363423 : ℕ)^4637*25000000000000^3613 ≤ 11050234436759^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293363423 10000000000 11050234436759 25000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (842240629/5000000000 : ℝ)^4637 ≤ (10167881379733/100000000000000 : ℝ)^3613 := by
    have hnat : (842240629 : ℕ)^4637*100000000000000^3613 ≤ 10167881379733^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842240629 5000000000 10167881379733 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426349651/10000000000 : ℝ)^4637 ≤ (2851948803611/6250000000000 : ℝ)^3613 := by
    have hnat : (5426349651 : ℕ)^4637*6250000000000^3613 ≤ 2851948803611^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426349651 10000000000 2851948803611 6250000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293363423/10000000000 : ℝ), (-842240629/5000000000 : ℝ), (5426349651/10000000000 : ℝ)] ![(11050234436759/25000000000000 : ℝ), (10167881379733/100000000000000 : ℝ), (2851948803611/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293363423/10000000000 : ℝ)|^4637 ≤ (11050234436759/25000000000000 : ℝ)^3613
        have hw : |(5293363423/10000000000 : ℝ)|=(5293363423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-842240629/5000000000 : ℝ)|^4637 ≤ (10167881379733/100000000000000 : ℝ)^3613
        have hw : |(-842240629/5000000000 : ℝ)|=(842240629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426349651/10000000000 : ℝ)|^4637 ≤ (2851948803611/6250000000000 : ℝ)^3613
        have hw : |(5426349651/10000000000 : ℝ)|=(5426349651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s3_6 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293363441/10000000000 : ℝ)*x 0 + (1356587423/2500000000 : ℝ)*x 1 + (-210560147/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293363441/10000000000 : ℝ)^4637 ≤ (2210046896997/5000000000000 : ℝ)^3613 := by
    have hnat : (5293363441 : ℕ)^4637*5000000000000^3613 ≤ 2210046896997^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293363441 10000000000 2210046896997 5000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356587423/2500000000 : ℝ)^4637 ≤ (4563118130027/10000000000000 : ℝ)^3613 := by
    have hnat : (1356587423 : ℕ)^4637*10000000000000^3613 ≤ 4563118130027^3613*2500000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356587423 2500000000 4563118130027 10000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210560147/1250000000 : ℝ)^4637 ≤ (10167880744479/100000000000000 : ℝ)^3613 := by
    have hnat : (210560147 : ℕ)^4637*100000000000000^3613 ≤ 10167880744479^3613*1250000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210560147 1250000000 10167880744479 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293363441/10000000000 : ℝ), (1356587423/2500000000 : ℝ), (-210560147/1250000000 : ℝ)] ![(2210046896997/5000000000000 : ℝ), (4563118130027/10000000000000 : ℝ), (10167880744479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293363441/10000000000 : ℝ)|^4637 ≤ (2210046896997/5000000000000 : ℝ)^3613
        have hw : |(5293363441/10000000000 : ℝ)|=(5293363441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356587423/2500000000 : ℝ)|^4637 ≤ (4563118130027/10000000000000 : ℝ)^3613
        have hw : |(1356587423/2500000000 : ℝ)|=(1356587423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-210560147/1250000000 : ℝ)|^4637 ≤ (10167880744479/100000000000000 : ℝ)^3613
        have hw : |(-210560147/1250000000 : ℝ)|=(210560147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s3_7 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4243414203/10000000000 : ℝ)*x 0 + (1123277521/2500000000 : ℝ)*x 1 + (500651051/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4243414203/10000000000 : ℝ)^4637 ≤ (16640722223901/50000000000000 : ℝ)^3613 := by
    have hnat : (4243414203 : ℕ)^4637*50000000000000^3613 ≤ 16640722223901^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243414203 10000000000 16640722223901 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123277521/2500000000 : ℝ)^4637 ≤ (895388711913/2500000000000 : ℝ)^3613 := by
    have hnat : (1123277521 : ℕ)^4637*2500000000000^3613 ≤ 895388711913^3613*2500000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123277521 2500000000 895388711913 2500000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (500651051/1250000000 : ℝ)^4637 ≤ (15451503530773/50000000000000 : ℝ)^3613 := by
    have hnat : (500651051 : ℕ)^4637*50000000000000^3613 ≤ 15451503530773^3613*1250000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500651051 1250000000 15451503530773 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4243414203/10000000000 : ℝ), (1123277521/2500000000 : ℝ), (500651051/1250000000 : ℝ)] ![(16640722223901/50000000000000 : ℝ), (895388711913/2500000000000 : ℝ), (15451503530773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4243414203/10000000000 : ℝ)|^4637 ≤ (16640722223901/50000000000000 : ℝ)^3613
        have hw : |(4243414203/10000000000 : ℝ)|=(4243414203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123277521/2500000000 : ℝ)|^4637 ≤ (895388711913/2500000000000 : ℝ)^3613
        have hw : |(1123277521/2500000000 : ℝ)|=(1123277521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(500651051/1250000000 : ℝ)|^4637 ≤ (15451503530773/50000000000000 : ℝ)^3613
        have hw : |(500651051/1250000000 : ℝ)|=(500651051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1570_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3953/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (541/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11089/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15519/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3953/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (541/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3953/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (541/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3953/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (541/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3953/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (541/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3953/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (541/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3953/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (541/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (541/5000 : ℝ) ^ (4635/1024 : ℝ) ≤ (212582723596383/5000000000000000000 : ℝ) := by
    have hpowers : (541/5000 : ℝ)^4635 ≤ (212582723596383/5000000000000000000 : ℝ)^1024 := by
      have hnat : (541 : ℕ)^4635*5000000000000000000^1024 ≤ 212582723596383^1024*5000^4635 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        541 5000 212582723596383 5000000000000000000 4635 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (541/5000 : ℝ)) (X := (212582723596383/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3953/25000 : ℝ) ^ (4635/1024 : ℝ) ≤ (4735328977187187/20000000000000000000 : ℝ) := by
    have hpowers : (3953/25000 : ℝ)^4635 ≤ (4735328977187187/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3953 : ℕ)^4635*20000000000000000000^1024 ≤ 4735328977187187^1024*25000^4635 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3953 25000 4735328977187187 20000000000000000000 4635 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3953/25000 : ℝ)) (X := (4735328977187187/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500212582723596383/2500000000000000000 : ℝ) ≤ (10000187855446693/10000000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (2500212582723596383/2500000000000000000 : ℝ)^1024 ≤ (10000187855446693/10000000000000000 : ℝ)^4635 := by
      have hnat : (2500212582723596383 : ℕ)^1024*10000000000000000^4635 ≤ 10000187855446693^4635*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500212582723596383 2500000000000000000 10000187855446693 10000000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000187855446693/10000000000000000 : ℝ)) (X := (2500212582723596383/2500000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005585659871572719/20000000000000000000 : ℝ) ≤ (2500154236611623/2500000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (20005585659871572719/20000000000000000000 : ℝ)^1024 ≤ (2500154236611623/2500000000000000 : ℝ)^4635 := by
      have hnat : (20005585659871572719 : ℕ)^1024*2500000000000000^4635 ≤ 2500154236611623^4635*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005585659871572719 20000000000000000000 2500154236611623 2500000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500154236611623/2500000000000000 : ℝ)) (X := (20005585659871572719/20000000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004735328977187187/10000000000000000000 : ℝ) ≤ (10001046037446291/10000000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (10004735328977187187/10000000000000000000 : ℝ)^1024 ≤ (10001046037446291/10000000000000000 : ℝ)^4635 := by
      have hnat : (10004735328977187187 : ℕ)^1024*10000000000000000^4635 ≤ 10001046037446291^4635*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004735328977187187 10000000000000000000 10001046037446291 10000000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001046037446291/10000000000000000 : ℝ)) (X := (10004735328977187187/10000000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(212582723596383/5000000000000000000 : ℝ) ≤ ((6238956530644280137/6240000000000000000 : ℝ)+2*(429090999799/499200000000000 : ℝ)*(541/5000 : ℝ))^(4635/1024 : ℝ) := by
    rw [show (6238956530644280137/6240000000000000000 : ℝ)+2*(429090999799/499200000000000 : ℝ)*(541/5000 : ℝ)=(10000187855446693/10000000000000000 : ℝ) by norm_num, show 1+2*(212582723596383/5000000000000000000 : ℝ)=(2500212582723596383/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4735328977187187/20000000000000000000 : ℝ)+(212582723596383/5000000000000000000 : ℝ) ≤ ((6238956530644280137/6240000000000000000 : ℝ)+(429090999799/499200000000000 : ℝ)*((3953/25000 : ℝ)+(541/5000 : ℝ)))^(4635/1024 : ℝ) := by
    rw [show (6238956530644280137/6240000000000000000 : ℝ)+(429090999799/499200000000000 : ℝ)*((3953/25000 : ℝ)+(541/5000 : ℝ))=(2500154236611623/2500000000000000 : ℝ) by norm_num, show 1+(4735328977187187/20000000000000000000 : ℝ)+(212582723596383/5000000000000000000 : ℝ)=(20005585659871572719/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4735328977187187/20000000000000000000 : ℝ) ≤ ((6238956530644280137/6240000000000000000 : ℝ)+2*(429090999799/499200000000000 : ℝ)*(3953/25000 : ℝ))^(4635/1024 : ℝ) := by
    rw [show (6238956530644280137/6240000000000000000 : ℝ)+2*(429090999799/499200000000000 : ℝ)*(3953/25000 : ℝ)=(10001046037446291/10000000000000000 : ℝ) by norm_num, show 1+2*(4735328977187187/20000000000000000000 : ℝ)=(10004735328977187187/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6238956530644280137/6240000000000000000 : ℝ)*(X 1 0+X 2 0)+(429090999799/499200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (541/5000 : ℝ)) (hi := (3953/25000 : ℝ)) (c := (6238956530644280137/6240000000000000000 : ℝ)) (alpha := (429090999799/499200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6238956530644280137/6240000000000000000 : ℝ)*(X 0 1+X 2 1)+(429090999799/499200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (541/5000 : ℝ)) (hi := (3953/25000 : ℝ)) (c := (6238956530644280137/6240000000000000000 : ℝ)) (alpha := (429090999799/499200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6238956530644280137/6240000000000000000 : ℝ)*(X 0 2+X 1 2)+(429090999799/499200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (541/5000 : ℝ)) (hi := (3953/25000 : ℝ)) (c := (6238956530644280137/6240000000000000000 : ℝ)) (alpha := (429090999799/499200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-357072781/2000000000 : ℝ)*X 0 0+(1356865701/2500000000 : ℝ)*X 0 1+(652319501/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668579277/1250000000 : ℝ)*X 1 0+(-378454979/2000000000 : ℝ)*X 1 1+(2609278017/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337158563/2500000000 : ℝ)*X 2 0+(5218556017/10000000000 : ℝ)*X 2 1+(-1892274869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((848669627/2000000000 : ℝ)*X 0 0+(160103229/400000000 : ℝ)*X 0 1+(2247859047/5000000000 : ℝ)*X 0 2+(848669627/2000000000 : ℝ)*X 1 0+(160103229/400000000 : ℝ)*X 1 1+(2247859047/5000000000 : ℝ)*X 1 2+(848669627/2000000000 : ℝ)*X 2 0+(160103229/400000000 : ℝ)*X 2 1+(2247859047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-223173993/1250000000 : ℝ)*X 0 0+(5219660819/10000000000 : ℝ)*X 0 1+(542634969/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293363423/10000000000 : ℝ)*X 1 0+(-842240629/5000000000 : ℝ)*X 1 1+(5426349651/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293363441/10000000000 : ℝ)*X 2 0+(1356587423/2500000000 : ℝ)*X 2 1+(-210560147/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4243414203/10000000000 : ℝ)*X 0 0+(1123277521/2500000000 : ℝ)*X 0 1+(500651051/1250000000 : ℝ)*X 0 2+(4243414203/10000000000 : ℝ)*X 1 0+(1123277521/2500000000 : ℝ)*X 1 1+(500651051/1250000000 : ℝ)*X 1 2+(4243414203/10000000000 : ℝ)*X 2 0+(1123277521/2500000000 : ℝ)*X 2 1+(500651051/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6200489166978921936345661/800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (163947293/12500000000000 : ℝ)*(base19) + (15771657/1250000000000 : ℝ)*(base23) + (8778681/20000000000000 : ℝ)*(lower2) + (36351319/20000000000000 : ℝ)*(upper3) + (153001629/100000000000000 : ℝ)*(upper5) + (340735922992711/10000000000000 : ℝ)*(major0) + (340735922992711/10000000000000 : ℝ)*(major1) + (340735922992711/10000000000000 : ℝ)*(major2) + (7479445834033/156250000000 : ℝ)*(sp0) + (2393433027150869/50000000000000 : ℝ)*(sp1) + (4786866104147521/100000000000000 : ℝ)*(sp2) + (506960327886581/25000000000000 : ℝ)*(sp3) + (22032098961/100000000000000 : ℝ)*(sp4) + (9524074093/100000000000000 : ℝ)*(sp7) + (2027850835620417/100000000000000 : ℝ)*(f.failure) + (2393433682940041/50000000000000 : ℝ)*(f.sum) + (2167160996929/2496000000000000000000000000 : ℝ)*base65 + (15179765248097969/20800000000000000000000000000000 : ℝ)*base67 + (121048162708897969/20800000000000000000000000000000 : ℝ)*base69 + (53104300492702031/20800000000000000000000000000000 : ℝ)*base72 + (8500046224897/2496000000000000000000000000 : ℝ)*base73 + (114975685035297969/20800000000000000000000000000000 : ℝ)*base75 + (150186124320097969/20800000000000000000000000000000 : ℝ)*base77 + (64492852566302031/20800000000000000000000000000000 : ℝ)*base80 + (6803976719807/2496000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (102823/100000000000000000000 : ℝ)*base90 + (102823/100000000000000000000 : ℝ)*base92 + (102823/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62965352782939998320671067/26000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (98939777/25000000000000 : ℝ)*(base19) + (225226101/50000000000000 : ℝ)*(base23) + (619919/5000000000000 : ℝ)*(upper2) + (6146267/20000000000000 : ℝ)*(upper3) + (69689011/100000000000000 : ℝ)*(upper5) + (1721945992369141/50000000000000 : ℝ)*(major0) + (1721945992369141/50000000000000 : ℝ)*(major1) + (1721945992369141/50000000000000 : ℝ)*(major2) + (3161937813/50000000000000 : ℝ)*(sp1) + (1935763193/25000000000000 : ℝ)*(sp2) + (604773875295069/12500000000000 : ℝ)*(sp4) + (2419092141362909/50000000000000 : ℝ)*(sp5) + (4838182808855579/100000000000000 : ℝ)*(sp6) + (1024796443195597/50000000000000 : ℝ)*(sp7) + (1024796443195597/50000000000000 : ℝ)*(f.failure) + (604773875295069/12500000000000 : ℝ)*(f.sum) + (84937364333539/12480000000000000000000000000 : ℝ)*base65 + (1186840660885570061/104000000000000000000000000000000 : ℝ)*base68 + (1275071728277570061/104000000000000000000000000000000 : ℝ)*base70 + (164197244597570061/104000000000000000000000000000000 : ℝ)*base72 + (734549532701/12480000000000000000000000000 : ℝ)*base74 + (604000072165570061/104000000000000000000000000000000 : ℝ)*base76 + (85479751490429939/104000000000000000000000000000000 : ℝ)*base77 + (1130956126101570061/104000000000000000000000000000000 : ℝ)*base80 + (672952380259/12480000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (77243/50000000000000000000 : ℝ)*base90 + (77243/50000000000000000000 : ℝ)*base92 + (77243/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1570_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3953/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (541/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11089/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15519/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1570_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1570_s4_0 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1785591043/10000000000 : ℝ)*x 0 + (2712975503/5000000000 : ℝ)*x 1 + (5219917007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1785591043/10000000000 : ℝ)^4637 ≤ (273943707031/2500000000000 : ℝ)^3613 := by
    have hnat : (1785591043 : ℕ)^4637*2500000000000^3613 ≤ 273943707031^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1785591043 10000000000 273943707031 2500000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712975503/5000000000 : ℝ)^4637 ≤ (45626878516397/100000000000000 : ℝ)^3613 := by
    have hnat : (2712975503 : ℕ)^4637*100000000000000^3613 ≤ 45626878516397^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712975503 5000000000 45626878516397 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219917007/10000000000 : ℝ)^4637 ≤ (21707686591641/50000000000000 : ℝ)^3613 := by
    have hnat : (5219917007 : ℕ)^4637*50000000000000^3613 ≤ 21707686591641^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219917007 10000000000 21707686591641 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1785591043/10000000000 : ℝ), (2712975503/5000000000 : ℝ), (5219917007/10000000000 : ℝ)] ![(273943707031/2500000000000 : ℝ), (45626878516397/100000000000000 : ℝ), (21707686591641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1785591043/10000000000 : ℝ)|^4637 ≤ (273943707031/2500000000000 : ℝ)^3613
        have hw : |(-1785591043/10000000000 : ℝ)|=(1785591043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712975503/5000000000 : ℝ)|^4637 ≤ (45626878516397/100000000000000 : ℝ)^3613
        have hw : |(2712975503/5000000000 : ℝ)|=(2712975503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219917007/10000000000 : ℝ)|^4637 ≤ (21707686591641/50000000000000 : ℝ)^3613
        have hw : |(5219917007/10000000000 : ℝ)|=(5219917007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s4_1 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337058319/2500000000 : ℝ)*x 0 + (-945499283/5000000000 : ℝ)*x 1 + (5219917043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337058319/2500000000 : ℝ)^4637 ≤ (11197458440811/25000000000000 : ℝ)^3613 := by
    have hnat : (1337058319 : ℕ)^4637*25000000000000^3613 ≤ 11197458440811^3613*2500000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337058319 2500000000 11197458440811 25000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (945499283/5000000000 : ℝ)^4637 ≤ (5897396326283/50000000000000 : ℝ)^3613 := by
    have hnat : (945499283 : ℕ)^4637*50000000000000^3613 ≤ 5897396326283^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945499283 5000000000 5897396326283 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219917043/10000000000 : ℝ)^4637 ≤ (21707686783783/50000000000000 : ℝ)^3613 := by
    have hnat : (5219917043 : ℕ)^4637*50000000000000^3613 ≤ 21707686783783^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219917043 10000000000 21707686783783 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337058319/2500000000 : ℝ), (-945499283/5000000000 : ℝ), (5219917043/10000000000 : ℝ)] ![(11197458440811/25000000000000 : ℝ), (5897396326283/50000000000000 : ℝ), (21707686783783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337058319/2500000000 : ℝ)|^4637 ≤ (11197458440811/25000000000000 : ℝ)^3613
        have hw : |(1337058319/2500000000 : ℝ)|=(1337058319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-945499283/5000000000 : ℝ)|^4637 ≤ (5897396326283/50000000000000 : ℝ)^3613
        have hw : |(-945499283/5000000000 : ℝ)|=(945499283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219917043/10000000000 : ℝ)|^4637 ≤ (21707686783783/50000000000000 : ℝ)^3613
        have hw : |(5219917043/10000000000 : ℝ)|=(5219917043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s4_2 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348233303/10000000000 : ℝ)*x 0 + (5219917013/10000000000 : ℝ)*x 1 + (-189099857/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348233303/10000000000 : ℝ)^4637 ≤ (44789834053447/100000000000000 : ℝ)^3613 := by
    have hnat : (5348233303 : ℕ)^4637*100000000000000^3613 ≤ 44789834053447^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348233303 10000000000 44789834053447 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219917013/10000000000 : ℝ)^4637 ≤ (4341537324733/10000000000000 : ℝ)^3613 := by
    have hnat : (5219917013 : ℕ)^4637*10000000000000^3613 ≤ 4341537324733^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219917013 10000000000 4341537324733 10000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (189099857/1000000000 : ℝ)^4637 ≤ (11794792684587/100000000000000 : ℝ)^3613 := by
    have hnat : (189099857 : ℕ)^4637*100000000000000^3613 ≤ 11794792684587^3613*1000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189099857 1000000000 11794792684587 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348233303/10000000000 : ℝ), (5219917013/10000000000 : ℝ), (-189099857/1000000000 : ℝ)] ![(44789834053447/100000000000000 : ℝ), (4341537324733/10000000000000 : ℝ), (11794792684587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348233303/10000000000 : ℝ)|^4637 ≤ (44789834053447/100000000000000 : ℝ)^3613
        have hw : |(5348233303/10000000000 : ℝ)|=(5348233303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219917013/10000000000 : ℝ)|^4637 ≤ (4341537324733/10000000000000 : ℝ)^3613
        have hw : |(5219917013/10000000000 : ℝ)|=(5219917013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-189099857/1000000000 : ℝ)|^4637 ≤ (11794792684587/100000000000000 : ℝ)^3613
        have hw : |(-189099857/1000000000 : ℝ)|=(189099857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s4_3 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2121745293/5000000000 : ℝ)*x 0 + (4005955633/10000000000 : ℝ)*x 1 + (70192369/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121745293/5000000000 : ℝ)^4637 ≤ (16641106659591/50000000000000 : ℝ)^3613 := by
    have hnat : (2121745293 : ℕ)^4637*50000000000000^3613 ≤ 16641106659591^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121745293 5000000000 16641106659591 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4005955633/10000000000 : ℝ)^4637 ≤ (3091040665111/10000000000000 : ℝ)^3613 := by
    have hnat : (4005955633 : ℕ)^4637*10000000000000^3613 ≤ 3091040665111^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4005955633 10000000000 3091040665111 10000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70192369/156250000 : ℝ)^4637 ≤ (716147600303/2000000000000 : ℝ)^3613 := by
    have hnat : (70192369 : ℕ)^4637*2000000000000^3613 ≤ 716147600303^3613*156250000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70192369 156250000 716147600303 2000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121745293/5000000000 : ℝ), (4005955633/10000000000 : ℝ), (70192369/156250000 : ℝ)] ![(16641106659591/50000000000000 : ℝ), (3091040665111/10000000000000 : ℝ), (716147600303/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121745293/5000000000 : ℝ)|^4637 ≤ (16641106659591/50000000000000 : ℝ)^3613
        have hw : |(2121745293/5000000000 : ℝ)|=(2121745293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4005955633/10000000000 : ℝ)|^4637 ≤ (3091040665111/10000000000000 : ℝ)^3613
        have hw : |(4005955633/10000000000 : ℝ)|=(4005955633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70192369/156250000 : ℝ)|^4637 ≤ (716147600303/2000000000000 : ℝ)^3613
        have hw : |(70192369/156250000 : ℝ)|=(70192369/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s4_4 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-357123587/2000000000 : ℝ)*x 0 + (1044198361/2000000000 : ℝ)*x 1 + (21699473/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (357123587/2000000000 : ℝ)^4637 ≤ (1369745010553/12500000000000 : ℝ)^3613 := by
    have hnat : (357123587 : ℕ)^4637*12500000000000^3613 ≤ 1369745010553^3613*2000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357123587 2000000000 1369745010553 12500000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044198361/2000000000 : ℝ)^4637 ≤ (43426846489783/100000000000000 : ℝ)^3613 := by
    have hnat : (1044198361 : ℕ)^4637*100000000000000^3613 ≤ 43426846489783^3613*2000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044198361 2000000000 43426846489783 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21699473/40000000 : ℝ)^4637 ≤ (2850949588679/6250000000000 : ℝ)^3613 := by
    have hnat : (21699473 : ℕ)^4637*6250000000000^3613 ≤ 2850949588679^3613*40000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21699473 40000000 2850949588679 6250000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-357123587/2000000000 : ℝ), (1044198361/2000000000 : ℝ), (21699473/40000000 : ℝ)] ![(1369745010553/12500000000000 : ℝ), (43426846489783/100000000000000 : ℝ), (2850949588679/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-357123587/2000000000 : ℝ)|^4637 ≤ (1369745010553/12500000000000 : ℝ)^3613
        have hw : |(-357123587/2000000000 : ℝ)|=(357123587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044198361/2000000000 : ℝ)|^4637 ≤ (43426846489783/100000000000000 : ℝ)^3613
        have hw : |(1044198361/2000000000 : ℝ)|=(1044198361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21699473/40000000 : ℝ)|^4637 ≤ (2850949588679/6250000000000 : ℝ)^3613
        have hw : |(21699473/40000000 : ℝ)|=(21699473/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s4_5 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293722979/10000000000 : ℝ)*x 0 + (-105377959/625000000 : ℝ)*x 1 + (5424868251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293722979/10000000000 : ℝ)^4637 ≤ (44204791107403/100000000000000 : ℝ)^3613 := by
    have hnat : (5293722979 : ℕ)^4637*100000000000000^3613 ≤ 44204791107403^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293722979 10000000000 44204791107403 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105377959/625000000 : ℝ)^4637 ≤ (2036003088467/20000000000000 : ℝ)^3613 := by
    have hnat : (105377959 : ℕ)^4637*20000000000000^3613 ≤ 2036003088467^3613*625000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105377959 625000000 2036003088467 20000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424868251/10000000000 : ℝ)^4637 ≤ (9123038685931/20000000000000 : ℝ)^3613 := by
    have hnat : (5424868251 : ℕ)^4637*20000000000000^3613 ≤ 9123038685931^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424868251 10000000000 9123038685931 20000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293722979/10000000000 : ℝ), (-105377959/625000000 : ℝ), (5424868251/10000000000 : ℝ)] ![(44204791107403/100000000000000 : ℝ), (2036003088467/20000000000000 : ℝ), (9123038685931/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293722979/10000000000 : ℝ)|^4637 ≤ (44204791107403/100000000000000 : ℝ)^3613
        have hw : |(5293722979/10000000000 : ℝ)|=(5293722979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-105377959/625000000 : ℝ)|^4637 ≤ (2036003088467/20000000000000 : ℝ)^3613
        have hw : |(-105377959/625000000 : ℝ)|=(105377959/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424868251/10000000000 : ℝ)|^4637 ≤ (9123038685931/20000000000000 : ℝ)^3613
        have hw : |(5424868251/10000000000 : ℝ)|=(5424868251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s4_6 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293722983/10000000000 : ℝ)*x 0 + (5424868249/10000000000 : ℝ)*x 1 + (-843023671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293722983/10000000000 : ℝ)^4637 ≤ (44204791150271/100000000000000 : ℝ)^3613 := by
    have hnat : (5293722983 : ℕ)^4637*100000000000000^3613 ≤ 44204791150271^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293722983 10000000000 44204791150271 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424868249/10000000000 : ℝ)^4637 ≤ (5701899176009/12500000000000 : ℝ)^3613 := by
    have hnat : (5424868249 : ℕ)^4637*12500000000000^3613 ≤ 5701899176009^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424868249 10000000000 5701899176009 12500000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (843023671/5000000000 : ℝ)^4637 ≤ (10180015426837/100000000000000 : ℝ)^3613 := by
    have hnat : (843023671 : ℕ)^4637*100000000000000^3613 ≤ 10180015426837^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843023671 5000000000 10180015426837 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293722983/10000000000 : ℝ), (5424868249/10000000000 : ℝ), (-843023671/5000000000 : ℝ)] ![(44204791150271/100000000000000 : ℝ), (5701899176009/12500000000000 : ℝ), (10180015426837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293722983/10000000000 : ℝ)|^4637 ≤ (44204791150271/100000000000000 : ℝ)^3613
        have hw : |(5293722983/10000000000 : ℝ)|=(5293722983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424868249/10000000000 : ℝ)|^4637 ≤ (5701899176009/12500000000000 : ℝ)^3613
        have hw : |(5424868249/10000000000 : ℝ)|=(5424868249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-843023671/5000000000 : ℝ)|^4637 ≤ (10180015426837/100000000000000 : ℝ)^3613
        have hw : |(-843023671/5000000000 : ℝ)|=(843023671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s4_7 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4243554067/10000000000 : ℝ)*x 0 + (2244887247/5000000000 : ℝ)*x 1 + (801702307/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4243554067/10000000000 : ℝ)^4637 ≤ (8320713080499/25000000000000 : ℝ)^3613 := by
    have hnat : (4243554067 : ℕ)^4637*25000000000000^3613 ≤ 8320713080499^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243554067 10000000000 8320713080499 25000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244887247/5000000000 : ℝ)^4637 ≤ (279542402839/781250000000 : ℝ)^3613 := by
    have hnat : (2244887247 : ℕ)^4637*781250000000^3613 ≤ 279542402839^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244887247 5000000000 279542402839 781250000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (801702307/2000000000 : ℝ)^4637 ≤ (966741252859/3125000000000 : ℝ)^3613 := by
    have hnat : (801702307 : ℕ)^4637*3125000000000^3613 ≤ 966741252859^3613*2000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801702307 2000000000 966741252859 3125000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4243554067/10000000000 : ℝ), (2244887247/5000000000 : ℝ), (801702307/2000000000 : ℝ)] ![(8320713080499/25000000000000 : ℝ), (279542402839/781250000000 : ℝ), (966741252859/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4243554067/10000000000 : ℝ)|^4637 ≤ (8320713080499/25000000000000 : ℝ)^3613
        have hw : |(4243554067/10000000000 : ℝ)|=(4243554067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244887247/5000000000 : ℝ)|^4637 ≤ (279542402839/781250000000 : ℝ)^3613
        have hw : |(2244887247/5000000000 : ℝ)|=(2244887247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(801702307/2000000000 : ℝ)|^4637 ≤ (966741252859/3125000000000 : ℝ)^3613
        have hw : |(801702307/2000000000 : ℝ)|=(801702307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1570_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15519/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11089/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5559/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15519/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11089/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15519/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11089/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15519/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11089/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15519/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11089/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15519/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11089/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15519/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11089/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11089/100000 : ℝ) ^ (4635/1024 : ℝ) ≤ (4751516306384217/100000000000000000000 : ℝ) := by
    have hpowers : (11089/100000 : ℝ)^4635 ≤ (4751516306384217/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11089 : ℕ)^4635*100000000000000000000^1024 ≤ 4751516306384217^1024*100000^4635 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11089 100000 4751516306384217 100000000000000000000 4635 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11089/100000 : ℝ)) (X := (4751516306384217/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15519/100000 : ℝ) ^ (4635/1024 : ℝ) ≤ (5438663137242013/25000000000000000000 : ℝ) := by
    have hpowers : (15519/100000 : ℝ)^4635 ≤ (5438663137242013/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15519 : ℕ)^4635*25000000000000000000^1024 ≤ 5438663137242013^1024*100000^4635 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15519 100000 5438663137242013 25000000000000000000 4635 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15519/100000 : ℝ)) (X := (5438663137242013/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004751516306384217/50000000000000000000 : ℝ) ≤ (1250026242570637/1250000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (50004751516306384217/50000000000000000000 : ℝ)^1024 ≤ (1250026242570637/1250000000000000 : ℝ)^4635 := by
      have hnat : (50004751516306384217 : ℕ)^1024*1250000000000000^4635 ≤ 1250026242570637^4635*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004751516306384217 50000000000000000000 1250026242570637 1250000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250026242570637/1250000000000000 : ℝ)) (X := (50004751516306384217/50000000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026506168855352269/100000000000000000000 : ℝ) ≤ (1000058553430149/1000000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (100026506168855352269/100000000000000000000 : ℝ)^1024 ≤ (1000058553430149/1000000000000000 : ℝ)^4635 := by
      have hnat : (100026506168855352269 : ℕ)^1024*1000000000000000^4635 ≤ 1000058553430149^4635*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026506168855352269 100000000000000000000 1000058553430149 1000000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000058553430149/1000000000000000 : ℝ)) (X := (100026506168855352269/100000000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505438663137242013/12500000000000000000 : ℝ) ≤ (2500240282009471/2500000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (12505438663137242013/12500000000000000000 : ℝ)^1024 ≤ (2500240282009471/2500000000000000 : ℝ)^4635 := by
      have hnat : (12505438663137242013 : ℕ)^1024*2500000000000000^4635 ≤ 2500240282009471^4635*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505438663137242013 12500000000000000000 2500240282009471 2500000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500240282009471/2500000000000000 : ℝ)) (X := (12505438663137242013/12500000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4751516306384217/100000000000000000000 : ℝ) ≤ ((11073150029704407287/11075000000000000000 : ℝ)+2*(187796868197/221500000000000 : ℝ)*(11089/100000 : ℝ))^(4635/1024 : ℝ) := by
    rw [show (11073150029704407287/11075000000000000000 : ℝ)+2*(187796868197/221500000000000 : ℝ)*(11089/100000 : ℝ)=(1250026242570637/1250000000000000 : ℝ) by norm_num, show 1+2*(4751516306384217/100000000000000000000 : ℝ)=(50004751516306384217/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5438663137242013/25000000000000000000 : ℝ)+(4751516306384217/100000000000000000000 : ℝ) ≤ ((11073150029704407287/11075000000000000000 : ℝ)+(187796868197/221500000000000 : ℝ)*((15519/100000 : ℝ)+(11089/100000 : ℝ)))^(4635/1024 : ℝ) := by
    rw [show (11073150029704407287/11075000000000000000 : ℝ)+(187796868197/221500000000000 : ℝ)*((15519/100000 : ℝ)+(11089/100000 : ℝ))=(1000058553430149/1000000000000000 : ℝ) by norm_num, show 1+(5438663137242013/25000000000000000000 : ℝ)+(4751516306384217/100000000000000000000 : ℝ)=(100026506168855352269/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5438663137242013/25000000000000000000 : ℝ) ≤ ((11073150029704407287/11075000000000000000 : ℝ)+2*(187796868197/221500000000000 : ℝ)*(15519/100000 : ℝ))^(4635/1024 : ℝ) := by
    rw [show (11073150029704407287/11075000000000000000 : ℝ)+2*(187796868197/221500000000000 : ℝ)*(15519/100000 : ℝ)=(2500240282009471/2500000000000000 : ℝ) by norm_num, show 1+2*(5438663137242013/25000000000000000000 : ℝ)=(12505438663137242013/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11073150029704407287/11075000000000000000 : ℝ)*(X 1 0+X 2 0)+(187796868197/221500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (11089/100000 : ℝ)) (hi := (15519/100000 : ℝ)) (c := (11073150029704407287/11075000000000000000 : ℝ)) (alpha := (187796868197/221500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11073150029704407287/11075000000000000000 : ℝ)*(X 0 1+X 2 1)+(187796868197/221500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (11089/100000 : ℝ)) (hi := (15519/100000 : ℝ)) (c := (11073150029704407287/11075000000000000000 : ℝ)) (alpha := (187796868197/221500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11073150029704407287/11075000000000000000 : ℝ)*(X 0 2+X 1 2)+(187796868197/221500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (11089/100000 : ℝ)) (hi := (15519/100000 : ℝ)) (c := (11073150029704407287/11075000000000000000 : ℝ)) (alpha := (187796868197/221500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1785591043/10000000000 : ℝ)*X 0 0+(2712975503/5000000000 : ℝ)*X 0 1+(5219917007/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337058319/2500000000 : ℝ)*X 1 0+(-945499283/5000000000 : ℝ)*X 1 1+(5219917043/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348233303/10000000000 : ℝ)*X 2 0+(5219917013/10000000000 : ℝ)*X 2 1+(-189099857/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2121745293/5000000000 : ℝ)*X 0 0+(4005955633/10000000000 : ℝ)*X 0 1+(70192369/156250000 : ℝ)*X 0 2+(2121745293/5000000000 : ℝ)*X 1 0+(4005955633/10000000000 : ℝ)*X 1 1+(70192369/156250000 : ℝ)*X 1 2+(2121745293/5000000000 : ℝ)*X 2 0+(4005955633/10000000000 : ℝ)*X 2 1+(70192369/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-357123587/2000000000 : ℝ)*X 0 0+(1044198361/2000000000 : ℝ)*X 0 1+(21699473/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293722979/10000000000 : ℝ)*X 1 0+(-105377959/625000000 : ℝ)*X 1 1+(5424868251/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293722983/10000000000 : ℝ)*X 2 0+(5424868249/10000000000 : ℝ)*X 2 1+(-843023671/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4243554067/10000000000 : ℝ)*X 0 0+(2244887247/5000000000 : ℝ)*X 0 1+(801702307/2000000000 : ℝ)*X 0 2+(4243554067/10000000000 : ℝ)*X 1 0+(2244887247/5000000000 : ℝ)*X 1 1+(801702307/2000000000 : ℝ)*X 1 2+(4243554067/10000000000 : ℝ)*X 2 0+(2244887247/5000000000 : ℝ)*X 2 1+(801702307/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1323627427335431663581466571/138437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (400630091/25000000000000 : ℝ)*(base19) + (762854579/50000000000000 : ℝ)*(base23) + (54185201/100000000000000 : ℝ)*(lower2) + (23481017/10000000000000 : ℝ)*(upper3) + (32346891/20000000000000 : ℝ)*(upper5) + (863719074305037/25000000000000 : ℝ)*(major0) + (863719074305037/25000000000000 : ℝ)*(major1) + (863719074305037/25000000000000 : ℝ)*(major2) + (4853595430236911/100000000000000 : ℝ)*(sp0) + (1213405149751407/25000000000000 : ℝ)*(sp1) + (970724135163367/20000000000000 : ℝ)*(sp2) + (1028058976086787/50000000000000 : ℝ)*(sp3) + (13385644541/50000000000000 : ℝ)*(sp4) + (12122034341/100000000000000 : ℝ)*(sp7) + (411226014841583/20000000000000 : ℝ)*(f.failure) + (606702775190749/12500000000000 : ℝ)*(f.sum) + (7979781533139/2768750000000000000000000000 : ℝ)*base65 + (2722398921871945381/276875000000000000000000000000000 : ℝ)*base68 + (3291226045891945381/276875000000000000000000000000000 : ℝ)*base70 + (990952877047570381/276875000000000000000000000000000 : ℝ)*base72 + (8976575230743/1384375000000000000000000000 : ℝ)*base74 + (3337914404805070381/276875000000000000000000000000000 : ℝ)*base76 + (1404653598241945381/276875000000000000000000000000000 : ℝ)*base78 + (4998742898057570381/276875000000000000000000000000000 : ℝ)*base80 + (11200474906019/11075000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (324823/20000000000000000000 : ℝ)*base89 + (324823/20000000000000000000 : ℝ)*base91 + (324823/20000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (387359662416852817971/43261718750000000000000000 : ℝ) := by norm_num
    linear_combination (707527453/50000000000000 : ℝ)*(base19) + (382543007/25000000000000 : ℝ)*(base23) + (9196973/5000000000000 : ℝ)*(upper3) + (2534837/5000000000000 : ℝ)*(lower4) + (188891877/100000000000000 : ℝ)*(upper5) + (872849605818947/25000000000000 : ℝ)*(major0) + (872849605818947/25000000000000 : ℝ)*(major1) + (872849605818947/25000000000000 : ℝ)*(major2) + (226374511/1000000000000 : ℝ)*(sp1) + (12078311139/50000000000000 : ℝ)*(sp2) + (4904930748692823/100000000000000 : ℝ)*(sp4) + (76639167127919/1562500000000 : ℝ)*(sp5) + (4904905061898517/100000000000000 : ℝ)*(sp6) + (1038932899698261/50000000000000 : ℝ)*(sp7) + (1038932899698261/50000000000000 : ℝ)*(f.failure) + (4904930748692823/100000000000000 : ℝ)*(f.sum) + (29420785070061/11075000000000000000000000000 : ℝ)*base65 + (708933095379291789/276875000000000000000000000000000 : ℝ)*base67 + (819149934634916789/276875000000000000000000000000000 : ℝ)*base69 + (126780328598833211/276875000000000000000000000000000 : ℝ)*base72 + (4258689269871/692187500000000000000000000 : ℝ)*base73 + (110238140451333211/276875000000000000000000000000000 : ℝ)*base76 + (1016992516661791789/276875000000000000000000000000000 : ℝ)*base77 + (3924621758730708211/276875000000000000000000000000000 : ℝ)*base80 + (2247716854173/346093750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (308659/50000000000000000000 : ℝ)*base90 + (308659/50000000000000000000 : ℝ)*base92 + (308659/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1570_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15519/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11089/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5559/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1570_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1570_s5_0 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-892806407/5000000000 : ℝ)*x 0 + (1085160107/2000000000 : ℝ)*x 1 + (2610026537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (892806407/5000000000 : ℝ)^4637 ≤ (10957919751017/100000000000000 : ℝ)^3613 := by
    have hnat : (892806407 : ℕ)^4637*100000000000000^3613 ≤ 10957919751017^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892806407 5000000000 10957919751017 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085160107/2000000000 : ℝ)^4637 ≤ (45625254594547/100000000000000 : ℝ)^3613 := by
    have hnat : (1085160107 : ℕ)^4637*100000000000000^3613 ≤ 45625254594547^3613*2000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085160107 2000000000 45625254594547 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610026537/5000000000 : ℝ)^4637 ≤ (21708412820483/50000000000000 : ℝ)^3613 := by
    have hnat : (2610026537 : ℕ)^4637*50000000000000^3613 ≤ 21708412820483^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610026537 5000000000 21708412820483 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-892806407/5000000000 : ℝ), (1085160107/2000000000 : ℝ), (2610026537/5000000000 : ℝ)] ![(10957919751017/100000000000000 : ℝ), (45625254594547/100000000000000 : ℝ), (21708412820483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-892806407/5000000000 : ℝ)|^4637 ≤ (10957919751017/100000000000000 : ℝ)^3613
        have hw : |(-892806407/5000000000 : ℝ)|=(892806407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085160107/2000000000 : ℝ)|^4637 ≤ (45625254594547/100000000000000 : ℝ)^3613
        have hw : |(1085160107/2000000000 : ℝ)|=(1085160107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610026537/5000000000 : ℝ)|^4637 ≤ (21708412820483/50000000000000 : ℝ)^3613
        have hw : |(2610026537/5000000000 : ℝ)|=(2610026537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s5_1 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348191651/10000000000 : ℝ)*x 0 + (-945434553/5000000000 : ℝ)*x 1 + (5220056039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348191651/10000000000 : ℝ)^4637 ≤ (44789386367333/100000000000000 : ℝ)^3613 := by
    have hnat : (5348191651 : ℕ)^4637*100000000000000^3613 ≤ 44789386367333^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348191651 10000000000 44789386367333 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (945434553/5000000000 : ℝ)^4637 ≤ (5896878159417/50000000000000 : ℝ)^3613 := by
    have hnat : (945434553 : ℕ)^4637*50000000000000^3613 ≤ 5896878159417^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945434553 5000000000 5896878159417 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220056039/10000000000 : ℝ)^4637 ≤ (43416857291207/100000000000000 : ℝ)^3613 := by
    have hnat : (5220056039 : ℕ)^4637*100000000000000^3613 ≤ 43416857291207^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220056039 10000000000 43416857291207 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348191651/10000000000 : ℝ), (-945434553/5000000000 : ℝ), (5220056039/10000000000 : ℝ)] ![(44789386367333/100000000000000 : ℝ), (5896878159417/50000000000000 : ℝ), (43416857291207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348191651/10000000000 : ℝ)|^4637 ≤ (44789386367333/100000000000000 : ℝ)^3613
        have hw : |(5348191651/10000000000 : ℝ)|=(5348191651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-945434553/5000000000 : ℝ)|^4637 ≤ (5896878159417/50000000000000 : ℝ)^3613
        have hw : |(-945434553/5000000000 : ℝ)|=(945434553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220056039/10000000000 : ℝ)|^4637 ≤ (43416857291207/100000000000000 : ℝ)^3613
        have hw : |(5220056039/10000000000 : ℝ)|=(5220056039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s5_2 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167131127/312500000 : ℝ)*x 0 + (2610024953/5000000000 : ℝ)*x 1 + (-1890871359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167131127/312500000 : ℝ)^4637 ≤ (22394716899657/50000000000000 : ℝ)^3613 := by
    have hnat : (167131127 : ℕ)^4637*50000000000000^3613 ≤ 22394716899657^3613*312500000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167131127 312500000 22394716899657 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610024953/5000000000 : ℝ)^4637 ≤ (5427098977973/12500000000000 : ℝ)^3613 := by
    have hnat : (2610024953 : ℕ)^4637*12500000000000^3613 ≤ 5427098977973^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610024953 5000000000 5427098977973 12500000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1890871359/10000000000 : ℝ)^4637 ≤ (11793774354039/100000000000000 : ℝ)^3613 := by
    have hnat : (1890871359 : ℕ)^4637*100000000000000^3613 ≤ 11793774354039^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1890871359 10000000000 11793774354039 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167131127/312500000 : ℝ), (2610024953/5000000000 : ℝ), (-1890871359/10000000000 : ℝ)] ![(22394716899657/50000000000000 : ℝ), (5427098977973/12500000000000 : ℝ), (11793774354039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167131127/312500000 : ℝ)|^4637 ≤ (22394716899657/50000000000000 : ℝ)^3613
        have hw : |(167131127/312500000 : ℝ)|=(167131127/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610024953/5000000000 : ℝ)|^4637 ≤ (5427098977973/12500000000000 : ℝ)^3613
        have hw : |(2610024953/5000000000 : ℝ)|=(2610024953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1890871359/10000000000 : ℝ)|^4637 ≤ (11793774354039/100000000000000 : ℝ)^3613
        have hw : |(-1890871359/10000000000 : ℝ)|=(1890871359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s5_3 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4243507237/10000000000 : ℝ)*x 0 + (4006292333/10000000000 : ℝ)*x 1 + (2245984641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4243507237/10000000000 : ℝ)^4637 ≤ (3328238092869/10000000000000 : ℝ)^3613 := by
    have hnat : (4243507237 : ℕ)^4637*10000000000000^3613 ≤ 3328238092869^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243507237 10000000000 3328238092869 10000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4006292333/10000000000 : ℝ)^4637 ≤ (30913741038131/100000000000000 : ℝ)^3613 := by
    have hnat : (4006292333 : ℕ)^4637*100000000000000^3613 ≤ 30913741038131^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4006292333 10000000000 30913741038131 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245984641/5000000000 : ℝ)^4637 ≤ (35803878007019/100000000000000 : ℝ)^3613 := by
    have hnat : (2245984641 : ℕ)^4637*100000000000000^3613 ≤ 35803878007019^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245984641 5000000000 35803878007019 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4243507237/10000000000 : ℝ), (4006292333/10000000000 : ℝ), (2245984641/5000000000 : ℝ)] ![(3328238092869/10000000000000 : ℝ), (30913741038131/100000000000000 : ℝ), (35803878007019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4243507237/10000000000 : ℝ)|^4637 ≤ (3328238092869/10000000000000 : ℝ)^3613
        have hw : |(4243507237/10000000000 : ℝ)|=(4243507237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4006292333/10000000000 : ℝ)|^4637 ≤ (30913741038131/100000000000000 : ℝ)^3613
        have hw : |(4006292333/10000000000 : ℝ)|=(4006292333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2245984641/5000000000 : ℝ)|^4637 ≤ (35803878007019/100000000000000 : ℝ)^3613
        have hw : |(2245984641/5000000000 : ℝ)|=(2245984641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s5_4 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1785639689/10000000000 : ℝ)*x 0 + (5221125281/10000000000 : ℝ)*x 1 + (5424720337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1785639689/10000000000 : ℝ)^4637 ≤ (136976642763/1250000000000 : ℝ)^3613 := by
    have hnat : (1785639689 : ℕ)^4637*1250000000000^3613 ≤ 136976642763^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1785639689 10000000000 136976642763 1250000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221125281/10000000000 : ℝ)^4637 ≤ (21714135686339/50000000000000 : ℝ)^3613 := by
    have hnat : (5221125281 : ℕ)^4637*50000000000000^3613 ≤ 21714135686339^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221125281 10000000000 21714135686339 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424720337/10000000000 : ℝ)^4637 ≤ (22806798596897/50000000000000 : ℝ)^3613 := by
    have hnat : (5424720337 : ℕ)^4637*50000000000000^3613 ≤ 22806798596897^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424720337 10000000000 22806798596897 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1785639689/10000000000 : ℝ), (5221125281/10000000000 : ℝ), (5424720337/10000000000 : ℝ)] ![(136976642763/1250000000000 : ℝ), (21714135686339/50000000000000 : ℝ), (22806798596897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1785639689/10000000000 : ℝ)|^4637 ≤ (136976642763/1250000000000 : ℝ)^3613
        have hw : |(-1785639689/10000000000 : ℝ)|=(1785639689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221125281/10000000000 : ℝ)|^4637 ≤ (21714135686339/50000000000000 : ℝ)^3613
        have hw : |(5221125281/10000000000 : ℝ)|=(5221125281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424720337/10000000000 : ℝ)|^4637 ≤ (22806798596897/50000000000000 : ℝ)^3613
        have hw : |(5424720337/10000000000 : ℝ)|=(5424720337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s5_5 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058751827/2000000000 : ℝ)*x 0 + (-337240659/2000000000 : ℝ)*x 1 + (2712360181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058751827/2000000000 : ℝ)^4637 ≤ (4420517859523/10000000000000 : ℝ)^3613 := by
    have hnat : (1058751827 : ℕ)^4637*10000000000000^3613 ≤ 4420517859523^3613*2000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058751827 2000000000 4420517859523 10000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337240659/2000000000 : ℝ)^4637 ≤ (5090611964221/50000000000000 : ℝ)^3613 := by
    have hnat : (337240659 : ℕ)^4637*50000000000000^3613 ≤ 5090611964221^3613*2000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337240659 2000000000 5090611964221 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712360181/5000000000 : ℝ)^4637 ≤ (1425424920737/3125000000000 : ℝ)^3613 := by
    have hnat : (2712360181 : ℕ)^4637*3125000000000^3613 ≤ 1425424920737^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712360181 5000000000 1425424920737 3125000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058751827/2000000000 : ℝ), (-337240659/2000000000 : ℝ), (2712360181/5000000000 : ℝ)] ![(4420517859523/10000000000000 : ℝ), (5090611964221/50000000000000 : ℝ), (1425424920737/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058751827/2000000000 : ℝ)|^4637 ≤ (4420517859523/10000000000000 : ℝ)^3613
        have hw : |(1058751827/2000000000 : ℝ)|=(1058751827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-337240659/2000000000 : ℝ)|^4637 ≤ (5090611964221/50000000000000 : ℝ)^3613
        have hw : |(-337240659/2000000000 : ℝ)|=(337240659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712360181/5000000000 : ℝ)|^4637 ≤ (1425424920737/3125000000000 : ℝ)^3613
        have hw : |(2712360181/5000000000 : ℝ)|=(2712360181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s5_6 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330859939/625000000 : ℝ)*x 0 + (2712360257/5000000000 : ℝ)*x 1 + (-421550809/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330859939/625000000 : ℝ)^4637 ≤ (4420517740563/10000000000000 : ℝ)^3613 := by
    have hnat : (330859939 : ℕ)^4637*10000000000000^3613 ≤ 4420517740563^3613*625000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330859939 625000000 4420517740563 10000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712360257/5000000000 : ℝ)^4637 ≤ (11403399775977/25000000000000 : ℝ)^3613 := by
    have hnat : (2712360257 : ℕ)^4637*25000000000000^3613 ≤ 11403399775977^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712360257 5000000000 11403399775977 25000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (421550809/2500000000 : ℝ)^4637 ≤ (10181223471237/100000000000000 : ℝ)^3613 := by
    have hnat : (421550809 : ℕ)^4637*100000000000000^3613 ≤ 10181223471237^3613*2500000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421550809 2500000000 10181223471237 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330859939/625000000 : ℝ), (2712360257/5000000000 : ℝ), (-421550809/2500000000 : ℝ)] ![(4420517740563/10000000000000 : ℝ), (11403399775977/25000000000000 : ℝ), (10181223471237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330859939/625000000 : ℝ)|^4637 ≤ (4420517740563/10000000000000 : ℝ)^3613
        have hw : |(330859939/625000000 : ℝ)|=(330859939/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712360257/5000000000 : ℝ)|^4637 ≤ (11403399775977/25000000000000 : ℝ)^3613
        have hw : |(2712360257/5000000000 : ℝ)|=(2712360257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-421550809/2500000000 : ℝ)|^4637 ≤ (10181223471237/100000000000000 : ℝ)^3613
        have hw : |(-421550809/2500000000 : ℝ)|=(421550809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s5_7 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4243567941/10000000000 : ℝ)*x 0 + (448944101/1000000000 : ℝ)*x 1 + (4008841803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4243567941/10000000000 : ℝ)^4637 ≤ (4160373997339/12500000000000 : ℝ)^3613 := by
    have hnat : (4243567941 : ℕ)^4637*12500000000000^3613 ≤ 4160373997339^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243567941 10000000000 4160373997339 12500000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448944101/1000000000 : ℝ)^4637 ≤ (3577801663423/10000000000000 : ℝ)^3613 := by
    have hnat : (448944101 : ℕ)^4637*10000000000000^3613 ≤ 3577801663423^3613*1000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448944101 1000000000 3577801663423 10000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4008841803/10000000000 : ℝ)^4637 ≤ (30938991372051/100000000000000 : ℝ)^3613 := by
    have hnat : (4008841803 : ℕ)^4637*100000000000000^3613 ≤ 30938991372051^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4008841803 10000000000 30938991372051 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4243567941/10000000000 : ℝ), (448944101/1000000000 : ℝ), (4008841803/10000000000 : ℝ)] ![(4160373997339/12500000000000 : ℝ), (3577801663423/10000000000000 : ℝ), (30938991372051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4243567941/10000000000 : ℝ)|^4637 ≤ (4160373997339/12500000000000 : ℝ)^3613
        have hw : |(4243567941/10000000000 : ℝ)|=(4243567941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448944101/1000000000 : ℝ)|^4637 ≤ (3577801663423/10000000000000 : ℝ)^3613
        have hw : |(448944101/1000000000 : ℝ)|=(448944101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4008841803/10000000000 : ℝ)|^4637 ≤ (30938991372051/100000000000000 : ℝ)^3613
        have hw : |(4008841803/10000000000 : ℝ)|=(4008841803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1570_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5559/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11121/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5559/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5559/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5559/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5559/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5559/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5559/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5559/50000 : ℝ) ^ (4635/1024 : ℝ) ≤ (4808021709909503/100000000000000000000 : ℝ) := by
    have hpowers : (5559/50000 : ℝ)^4635 ≤ (4808021709909503/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5559 : ℕ)^4635*100000000000000000000^1024 ≤ 4808021709909503^1024*50000^4635 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5559 50000 4808021709909503 100000000000000000000 4635 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5559/50000 : ℝ)) (X := (4808021709909503/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4635/1024 : ℝ) ≤ (21558646187255533/100000000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4635 ≤ (21558646187255533/100000000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4635*100000000000000000000^1024 ≤ 21558646187255533^1024*3125^4635 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 21558646187255533 100000000000000000000 4635 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (21558646187255533/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004808021709909503/50000000000000000000 : ℝ) ≤ (2500053109275301/2500000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (50004808021709909503/50000000000000000000 : ℝ)^1024 ≤ (2500053109275301/2500000000000000 : ℝ)^4635 := by
      have hnat : (50004808021709909503 : ℕ)^1024*2500000000000000^4635 ≤ 2500053109275301^4635*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004808021709909503 50000000000000000000 2500053109275301 2500000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500053109275301/2500000000000000 : ℝ)) (X := (50004808021709909503/50000000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25006591666974291259/25000000000000000000 : ℝ) ≤ (5000291226486591/5000000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (25006591666974291259/25000000000000000000 : ℝ)^1024 ≤ (5000291226486591/5000000000000000 : ℝ)^4635 := by
      have hnat : (25006591666974291259 : ℕ)^1024*5000000000000000^4635 ≤ 5000291226486591^4635*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006591666974291259 25000000000000000000 5000291226486591 5000000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000291226486591/5000000000000000 : ℝ)) (X := (25006591666974291259/25000000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021558646187255533/50000000000000000000 : ℝ) ≤ (250023811721129/250000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (50021558646187255533/50000000000000000000 : ℝ)^1024 ≤ (250023811721129/250000000000000 : ℝ)^4635 := by
      have hnat : (50021558646187255533 : ℕ)^1024*250000000000000^4635 ≤ 250023811721129^4635*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021558646187255533 50000000000000000000 250023811721129 250000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250023811721129/250000000000000 : ℝ)) (X := (50021558646187255533/50000000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4808021709909503/100000000000000000000 : ℝ) ≤ ((2730793792325184917/2731250000000000000 : ℝ)+2*(185007935989/218500000000000 : ℝ)*(5559/50000 : ℝ))^(4635/1024 : ℝ) := by
    rw [show (2730793792325184917/2731250000000000000 : ℝ)+2*(185007935989/218500000000000 : ℝ)*(5559/50000 : ℝ)=(2500053109275301/2500000000000000 : ℝ) by norm_num, show 1+2*(4808021709909503/100000000000000000000 : ℝ)=(50004808021709909503/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21558646187255533/100000000000000000000 : ℝ)+(4808021709909503/100000000000000000000 : ℝ) ≤ ((2730793792325184917/2731250000000000000 : ℝ)+(185007935989/218500000000000 : ℝ)*((484/3125 : ℝ)+(5559/50000 : ℝ)))^(4635/1024 : ℝ) := by
    rw [show (2730793792325184917/2731250000000000000 : ℝ)+(185007935989/218500000000000 : ℝ)*((484/3125 : ℝ)+(5559/50000 : ℝ))=(5000291226486591/5000000000000000 : ℝ) by norm_num, show 1+(21558646187255533/100000000000000000000 : ℝ)+(4808021709909503/100000000000000000000 : ℝ)=(25006591666974291259/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21558646187255533/100000000000000000000 : ℝ) ≤ ((2730793792325184917/2731250000000000000 : ℝ)+2*(185007935989/218500000000000 : ℝ)*(484/3125 : ℝ))^(4635/1024 : ℝ) := by
    rw [show (2730793792325184917/2731250000000000000 : ℝ)+2*(185007935989/218500000000000 : ℝ)*(484/3125 : ℝ)=(250023811721129/250000000000000 : ℝ) by norm_num, show 1+2*(21558646187255533/100000000000000000000 : ℝ)=(50021558646187255533/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2730793792325184917/2731250000000000000 : ℝ)*(X 1 0+X 2 0)+(185007935989/218500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (5559/50000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (2730793792325184917/2731250000000000000 : ℝ)) (alpha := (185007935989/218500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2730793792325184917/2731250000000000000 : ℝ)*(X 0 1+X 2 1)+(185007935989/218500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (5559/50000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (2730793792325184917/2731250000000000000 : ℝ)) (alpha := (185007935989/218500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2730793792325184917/2731250000000000000 : ℝ)*(X 0 2+X 1 2)+(185007935989/218500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (5559/50000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (2730793792325184917/2731250000000000000 : ℝ)) (alpha := (185007935989/218500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-892806407/5000000000 : ℝ)*X 0 0+(1085160107/2000000000 : ℝ)*X 0 1+(2610026537/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348191651/10000000000 : ℝ)*X 1 0+(-945434553/5000000000 : ℝ)*X 1 1+(5220056039/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167131127/312500000 : ℝ)*X 2 0+(2610024953/5000000000 : ℝ)*X 2 1+(-1890871359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4243507237/10000000000 : ℝ)*X 0 0+(4006292333/10000000000 : ℝ)*X 0 1+(2245984641/5000000000 : ℝ)*X 0 2+(4243507237/10000000000 : ℝ)*X 1 0+(4006292333/10000000000 : ℝ)*X 1 1+(2245984641/5000000000 : ℝ)*X 1 2+(4243507237/10000000000 : ℝ)*X 2 0+(4006292333/10000000000 : ℝ)*X 2 1+(2245984641/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1785639689/10000000000 : ℝ)*X 0 0+(5221125281/10000000000 : ℝ)*X 0 1+(5424720337/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058751827/2000000000 : ℝ)*X 1 0+(-337240659/2000000000 : ℝ)*X 1 1+(2712360181/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330859939/625000000 : ℝ)*X 2 0+(2712360257/5000000000 : ℝ)*X 2 1+(-421550809/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4243567941/10000000000 : ℝ)*X 0 0+(448944101/1000000000 : ℝ)*X 0 1+(4008841803/10000000000 : ℝ)*X 0 2+(4243567941/10000000000 : ℝ)*X 1 0+(448944101/1000000000 : ℝ)*X 1 1+(4008841803/10000000000 : ℝ)*X 1 2+(4243567941/10000000000 : ℝ)*X 2 0+(448944101/1000000000 : ℝ)*X 2 1+(4008841803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (356542508263196414794328511/68281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1180106243/25000000000000 : ℝ)*(base23) + (13217971/12500000000000 : ℝ)*(lower2) + (32982323/5000000000000 : ℝ)*(upper3) + (270500749/50000000000000 : ℝ)*(lower4) + (1729854014323337/50000000000000 : ℝ)*(major0) + (1729854014323337/50000000000000 : ℝ)*(major1) + (1729854014323337/50000000000000 : ℝ)*(major2) + (4860372077161823/100000000000000 : ℝ)*(sp0) + (4860410259388469/100000000000000 : ℝ)*(sp1) + (607549416103579/12500000000000 : ℝ)*(sp2) + (1029493378425341/50000000000000 : ℝ)*(sp3) + (19091113323/50000000000000 : ℝ)*(sp4) + (2042026973/20000000000000 : ℝ)*(sp6) + (18866998349/100000000000000 : ℝ)*(sp7) + (257375702981129/12500000000000 : ℝ)*(f.failure) + (4860410259388469/100000000000000 : ℝ)*(f.sum) + (45596734605611/10925000000000000000000000000 : ℝ)*base65 + (363553261592516971/136562500000000000000000000000000 : ℝ)*base68 + (1944032144991266971/136562500000000000000000000000000 : ℝ)*base70 + (694862208028454471/136562500000000000000000000000000 : ℝ)*base72 + (726068893199/170703125000000000000000000 : ℝ)*base73 + (1425684688809704471/136562500000000000000000000000000 : ℝ)*base76 + (554503801620016971/136562500000000000000000000000000 : ℝ)*base78 + (1130545122257204471/136562500000000000000000000000000 : ℝ)*base80 + (7500923256689/10925000000000000000000000000 : ℝ)*base82 + (167249/12500000000000000000 : ℝ)*base89 + (167249/12500000000000000000 : ℝ)*base91 + (167249/12500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1246052141553833093286081/112304687500000000000000000000 : ℝ) := by norm_num
    linear_combination (1502597461/100000000000000 : ℝ)*(base19) + (1693210807/100000000000000 : ℝ)*(base23) + (18322489/4000000000000 : ℝ)*(lower1) + (60424333/25000000000000 : ℝ)*(upper3) + (118880599/100000000000000 : ℝ)*(lower4) + (82375089/50000000000000 : ℝ)*(upper5) + (437025615630437/12500000000000 : ℝ)*(major0) + (437025615630437/12500000000000 : ℝ)*(major1) + (437025615630437/12500000000000 : ℝ)*(major2) + (268531777/4000000000000 : ℝ)*(sp2) + (982336629269841/20000000000000 : ℝ)*(sp4) + (76745025683621/1562500000000 : ℝ)*(sp5) + (4911674739843973/100000000000000 : ℝ)*(sp6) + (2080726333895043/100000000000000 : ℝ)*(sp7) + (2080726333895043/100000000000000 : ℝ)*(f.failure) + (982336629269841/20000000000000 : ℝ)*(f.sum) + (36691900589553/5462500000000000000000000000 : ℝ)*base66 + (296688550656057823/17070312500000000000000000000000 : ℝ)*base68 + (244593047876412521/34140625000000000000000000000000 : ℝ)*base70 + (1410296048433160927/17070312500000000000000000000000 : ℝ)*base71 + (7264303049397/5462500000000000000000000000 : ℝ)*base73 + (710524536953302349/8535156250000000000000000000000 : ℝ)*base76 + (27139046759964073/17070312500000000000000000000000 : ℝ)*base78 + (137772222455149979/34140625000000000000000000000000 : ℝ)*base79 + (13674526692003/5462500000000000000000000000 : ℝ)*base82 + (747083/100000000000000000000 : ℝ)*base89 + (747083/100000000000000000000 : ℝ)*base91 + (747083/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1570_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5559/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1570_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1570_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3953/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (541/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1570_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1570_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1570_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3953/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (541/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1570_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

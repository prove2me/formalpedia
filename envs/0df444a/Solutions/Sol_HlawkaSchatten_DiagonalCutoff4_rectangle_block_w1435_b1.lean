-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1435_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:55:14.820663+00:00
-- url     : https://prove2.me/submissions/3f33a07d-0a41-47f9-aae6-dd28316395c1

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
theorem support_rectangle_w1435_s3_0 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-122828347/625000000 : ℝ)*x 0 + (2708339029/5000000000 : ℝ)*x 1 + (2619470979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (122828347/625000000 : ℝ)^4395 ≤ (2397795649513/20000000000000 : ℝ)^3371 := by
    have hnat : (122828347 : ℕ)^4395*20000000000000^3371 ≤ 2397795649513^3371*625000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122828347 625000000 2397795649513 20000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708339029/5000000000 : ℝ)^4395 ≤ (44962431524749/100000000000000 : ℝ)^3371 := by
    have hnat : (2708339029 : ℕ)^4395*100000000000000^3371 ≤ 44962431524749^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708339029 5000000000 44962431524749 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619470979/5000000000 : ℝ)^4395 ≤ (21524295107181/50000000000000 : ℝ)^3371 := by
    have hnat : (2619470979 : ℕ)^4395*50000000000000^3371 ≤ 21524295107181^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619470979 5000000000 21524295107181 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-122828347/625000000 : ℝ), (2708339029/5000000000 : ℝ), (2619470979/5000000000 : ℝ)] ![(2397795649513/20000000000000 : ℝ), (44962431524749/100000000000000 : ℝ), (21524295107181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-122828347/625000000 : ℝ)|^4395 ≤ (2397795649513/20000000000000 : ℝ)^3371
        have hw : |(-122828347/625000000 : ℝ)|=(122828347/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708339029/5000000000 : ℝ)|^4395 ≤ (44962431524749/100000000000000 : ℝ)^3371
        have hw : |(2708339029/5000000000 : ℝ)|=(2708339029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619470979/5000000000 : ℝ)|^4395 ≤ (21524295107181/50000000000000 : ℝ)^3371
        have hw : |(2619470979/5000000000 : ℝ)|=(2619470979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s3_1 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337366419/2500000000 : ℝ)*x 0 + (-2055906437/10000000000 : ℝ)*x 1 + (5238941779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337366419/2500000000 : ℝ)^4395 ≤ (8847283655151/20000000000000 : ℝ)^3371 := by
    have hnat : (1337366419 : ℕ)^4395*20000000000000^3371 ≤ 8847283655151^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337366419 2500000000 8847283655151 20000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2055906437/10000000000 : ℝ)^4395 ≤ (12714993418859/100000000000000 : ℝ)^3371 := by
    have hnat : (2055906437 : ℕ)^4395*100000000000000^3371 ≤ 12714993418859^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055906437 10000000000 12714993418859 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238941779/10000000000 : ℝ)^4395 ≤ (10762147074179/25000000000000 : ℝ)^3371 := by
    have hnat : (5238941779 : ℕ)^4395*25000000000000^3371 ≤ 10762147074179^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238941779 10000000000 10762147074179 25000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337366419/2500000000 : ℝ), (-2055906437/10000000000 : ℝ), (5238941779/10000000000 : ℝ)] ![(8847283655151/20000000000000 : ℝ), (12714993418859/100000000000000 : ℝ), (10762147074179/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337366419/2500000000 : ℝ)|^4395 ≤ (8847283655151/20000000000000 : ℝ)^3371
        have hw : |(1337366419/2500000000 : ℝ)|=(1337366419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2055906437/10000000000 : ℝ)|^4395 ≤ (12714993418859/100000000000000 : ℝ)^3371
        have hw : |(-2055906437/10000000000 : ℝ)|=(2055906437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238941779/10000000000 : ℝ)|^4395 ≤ (10762147074179/25000000000000 : ℝ)^3371
        have hw : |(5238941779/10000000000 : ℝ)|=(5238941779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s3_2 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674732837/5000000000 : ℝ)*x 0 + (2619470843/5000000000 : ℝ)*x 1 + (-2055906563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674732837/5000000000 : ℝ)^4395 ≤ (44236418254193/100000000000000 : ℝ)^3371 := by
    have hnat : (2674732837 : ℕ)^4395*100000000000000^3371 ≤ 44236418254193^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674732837 5000000000 44236418254193 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619470843/5000000000 : ℝ)^4395 ≤ (43048587300397/100000000000000 : ℝ)^3371 := by
    have hnat : (2619470843 : ℕ)^4395*100000000000000^3371 ≤ 43048587300397^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619470843 5000000000 43048587300397 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2055906563/10000000000 : ℝ)^4395 ≤ (2542998886967/20000000000000 : ℝ)^3371 := by
    have hnat : (2055906563 : ℕ)^4395*20000000000000^3371 ≤ 2542998886967^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055906563 10000000000 2542998886967 20000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674732837/5000000000 : ℝ), (2619470843/5000000000 : ℝ), (-2055906563/10000000000 : ℝ)] ![(44236418254193/100000000000000 : ℝ), (43048587300397/100000000000000 : ℝ), (2542998886967/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674732837/5000000000 : ℝ)|^4395 ≤ (44236418254193/100000000000000 : ℝ)^3371
        have hw : |(2674732837/5000000000 : ℝ)|=(2674732837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619470843/5000000000 : ℝ)|^4395 ≤ (43048587300397/100000000000000 : ℝ)^3371
        have hw : |(2619470843/5000000000 : ℝ)|=(2619470843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2055906563/10000000000 : ℝ)|^4395 ≤ (2542998886967/20000000000000 : ℝ)^3371
        have hw : |(-2055906563/10000000000 : ℝ)|=(2055906563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s3_3 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2151125669/5000000000 : ℝ)*x 0 + (41134471/100000000 : ℝ)*x 1 + (4498794567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151125669/5000000000 : ℝ)^4395 ≤ (16649242975491/50000000000000 : ℝ)^3371 := by
    have hnat : (2151125669 : ℕ)^4395*50000000000000^3371 ≤ 16649242975491^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151125669 5000000000 16649242975491 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41134471/100000000 : ℝ)^4395 ≤ (7851529173559/25000000000000 : ℝ)^3371 := by
    have hnat : (41134471 : ℕ)^4395*25000000000000^3371 ≤ 7851529173559^3371*100000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41134471 100000000 7851529173559 25000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498794567/10000000000 : ℝ)^4395 ≤ (35295397338281/100000000000000 : ℝ)^3371 := by
    have hnat : (4498794567 : ℕ)^4395*100000000000000^3371 ≤ 35295397338281^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498794567 10000000000 35295397338281 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151125669/5000000000 : ℝ), (41134471/100000000 : ℝ), (4498794567/10000000000 : ℝ)] ![(16649242975491/50000000000000 : ℝ), (7851529173559/25000000000000 : ℝ), (35295397338281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151125669/5000000000 : ℝ)|^4395 ≤ (16649242975491/50000000000000 : ℝ)^3371
        have hw : |(2151125669/5000000000 : ℝ)|=(2151125669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41134471/100000000 : ℝ)|^4395 ≤ (7851529173559/25000000000000 : ℝ)^3371
        have hw : |(41134471/100000000 : ℝ)|=(41134471/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4498794567/10000000000 : ℝ)|^4395 ≤ (35295397338281/100000000000000 : ℝ)^3371
        have hw : |(4498794567/10000000000 : ℝ)|=(4498794567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s3_4 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1965268423/10000000000 : ℝ)*x 0 + (65495627/125000000 : ℝ)*x 1 + (5415966039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1965268423/10000000000 : ℝ)^4395 ≤ (11989096525677/100000000000000 : ℝ)^3371 := by
    have hnat : (1965268423 : ℕ)^4395*100000000000000^3371 ≤ 11989096525677^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965268423 10000000000 11989096525677 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65495627/125000000 : ℝ)^4395 ≤ (21528088707237/50000000000000 : ℝ)^3371 := by
    have hnat : (65495627 : ℕ)^4395*50000000000000^3371 ≤ 21528088707237^3371*125000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65495627 125000000 21528088707237 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415966039/10000000000 : ℝ)^4395 ≤ (44954726042857/100000000000000 : ℝ)^3371 := by
    have hnat : (5415966039 : ℕ)^4395*100000000000000^3371 ≤ 44954726042857^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415966039 10000000000 44954726042857 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1965268423/10000000000 : ℝ), (65495627/125000000 : ℝ), (5415966039/10000000000 : ℝ)] ![(11989096525677/100000000000000 : ℝ), (21528088707237/50000000000000 : ℝ), (44954726042857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1965268423/10000000000 : ℝ)|^4395 ≤ (11989096525677/100000000000000 : ℝ)^3371
        have hw : |(-1965268423/10000000000 : ℝ)|=(1965268423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65495627/125000000 : ℝ)|^4395 ≤ (21528088707237/50000000000000 : ℝ)^3371
        have hw : |(65495627/125000000 : ℝ)|=(65495627/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415966039/10000000000 : ℝ)|^4395 ≤ (44954726042857/100000000000000 : ℝ)^3371
        have hw : |(5415966039/10000000000 : ℝ)|=(5415966039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s3_5 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060646563/2000000000 : ℝ)*x 0 + (-469720577/2500000000 : ℝ)*x 1 + (5415965993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060646563/2000000000 : ℝ)^4395 ≤ (2186931260467/5000000000000 : ℝ)^3371 := by
    have hnat : (1060646563 : ℕ)^4395*5000000000000^3371 ≤ 2186931260467^3371*2000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060646563 2000000000 2186931260467 5000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (469720577/2500000000 : ℝ)^4395 ≤ (11306649227479/100000000000000 : ℝ)^3371 := by
    have hnat : (469720577 : ℕ)^4395*100000000000000^3371 ≤ 11306649227479^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469720577 2500000000 11306649227479 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415965993/10000000000 : ℝ)^4395 ≤ (8990945109011/20000000000000 : ℝ)^3371 := by
    have hnat : (5415965993 : ℕ)^4395*20000000000000^3371 ≤ 8990945109011^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415965993 10000000000 8990945109011 20000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060646563/2000000000 : ℝ), (-469720577/2500000000 : ℝ), (5415965993/10000000000 : ℝ)] ![(2186931260467/5000000000000 : ℝ), (11306649227479/100000000000000 : ℝ), (8990945109011/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060646563/2000000000 : ℝ)|^4395 ≤ (2186931260467/5000000000000 : ℝ)^3371
        have hw : |(1060646563/2000000000 : ℝ)|=(1060646563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-469720577/2500000000 : ℝ)|^4395 ≤ (11306649227479/100000000000000 : ℝ)^3371
        have hw : |(-469720577/2500000000 : ℝ)|=(469720577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415965993/10000000000 : ℝ)|^4395 ≤ (8990945109011/20000000000000 : ℝ)^3371
        have hw : |(5415965993/10000000000 : ℝ)|=(5415965993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s3_6 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303232503/10000000000 : ℝ)*x 0 + (2707983159/5000000000 : ℝ)*x 1 + (-117430143/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303232503/10000000000 : ℝ)^4395 ≤ (43738621854443/100000000000000 : ℝ)^3371 := by
    have hnat : (5303232503 : ℕ)^4395*100000000000000^3371 ≤ 43738621854443^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303232503 10000000000 43738621854443 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707983159/5000000000 : ℝ)^4395 ≤ (2247736453107/5000000000000 : ℝ)^3371 := by
    have hnat : (2707983159 : ℕ)^4395*5000000000000^3371 ≤ 2247736453107^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707983159 5000000000 2247736453107 5000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117430143/625000000 : ℝ)^4395 ≤ (2826662267641/25000000000000 : ℝ)^3371 := by
    have hnat : (117430143 : ℕ)^4395*25000000000000^3371 ≤ 2826662267641^3371*625000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117430143 625000000 2826662267641 25000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303232503/10000000000 : ℝ), (2707983159/5000000000 : ℝ), (-117430143/625000000 : ℝ)] ![(43738621854443/100000000000000 : ℝ), (2247736453107/5000000000000 : ℝ), (2826662267641/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303232503/10000000000 : ℝ)|^4395 ≤ (43738621854443/100000000000000 : ℝ)^3371
        have hw : |(5303232503/10000000000 : ℝ)|=(5303232503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707983159/5000000000 : ℝ)|^4395 ≤ (2247736453107/5000000000000 : ℝ)^3371
        have hw : |(2707983159/5000000000 : ℝ)|=(2707983159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-117430143/625000000 : ℝ)|^4395 ≤ (2826662267641/25000000000000 : ℝ)^3371
        have hw : |(-117430143/625000000 : ℝ)|=(117430143/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s3_7 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4302284033/10000000000 : ℝ)*x 0 + (899451959/2000000000 : ℝ)*x 1 + (4114990879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302284033/10000000000 : ℝ)^4395 ≤ (2081175992033/6250000000000 : ℝ)^3371 := by
    have hnat : (4302284033 : ℕ)^4395*6250000000000^3371 ≤ 2081175992033^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302284033 10000000000 2081175992033 6250000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899451959/2000000000 : ℝ)^4395 ≤ (8819924842907/25000000000000 : ℝ)^3371 := by
    have hnat : (899451959 : ℕ)^4395*25000000000000^3371 ≤ 8819924842907^3371*2000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899451959 2000000000 8819924842907 25000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4114990879/10000000000 : ℝ)^4395 ≤ (7855371182231/25000000000000 : ℝ)^3371 := by
    have hnat : (4114990879 : ℕ)^4395*25000000000000^3371 ≤ 7855371182231^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4114990879 10000000000 7855371182231 25000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302284033/10000000000 : ℝ), (899451959/2000000000 : ℝ), (4114990879/10000000000 : ℝ)] ![(2081175992033/6250000000000 : ℝ), (8819924842907/25000000000000 : ℝ), (7855371182231/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302284033/10000000000 : ℝ)|^4395 ≤ (2081175992033/6250000000000 : ℝ)^3371
        have hw : |(4302284033/10000000000 : ℝ)|=(4302284033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899451959/2000000000 : ℝ)|^4395 ≤ (8819924842907/25000000000000 : ℝ)^3371
        have hw : |(899451959/2000000000 : ℝ)|=(899451959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4114990879/10000000000 : ℝ)|^4395 ≤ (7855371182231/25000000000000 : ℝ)^3371
        have hw : |(4114990879/10000000000 : ℝ)|=(4114990879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1435_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79202277/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11179/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (467/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15781/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15781/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15781/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15781/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15781/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15781/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10399/100000 : ℝ) ^ (2197/512 : ℝ) ≤ (3025976193295909/50000000000000000000 : ℝ) := by
    have hpowers : (10399/100000 : ℝ)^2197 ≤ (3025976193295909/50000000000000000000 : ℝ)^512 := by
      have hnat : (10399 : ℕ)^2197*50000000000000000000^512 ≤ 3025976193295909^512*100000^2197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10399 100000 3025976193295909 50000000000000000000 2197 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10399/100000 : ℝ)) (X := (3025976193295909/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hpowhi : (15781/100000 : ℝ) ^ (2197/512 : ℝ) ≤ (4529942698678853/12500000000000000000 : ℝ) := by
    have hpowers : (15781/100000 : ℝ)^2197 ≤ (4529942698678853/12500000000000000000 : ℝ)^512 := by
      have hnat : (15781 : ℕ)^2197*12500000000000000000^512 ≤ 4529942698678853^512*100000^2197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15781 100000 4529942698678853 12500000000000000000 2197 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15781/100000 : ℝ)) (X := (4529942698678853/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003025976193295909/25000000000000000000 : ℝ) ≤ (200005641248627/200000000000000 : ℝ) ^ (2197/512 : ℝ) := by
    have hpowers : (25003025976193295909/25000000000000000000 : ℝ)^512 ≤ (200005641248627/200000000000000 : ℝ)^2197 := by
      have hnat : (25003025976193295909 : ℕ)^512*200000000000000^2197 ≤ 200005641248627^2197*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003025976193295909 25000000000000000000 200005641248627 200000000000000 512 2197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200005641248627/200000000000000 : ℝ)) (X := (25003025976193295909/25000000000000000000 : ℝ)) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021145746988011321/50000000000000000000 : ℝ) ≤ (10000985422580913/10000000000000000 : ℝ) ^ (2197/512 : ℝ) := by
    have hpowers : (50021145746988011321/50000000000000000000 : ℝ)^512 ≤ (10000985422580913/10000000000000000 : ℝ)^2197 := by
      have hnat : (50021145746988011321 : ℕ)^512*10000000000000000^2197 ≤ 10000985422580913^2197*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021145746988011321 50000000000000000000 10000985422580913 10000000000000000 512 2197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000985422580913/10000000000000000 : ℝ)) (X := (50021145746988011321/50000000000000000000 : ℝ)) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254529942698678853/6250000000000000000 : ℝ) ≤ (2500422195682619/2500000000000000 : ℝ) ^ (2197/512 : ℝ) := by
    have hpowers : (6254529942698678853/6250000000000000000 : ℝ)^512 ≤ (2500422195682619/2500000000000000 : ℝ)^2197 := by
      have hnat : (6254529942698678853 : ℕ)^512*2500000000000000^2197 ≤ 2500422195682619^2197*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254529942698678853 6250000000000000000 2500422195682619 2500000000000000 512 2197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500422195682619/2500000000000000 : ℝ)) (X := (6254529942698678853/6250000000000000000 : ℝ)) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3025976193295909/50000000000000000000 : ℝ) ≤ ((26903444787807457213/26910000000000000000 : ℝ)+2*(703360149563/538200000000000 : ℝ)*(10399/100000 : ℝ))^(2197/512 : ℝ) := by
    rw [show (26903444787807457213/26910000000000000000 : ℝ)+2*(703360149563/538200000000000 : ℝ)*(10399/100000 : ℝ)=(200005641248627/200000000000000 : ℝ) by norm_num, show 1+2*(3025976193295909/50000000000000000000 : ℝ)=(25003025976193295909/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4529942698678853/12500000000000000000 : ℝ)+(3025976193295909/50000000000000000000 : ℝ) ≤ ((26903444787807457213/26910000000000000000 : ℝ)+(703360149563/538200000000000 : ℝ)*((15781/100000 : ℝ)+(10399/100000 : ℝ)))^(2197/512 : ℝ) := by
    rw [show (26903444787807457213/26910000000000000000 : ℝ)+(703360149563/538200000000000 : ℝ)*((15781/100000 : ℝ)+(10399/100000 : ℝ))=(10000985422580913/10000000000000000 : ℝ) by norm_num, show 1+(4529942698678853/12500000000000000000 : ℝ)+(3025976193295909/50000000000000000000 : ℝ)=(50021145746988011321/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4529942698678853/12500000000000000000 : ℝ) ≤ ((26903444787807457213/26910000000000000000 : ℝ)+2*(703360149563/538200000000000 : ℝ)*(15781/100000 : ℝ))^(2197/512 : ℝ) := by
    rw [show (26903444787807457213/26910000000000000000 : ℝ)+2*(703360149563/538200000000000 : ℝ)*(15781/100000 : ℝ)=(2500422195682619/2500000000000000 : ℝ) by norm_num, show 1+2*(4529942698678853/12500000000000000000 : ℝ)=(6254529942698678853/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26903444787807457213/26910000000000000000 : ℝ)*(X 1 0+X 2 0)+(703360149563/538200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2197/512 : ℝ)) (lo := (10399/100000 : ℝ)) (hi := (15781/100000 : ℝ)) (c := (26903444787807457213/26910000000000000000 : ℝ)) (alpha := (703360149563/538200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26903444787807457213/26910000000000000000 : ℝ)*(X 0 1+X 2 1)+(703360149563/538200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2197/512 : ℝ)) (lo := (10399/100000 : ℝ)) (hi := (15781/100000 : ℝ)) (c := (26903444787807457213/26910000000000000000 : ℝ)) (alpha := (703360149563/538200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26903444787807457213/26910000000000000000 : ℝ)*(X 0 2+X 1 2)+(703360149563/538200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2197/512 : ℝ)) (lo := (10399/100000 : ℝ)) (hi := (15781/100000 : ℝ)) (c := (26903444787807457213/26910000000000000000 : ℝ)) (alpha := (703360149563/538200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-122828347/625000000 : ℝ)*X 0 0+(2708339029/5000000000 : ℝ)*X 0 1+(2619470979/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337366419/2500000000 : ℝ)*X 1 0+(-2055906437/10000000000 : ℝ)*X 1 1+(5238941779/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674732837/5000000000 : ℝ)*X 2 0+(2619470843/5000000000 : ℝ)*X 2 1+(-2055906563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2151125669/5000000000 : ℝ)*X 0 0+(41134471/100000000 : ℝ)*X 0 1+(4498794567/10000000000 : ℝ)*X 0 2+(2151125669/5000000000 : ℝ)*X 1 0+(41134471/100000000 : ℝ)*X 1 1+(4498794567/10000000000 : ℝ)*X 1 2+(2151125669/5000000000 : ℝ)*X 2 0+(41134471/100000000 : ℝ)*X 2 1+(4498794567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1965268423/10000000000 : ℝ)*X 0 0+(65495627/125000000 : ℝ)*X 0 1+(5415966039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060646563/2000000000 : ℝ)*X 1 0+(-469720577/2500000000 : ℝ)*X 1 1+(5415965993/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303232503/10000000000 : ℝ)*X 2 0+(2707983159/5000000000 : ℝ)*X 2 1+(-117430143/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4302284033/10000000000 : ℝ)*X 0 0+(899451959/2000000000 : ℝ)*X 0 1+(4114990879/10000000000 : ℝ)*X 0 2+(4302284033/10000000000 : ℝ)*X 1 0+(899451959/2000000000 : ℝ)*X 1 1+(4114990879/10000000000 : ℝ)*X 1 2+(4302284033/10000000000 : ℝ)*X 2 0+(899451959/2000000000 : ℝ)*X 2 1+(4114990879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4731905810298362209320952871/448500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1782085797/100000000000000 : ℝ)*(base19) + (434876623/25000000000000 : ℝ)*(base23) + (79041903/25000000000000 : ℝ)*(upper3) + (10826189/50000000000000 : ℝ)*(upper4) + (3486341/2500000000000 : ℝ)*(upper5) + (4110727818570733/100000000000000 : ℝ)*(major0) + (4110727818570733/100000000000000 : ℝ)*(major1) + (4110727818570733/100000000000000 : ℝ)*(major2) + (5626349063111149/100000000000000 : ℝ)*(sp0) + (5626371660856929/100000000000000 : ℝ)*(sp1) + (2813185851718117/50000000000000 : ℝ)*(sp2) + (1297534938224239/50000000000000 : ℝ)*(sp3) + (24379831577/100000000000000 : ℝ)*(sp4) + (11966066437/100000000000000 : ℝ)*(sp7) + (519016368502983/20000000000000 : ℝ)*(f.failure) + (2813186721471363/50000000000000 : ℝ)*(f.sum) + (44251021327619/26910000000000000000000000000 : ℝ)*base65 + (2197903719611502871/2691000000000000000000000000000000 : ℝ)*base68 + (14763972818558502871/2691000000000000000000000000000000 : ℝ)*base70 + (27232896418296497129/2691000000000000000000000000000000 : ℝ)*base71 + (103052773392541/26910000000000000000000000000 : ℝ)*base74 + (17005344978255497129/2691000000000000000000000000000000 : ℝ)*base75 + (7861564160304497129/2691000000000000000000000000000000 : ℝ)*base77 + (12492589379046497129/2691000000000000000000000000000000 : ℝ)*base79 + (7034695542691/26910000000000000000000000000 : ℝ)*base82 + (4892291/1000000000000000000000 : ℝ)*base89 + (4892291/1000000000000000000000 : ℝ)*base91 + (4892291/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42637227100780755115037/2990000000000000000000000000 : ℝ) := by norm_num
    linear_combination (722153181/50000000000000 : ℝ)*(base19) + (85763089/6250000000000 : ℝ)*(base23) + (46191/25000000000 : ℝ)*(upper3) + (12050111/10000000000000 : ℝ)*(lower4) + (181236321/100000000000000 : ℝ)*(upper5) + (4143796133283341/100000000000000 : ℝ)*(major0) + (4143796133283341/100000000000000 : ℝ)*(major1) + (4143796133283341/100000000000000 : ℝ)*(major2) + (25489249237/100000000000000 : ℝ)*(sp1) + (2942978701/10000000000000 : ℝ)*(sp2) + (56716340875929/1000000000000 : ℝ)*(sp4) + (5671607154037301/100000000000000 : ℝ)*(sp5) + (2835801642798233/50000000000000 : ℝ)*(sp6) + (653989425910593/25000000000000 : ℝ)*(sp7) + (653989425910593/25000000000000 : ℝ)*(f.failure) + (56716340875929/1000000000000 : ℝ)*(f.sum) + (24238474239823/26910000000000000000000000000 : ℝ)*base65 + (11541076508222338633/2691000000000000000000000000000000 : ℝ)*base67 + (17738215378245661367/2691000000000000000000000000000000 : ℝ)*base70 + (14280864168689338633/2691000000000000000000000000000000 : ℝ)*base71 + (82402424030653/26910000000000000000000000000 : ℝ)*base73 + (18478655911701661367/2691000000000000000000000000000000 : ℝ)*base76 + (17990925387488338633/2691000000000000000000000000000000 : ℝ)*base77 + (11833668117945661367/2691000000000000000000000000000000 : ℝ)*base80 + (70654602853483/26910000000000000000000000000 : ℝ)*base81 + (1520261/1250000000000000000000 : ℝ)*base89 + (1520261/1250000000000000000000 : ℝ)*base91 + (1520261/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1435_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79202277/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (467/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1435_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1435_s4_0 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1966122777/10000000000 : ℝ)*x 0 + (5409229509/10000000000 : ℝ)*x 1 + (1049163613/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1966122777/10000000000 : ℝ)^4395 ≤ (5997946089663/50000000000000 : ℝ)^3371 := by
    have hnat : (1966122777 : ℕ)^4395*50000000000000^3371 ≤ 5997946089663^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966122777 10000000000 5997946089663 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409229509/10000000000 : ℝ)^4395 ≤ (1402557450969/3125000000000 : ℝ)^3371 := by
    have hnat : (5409229509 : ℕ)^4395*3125000000000^3371 ≤ 1402557450969^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409229509 10000000000 1402557450969 3125000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049163613/2000000000 : ℝ)^4395 ≤ (10780567342491/25000000000000 : ℝ)^3371 := by
    have hnat : (1049163613 : ℕ)^4395*25000000000000^3371 ≤ 10780567342491^3371*2000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049163613 2000000000 10780567342491 25000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1966122777/10000000000 : ℝ), (5409229509/10000000000 : ℝ), (1049163613/2000000000 : ℝ)] ![(5997946089663/50000000000000 : ℝ), (1402557450969/3125000000000 : ℝ), (10780567342491/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1966122777/10000000000 : ℝ)|^4395 ≤ (5997946089663/50000000000000 : ℝ)^3371
        have hw : |(-1966122777/10000000000 : ℝ)|=(1966122777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409229509/10000000000 : ℝ)|^4395 ≤ (1402557450969/3125000000000 : ℝ)^3371
        have hw : |(5409229509/10000000000 : ℝ)|=(5409229509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049163613/2000000000 : ℝ)|^4395 ≤ (10780567342491/25000000000000 : ℝ)^3371
        have hw : |(1049163613/2000000000 : ℝ)|=(1049163613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s4_1 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334221363/625000000 : ℝ)*x 0 + (-6404179/31250000 : ℝ)*x 1 + (1049163667/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334221363/625000000 : ℝ)^4395 ≤ (11053919420043/25000000000000 : ℝ)^3371 := by
    have hnat : (334221363 : ℕ)^4395*25000000000000^3371 ≤ 11053919420043^3371*625000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334221363 625000000 11053919420043 25000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6404179/31250000 : ℝ)^4395 ≤ (3165512512049/25000000000000 : ℝ)^3371 := by
    have hnat : (6404179 : ℕ)^4395*25000000000000^3371 ≤ 3165512512049^3371*31250000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6404179 31250000 3165512512049 25000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049163667/2000000000 : ℝ)^4395 ≤ (5390284032957/12500000000000 : ℝ)^3371 := by
    have hnat : (1049163667 : ℕ)^4395*12500000000000^3371 ≤ 5390284032957^3371*2000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049163667 2000000000 5390284032957 12500000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334221363/625000000 : ℝ), (-6404179/31250000 : ℝ), (1049163667/2000000000 : ℝ)] ![(11053919420043/25000000000000 : ℝ), (3165512512049/25000000000000 : ℝ), (5390284032957/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334221363/625000000 : ℝ)|^4395 ≤ (11053919420043/25000000000000 : ℝ)^3371
        have hw : |(334221363/625000000 : ℝ)|=(334221363/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6404179/31250000 : ℝ)|^4395 ≤ (3165512512049/25000000000000 : ℝ)^3371
        have hw : |(-6404179/31250000 : ℝ)|=(6404179/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049163667/2000000000 : ℝ)|^4395 ≤ (5390284032957/12500000000000 : ℝ)^3371
        have hw : |(1049163667/2000000000 : ℝ)|=(1049163667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s4_2 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673770923/5000000000 : ℝ)*x 0 + (2622909169/5000000000 : ℝ)*x 1 + (-81973489/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673770923/5000000000 : ℝ)^4395 ≤ (8843135617963/20000000000000 : ℝ)^3371 := by
    have hnat : (2673770923 : ℕ)^4395*20000000000000^3371 ≤ 8843135617963^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673770923 5000000000 8843135617963 20000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622909169/5000000000 : ℝ)^4395 ≤ (336892752311/781250000000 : ℝ)^3371 := by
    have hnat : (2622909169 : ℕ)^4395*781250000000^3371 ≤ 336892752311^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622909169 5000000000 336892752311 781250000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81973489/400000000 : ℝ)^4395 ≤ (2532409921029/20000000000000 : ℝ)^3371 := by
    have hnat : (81973489 : ℕ)^4395*20000000000000^3371 ≤ 2532409921029^3371*400000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81973489 400000000 2532409921029 20000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673770923/5000000000 : ℝ), (2622909169/5000000000 : ℝ), (-81973489/400000000 : ℝ)] ![(8843135617963/20000000000000 : ℝ), (336892752311/781250000000 : ℝ), (2532409921029/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673770923/5000000000 : ℝ)|^4395 ≤ (8843135617963/20000000000000 : ℝ)^3371
        have hw : |(2673770923/5000000000 : ℝ)|=(2673770923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622909169/5000000000 : ℝ)|^4395 ≤ (336892752311/781250000000 : ℝ)^3371
        have hw : |(2622909169/5000000000 : ℝ)|=(2622909169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-81973489/400000000 : ℝ)|^4395 ≤ (2532409921029/20000000000000 : ℝ)^3371
        have hw : |(-81973489/400000000 : ℝ)|=(81973489/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s4_3 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075696289/2500000000 : ℝ)*x 0 + (165156457/400000000 : ℝ)*x 1 + (1120800449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075696289/2500000000 : ℝ)^4395 ≤ (33303872743319/100000000000000 : ℝ)^3371 := by
    have hnat : (1075696289 : ℕ)^4395*100000000000000^3371 ≤ 33303872743319^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075696289 2500000000 33303872743319 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (165156457/400000000 : ℝ)^4395 ≤ (31560140239019/100000000000000 : ℝ)^3371 := by
    have hnat : (165156457 : ℕ)^4395*100000000000000^3371 ≤ 31560140239019^3371*400000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165156457 400000000 31560140239019 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120800449/2500000000 : ℝ)^4395 ≤ (35135987004149/100000000000000 : ℝ)^3371 := by
    have hnat : (1120800449 : ℕ)^4395*100000000000000^3371 ≤ 35135987004149^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120800449 2500000000 35135987004149 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075696289/2500000000 : ℝ), (165156457/400000000 : ℝ), (1120800449/2500000000 : ℝ)] ![(33303872743319/100000000000000 : ℝ), (31560140239019/100000000000000 : ℝ), (35135987004149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075696289/2500000000 : ℝ)|^4395 ≤ (33303872743319/100000000000000 : ℝ)^3371
        have hw : |(1075696289/2500000000 : ℝ)|=(1075696289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(165156457/400000000 : ℝ)|^4395 ≤ (31560140239019/100000000000000 : ℝ)^3371
        have hw : |(165156457/400000000 : ℝ)|=(165156457/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1120800449/2500000000 : ℝ)|^4395 ≤ (35135987004149/100000000000000 : ℝ)^3371
        have hw : |(1120800449/2500000000 : ℝ)|=(1120800449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s4_4 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1966134621/10000000000 : ℝ)*x 0 + (5246417133/10000000000 : ℝ)*x 1 + (1352156817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1966134621/10000000000 : ℝ)^4395 ≤ (11995986394497/100000000000000 : ℝ)^3371 := by
    have hnat : (1966134621 : ℕ)^4395*100000000000000^3371 ≤ 11995986394497^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966134621 10000000000 11995986394497 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246417133/10000000000 : ℝ)^4395 ≤ (5391086239871/12500000000000 : ℝ)^3371 := by
    have hnat : (5246417133 : ℕ)^4395*12500000000000^3371 ≤ 5391086239871^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246417133 10000000000 5391086239871 12500000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352156817/2500000000 : ℝ)^4395 ≤ (22437661836183/50000000000000 : ℝ)^3371 := by
    have hnat : (1352156817 : ℕ)^4395*50000000000000^3371 ≤ 22437661836183^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352156817 2500000000 22437661836183 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1966134621/10000000000 : ℝ), (5246417133/10000000000 : ℝ), (1352156817/2500000000 : ℝ)] ![(11995986394497/100000000000000 : ℝ), (5391086239871/12500000000000 : ℝ), (22437661836183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1966134621/10000000000 : ℝ)|^4395 ≤ (11995986394497/100000000000000 : ℝ)^3371
        have hw : |(-1966134621/10000000000 : ℝ)|=(1966134621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246417133/10000000000 : ℝ)|^4395 ≤ (5391086239871/12500000000000 : ℝ)^3371
        have hw : |(5246417133/10000000000 : ℝ)|=(5246417133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352156817/2500000000 : ℝ)|^4395 ≤ (22437661836183/50000000000000 : ℝ)^3371
        have hw : |(1352156817/2500000000 : ℝ)|=(1352156817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s4_5 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652517401/5000000000 : ℝ)*x 0 + (-117908009/625000000 : ℝ)*x 1 + (1081725453/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652517401/5000000000 : ℝ)^4395 ≤ (43758002748637/100000000000000 : ℝ)^3371 := by
    have hnat : (2652517401 : ℕ)^4395*100000000000000^3371 ≤ 43758002748637^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652517401 5000000000 43758002748637 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (117908009/625000000 : ℝ)^4395 ≤ (5683336793531/50000000000000 : ℝ)^3371 := by
    have hnat : (117908009 : ℕ)^4395*50000000000000^3371 ≤ 5683336793531^3371*625000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117908009 625000000 5683336793531 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081725453/2000000000 : ℝ)^4395 ≤ (22437661819957/50000000000000 : ℝ)^3371 := by
    have hnat : (1081725453 : ℕ)^4395*50000000000000^3371 ≤ 22437661819957^3371*2000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081725453 2000000000 22437661819957 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652517401/5000000000 : ℝ), (-117908009/625000000 : ℝ), (1081725453/2000000000 : ℝ)] ![(43758002748637/100000000000000 : ℝ), (5683336793531/50000000000000 : ℝ), (22437661819957/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652517401/5000000000 : ℝ)|^4395 ≤ (43758002748637/100000000000000 : ℝ)^3371
        have hw : |(2652517401/5000000000 : ℝ)|=(2652517401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-117908009/625000000 : ℝ)|^4395 ≤ (5683336793531/50000000000000 : ℝ)^3371
        have hw : |(-117908009/625000000 : ℝ)|=(117908009/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081725453/2000000000 : ℝ)|^4395 ≤ (22437661819957/50000000000000 : ℝ)^3371
        have hw : |(1081725453/2000000000 : ℝ)|=(1081725453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s4_6 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663129347/1250000000 : ℝ)*x 0 + (216345091/400000000 : ℝ)*x 1 + (-1886528167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663129347/1250000000 : ℝ)^4395 ≤ (43758002469033/100000000000000 : ℝ)^3371 := by
    have hnat : (663129347 : ℕ)^4395*100000000000000^3371 ≤ 43758002469033^3371*1250000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663129347 1250000000 43758002469033 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216345091/400000000 : ℝ)^4395 ≤ (44875323748087/100000000000000 : ℝ)^3371 := by
    have hnat : (216345091 : ℕ)^4395*100000000000000^3371 ≤ 44875323748087^3371*400000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216345091 400000000 44875323748087 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1886528167/10000000000 : ℝ)^4395 ≤ (11366673767737/100000000000000 : ℝ)^3371 := by
    have hnat : (1886528167 : ℕ)^4395*100000000000000^3371 ≤ 11366673767737^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886528167 10000000000 11366673767737 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663129347/1250000000 : ℝ), (216345091/400000000 : ℝ), (-1886528167/10000000000 : ℝ)] ![(43758002469033/100000000000000 : ℝ), (44875323748087/100000000000000 : ℝ), (11366673767737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663129347/1250000000 : ℝ)|^4395 ≤ (43758002469033/100000000000000 : ℝ)^3371
        have hw : |(663129347/1250000000 : ℝ)|=(663129347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216345091/400000000 : ℝ)|^4395 ≤ (44875323748087/100000000000000 : ℝ)^3371
        have hw : |(216345091/400000000 : ℝ)|=(216345091/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1886528167/10000000000 : ℝ)|^4395 ≤ (11366673767737/100000000000000 : ℝ)^3371
        have hw : |(-1886528167/10000000000 : ℝ)|=(1886528167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s4_7 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4302810843/10000000000 : ℝ)*x 0 + (5602379/12500000 : ℝ)*x 1 + (1032554193/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302810843/10000000000 : ℝ)^4395 ≤ (6660826391527/20000000000000 : ℝ)^3371 := by
    have hnat : (4302810843 : ℕ)^4395*20000000000000^3371 ≤ 6660826391527^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302810843 10000000000 6660826391527 20000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5602379/12500000 : ℝ)^4395 ≤ (3512271859211/10000000000000 : ℝ)^3371 := by
    have hnat : (5602379 : ℕ)^4395*10000000000000^3371 ≤ 3512271859211^3371*12500000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5602379 12500000 3512271859211 10000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032554193/2500000000 : ℝ)^4395 ≤ (31573149430681/100000000000000 : ℝ)^3371 := by
    have hnat : (1032554193 : ℕ)^4395*100000000000000^3371 ≤ 31573149430681^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032554193 2500000000 31573149430681 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302810843/10000000000 : ℝ), (5602379/12500000 : ℝ), (1032554193/2500000000 : ℝ)] ![(6660826391527/20000000000000 : ℝ), (3512271859211/10000000000000 : ℝ), (31573149430681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302810843/10000000000 : ℝ)|^4395 ≤ (6660826391527/20000000000000 : ℝ)^3371
        have hw : |(4302810843/10000000000 : ℝ)|=(4302810843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5602379/12500000 : ℝ)|^4395 ≤ (3512271859211/10000000000000 : ℝ)^3371
        have hw : |(5602379/12500000 : ℝ)|=(5602379/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032554193/2500000000 : ℝ)|^4395 ≤ (31573149430681/100000000000000 : ℝ)^3371
        have hw : |(1032554193/2500000000 : ℝ)|=(1032554193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1435_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79202277/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (467/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5663/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3697/25000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11179/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (467/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11179/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (467/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11179/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (467/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11179/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (467/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11179/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (467/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11179/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11179/100000 : ℝ) ^ (2197/512 : ℝ) ≤ (8254337385709977/100000000000000000000 : ℝ) := by
    have hpowers : (11179/100000 : ℝ)^2197 ≤ (8254337385709977/100000000000000000000 : ℝ)^512 := by
      have hnat : (11179 : ℕ)^2197*100000000000000000000^512 ≤ 8254337385709977^512*100000^2197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11179 100000 8254337385709977 100000000000000000000 2197 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11179/100000 : ℝ)) (X := (8254337385709977/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hpowhi : (467/3125 : ℝ) ^ (2197/512 : ℝ) ≤ (229463904689891/800000000000000000 : ℝ) := by
    have hpowers : (467/3125 : ℝ)^2197 ≤ (229463904689891/800000000000000000 : ℝ)^512 := by
      have hnat : (467 : ℕ)^2197*800000000000000000^512 ≤ 229463904689891^512*3125^2197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        467 3125 229463904689891 800000000000000000 2197 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (467/3125 : ℝ)) (X := (229463904689891/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008254337385709977/50000000000000000000 : ℝ) ≤ (10000384702159121/10000000000000000 : ℝ) ^ (2197/512 : ℝ) := by
    have hpowers : (50008254337385709977/50000000000000000000 : ℝ)^512 ≤ (10000384702159121/10000000000000000 : ℝ)^2197 := by
      have hnat : (50008254337385709977 : ℕ)^512*10000000000000000^2197 ≤ 10000384702159121^2197*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008254337385709977 50000000000000000000 10000384702159121 10000000000000000 512 2197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000384702159121/10000000000000000 : ℝ)) (X := (50008254337385709977/50000000000000000000 : ℝ)) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252308582841996647/6250000000000000000 : ℝ) ≤ (1000086068422493/1000000000000000 : ℝ) ^ (2197/512 : ℝ) := by
    have hpowers : (6252308582841996647/6250000000000000000 : ℝ)^512 ≤ (1000086068422493/1000000000000000 : ℝ)^2197 := by
      have hnat : (6252308582841996647 : ℕ)^512*1000000000000000^2197 ≤ 1000086068422493^2197*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252308582841996647 6250000000000000000 1000086068422493 1000000000000000 512 2197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000086068422493/1000000000000000 : ℝ)) (X := (6252308582841996647/6250000000000000000 : ℝ)) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (400229463904689891/400000000000000000 : ℝ) ≤ (10001336666290739/10000000000000000 : ℝ) ^ (2197/512 : ℝ) := by
    have hpowers : (400229463904689891/400000000000000000 : ℝ)^512 ≤ (10001336666290739/10000000000000000 : ℝ)^2197 := by
      have hnat : (400229463904689891 : ℕ)^512*10000000000000000^2197 ≤ 10001336666290739^2197*400000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400229463904689891 400000000000000000 10001336666290739 10000000000000000 512 2197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001336666290739/10000000000000000 : ℝ)) (X := (400229463904689891/400000000000000000 : ℝ)) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8254337385709977/100000000000000000000 : ℝ) ≤ ((12546935465533910981/12550000000000000000 : ℝ)+2*(158660688603/125500000000000 : ℝ)*(11179/100000 : ℝ))^(2197/512 : ℝ) := by
    rw [show (12546935465533910981/12550000000000000000 : ℝ)+2*(158660688603/125500000000000 : ℝ)*(11179/100000 : ℝ)=(10000384702159121/10000000000000000 : ℝ) by norm_num, show 1+2*(8254337385709977/100000000000000000000 : ℝ)=(50008254337385709977/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(229463904689891/800000000000000000 : ℝ)+(8254337385709977/100000000000000000000 : ℝ) ≤ ((12546935465533910981/12550000000000000000 : ℝ)+(158660688603/125500000000000 : ℝ)*((467/3125 : ℝ)+(11179/100000 : ℝ)))^(2197/512 : ℝ) := by
    rw [show (12546935465533910981/12550000000000000000 : ℝ)+(158660688603/125500000000000 : ℝ)*((467/3125 : ℝ)+(11179/100000 : ℝ))=(1000086068422493/1000000000000000 : ℝ) by norm_num, show 1+(229463904689891/800000000000000000 : ℝ)+(8254337385709977/100000000000000000000 : ℝ)=(6252308582841996647/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(229463904689891/800000000000000000 : ℝ) ≤ ((12546935465533910981/12550000000000000000 : ℝ)+2*(158660688603/125500000000000 : ℝ)*(467/3125 : ℝ))^(2197/512 : ℝ) := by
    rw [show (12546935465533910981/12550000000000000000 : ℝ)+2*(158660688603/125500000000000 : ℝ)*(467/3125 : ℝ)=(10001336666290739/10000000000000000 : ℝ) by norm_num, show 1+2*(229463904689891/800000000000000000 : ℝ)=(400229463904689891/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12546935465533910981/12550000000000000000 : ℝ)*(X 1 0+X 2 0)+(158660688603/125500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2197/512 : ℝ)) (lo := (11179/100000 : ℝ)) (hi := (467/3125 : ℝ)) (c := (12546935465533910981/12550000000000000000 : ℝ)) (alpha := (158660688603/125500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12546935465533910981/12550000000000000000 : ℝ)*(X 0 1+X 2 1)+(158660688603/125500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2197/512 : ℝ)) (lo := (11179/100000 : ℝ)) (hi := (467/3125 : ℝ)) (c := (12546935465533910981/12550000000000000000 : ℝ)) (alpha := (158660688603/125500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12546935465533910981/12550000000000000000 : ℝ)*(X 0 2+X 1 2)+(158660688603/125500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2197/512 : ℝ)) (lo := (11179/100000 : ℝ)) (hi := (467/3125 : ℝ)) (c := (12546935465533910981/12550000000000000000 : ℝ)) (alpha := (158660688603/125500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1966122777/10000000000 : ℝ)*X 0 0+(5409229509/10000000000 : ℝ)*X 0 1+(1049163613/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334221363/625000000 : ℝ)*X 1 0+(-6404179/31250000 : ℝ)*X 1 1+(1049163667/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673770923/5000000000 : ℝ)*X 2 0+(2622909169/5000000000 : ℝ)*X 2 1+(-81973489/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1075696289/2500000000 : ℝ)*X 0 0+(165156457/400000000 : ℝ)*X 0 1+(1120800449/2500000000 : ℝ)*X 0 2+(1075696289/2500000000 : ℝ)*X 1 0+(165156457/400000000 : ℝ)*X 1 1+(1120800449/2500000000 : ℝ)*X 1 2+(1075696289/2500000000 : ℝ)*X 2 0+(165156457/400000000 : ℝ)*X 2 1+(1120800449/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1966134621/10000000000 : ℝ)*X 0 0+(5246417133/10000000000 : ℝ)*X 0 1+(1352156817/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652517401/5000000000 : ℝ)*X 1 0+(-117908009/625000000 : ℝ)*X 1 1+(1081725453/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663129347/1250000000 : ℝ)*X 2 0+(216345091/400000000 : ℝ)*X 2 1+(-1886528167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4302810843/10000000000 : ℝ)*X 0 0+(5602379/12500000 : ℝ)*X 0 1+(1032554193/2500000000 : ℝ)*X 0 2+(4302810843/10000000000 : ℝ)*X 1 0+(5602379/12500000 : ℝ)*X 1 1+(1032554193/2500000000 : ℝ)*X 1 2+(4302810843/10000000000 : ℝ)*X 2 0+(5602379/12500000 : ℝ)*X 2 1+(1032554193/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1498245099027117600965616207/156875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (629937731/50000000000000 : ℝ)*(base19) + (149103937/12500000000000 : ℝ)*(base23) + (5910649/10000000000000 : ℝ)*(lower2) + (43375267/25000000000000 : ℝ)*(upper3) + (169371623/100000000000000 : ℝ)*(upper5) + (1117770702204683/25000000000000 : ℝ)*(major0) + (1117770702204683/25000000000000 : ℝ)*(major1) + (1117770702204683/25000000000000 : ℝ)*(major2) + (764944609796779/12500000000000 : ℝ)*(sp0) + (6119591899963123/100000000000000 : ℝ)*(sp1) + (6119591967007089/100000000000000 : ℝ)*(sp2) + (282255744925409/10000000000000 : ℝ)*(sp3) + (36281464353/100000000000000 : ℝ)*(sp4) + (7345096283/50000000000000 : ℝ)*(sp7) + (22051344839427/781250000000 : ℝ)*(f.failure) + (1223918631967717/20000000000000 : ℝ)*(f.sum) + (52505493662379/6275000000000000000000000000 : ℝ)*base66 + (2791605027598025977/313750000000000000000000000000000 : ℝ)*base68 + (5164176186396775977/313750000000000000000000000000000 : ℝ)*base70 + (3898473008629275977/313750000000000000000000000000000 : ℝ)*base72 + (2157155675677/3137500000000000000000000000 : ℝ)*base74 + (5099977138610525977/313750000000000000000000000000000 : ℝ)*base76 + (5751292230391775977/313750000000000000000000000000000 : ℝ)*base78 + (1807881449216775977/313750000000000000000000000000000 : ℝ)*base80 + (31379707596529/6275000000000000000000000000 : ℝ)*base82 + (587779/39062500000000000000 : ℝ)*base89 + (587779/39062500000000000000 : ℝ)*base91 + (587779/39062500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6308037184237200784594534707/627500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (859584913/50000000000000 : ℝ)*(base19) + (914219367/50000000000000 : ℝ)*(base23) + (10604617/5000000000000 : ℝ)*(upper3) + (2021513/3125000000000 : ℝ)*(lower4) + (48390689/25000000000000 : ℝ)*(upper5) + (4504141316343549/100000000000000 : ℝ)*(major0) + (4504141316343549/100000000000000 : ℝ)*(major1) + (4504141316343549/100000000000000 : ℝ)*(major2) + (17670810637/50000000000000 : ℝ)*(sp1) + (37531250933/100000000000000 : ℝ)*(sp2) + (1232968097650623/20000000000000 : ℝ)*(sp4) + (3082401713731007/50000000000000 : ℝ)*(sp5) + (770600141070431/12500000000000 : ℝ)*(sp6) + (710860452336419/25000000000000 : ℝ)*(sp7) + (710860452336419/25000000000000 : ℝ)*(f.failure) + (1232968097650623/20000000000000 : ℝ)*(f.sum) + (936937954967/392187500000000000000000000 : ℝ)*base65 + (14799151443440688431/1255000000000000000000000000000000 : ℝ)*base68 + (10362268615675688431/1255000000000000000000000000000000 : ℝ)*base70 + (16077592230344311569/1255000000000000000000000000000000 : ℝ)*base71 + (51548942189553/6275000000000000000000000000 : ℝ)*base74 + (4052794619075688431/1255000000000000000000000000000000 : ℝ)*base76 + (11702316671114311569/1255000000000000000000000000000000 : ℝ)*base77 + (3573470438485688431/1255000000000000000000000000000000 : ℝ)*base80 + (12691129562489/3137500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (7673937/1250000000000000000000 : ℝ)*base90 + (7673937/1250000000000000000000 : ℝ)*base92 + (7673937/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1435_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79202277/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (467/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3697/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1435_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1435_s5_0 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-491563037/2500000000 : ℝ)*x 0 + (5408083259/10000000000 : ℝ)*x 1 + (2623439477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (491563037/2500000000 : ℝ)^4395 ≤ (2399384258587/20000000000000 : ℝ)^3371 := by
    have hnat : (491563037 : ℕ)^4395*20000000000000^3371 ≤ 2399384258587^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491563037 2500000000 2399384258587 20000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408083259/10000000000 : ℝ)^4395 ≤ (44869439029413/100000000000000 : ℝ)^3371 := by
    have hnat : (5408083259 : ℕ)^4395*100000000000000^3371 ≤ 44869439029413^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408083259 10000000000 44869439029413 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623439477/5000000000 : ℝ)^4395 ≤ (43133639666629/100000000000000 : ℝ)^3371 := by
    have hnat : (2623439477 : ℕ)^4395*100000000000000^3371 ≤ 43133639666629^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623439477 5000000000 43133639666629 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-491563037/2500000000 : ℝ), (5408083259/10000000000 : ℝ), (2623439477/5000000000 : ℝ)] ![(2399384258587/20000000000000 : ℝ), (44869439029413/100000000000000 : ℝ), (43133639666629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-491563037/2500000000 : ℝ)|^4395 ≤ (2399384258587/20000000000000 : ℝ)^3371
        have hw : |(-491563037/2500000000 : ℝ)|=(491563037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408083259/10000000000 : ℝ)|^4395 ≤ (44869439029413/100000000000000 : ℝ)^3371
        have hw : |(5408083259/10000000000 : ℝ)|=(5408083259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623439477/5000000000 : ℝ)|^4395 ≤ (43133639666629/100000000000000 : ℝ)^3371
        have hw : |(2623439477/5000000000 : ℝ)|=(2623439477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s5_1 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167101419/312500000 : ℝ)*x 0 + (-204832271/1000000000 : ℝ)*x 1 + (2623439477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167101419/312500000 : ℝ)^4395 ≤ (44212482489593/100000000000000 : ℝ)^3371 := by
    have hnat : (167101419 : ℕ)^4395*100000000000000^3371 ≤ 44212482489593^3371*312500000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167101419 312500000 44212482489593 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (204832271/1000000000 : ℝ)^4395 ≤ (790867364241/6250000000000 : ℝ)^3371 := by
    have hnat : (204832271 : ℕ)^4395*6250000000000^3371 ≤ 790867364241^3371*1000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204832271 1000000000 790867364241 6250000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623439477/5000000000 : ℝ)^4395 ≤ (43133639666629/100000000000000 : ℝ)^3371 := by
    have hnat : (2623439477 : ℕ)^4395*100000000000000^3371 ≤ 43133639666629^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623439477 5000000000 43133639666629 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167101419/312500000 : ℝ), (-204832271/1000000000 : ℝ), (2623439477/5000000000 : ℝ)] ![(44212482489593/100000000000000 : ℝ), (790867364241/6250000000000 : ℝ), (43133639666629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167101419/312500000 : ℝ)|^4395 ≤ (44212482489593/100000000000000 : ℝ)^3371
        have hw : |(167101419/312500000 : ℝ)|=(167101419/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-204832271/1000000000 : ℝ)|^4395 ≤ (790867364241/6250000000000 : ℝ)^3371
        have hw : |(-204832271/1000000000 : ℝ)|=(204832271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623439477/5000000000 : ℝ)|^4395 ≤ (43133639666629/100000000000000 : ℝ)^3371
        have hw : |(2623439477/5000000000 : ℝ)|=(2623439477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s5_2 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167101419/312500000 : ℝ)*x 0 + (2623439477/5000000000 : ℝ)*x 1 + (-204832271/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167101419/312500000 : ℝ)^4395 ≤ (44212482489593/100000000000000 : ℝ)^3371 := by
    have hnat : (167101419 : ℕ)^4395*100000000000000^3371 ≤ 44212482489593^3371*312500000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167101419 312500000 44212482489593 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623439477/5000000000 : ℝ)^4395 ≤ (43133639666629/100000000000000 : ℝ)^3371 := by
    have hnat : (2623439477 : ℕ)^4395*100000000000000^3371 ≤ 43133639666629^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623439477 5000000000 43133639666629 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204832271/1000000000 : ℝ)^4395 ≤ (790867364241/6250000000000 : ℝ)^3371 := by
    have hnat : (204832271 : ℕ)^4395*6250000000000^3371 ≤ 790867364241^3371*1000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204832271 1000000000 790867364241 6250000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167101419/312500000 : ℝ), (2623439477/5000000000 : ℝ), (-204832271/1000000000 : ℝ)] ![(44212482489593/100000000000000 : ℝ), (43133639666629/100000000000000 : ℝ), (790867364241/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167101419/312500000 : ℝ)|^4395 ≤ (44212482489593/100000000000000 : ℝ)^3371
        have hw : |(167101419/312500000 : ℝ)|=(167101419/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623439477/5000000000 : ℝ)|^4395 ≤ (43133639666629/100000000000000 : ℝ)^3371
        have hw : |(2623439477/5000000000 : ℝ)|=(2623439477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-204832271/1000000000 : ℝ)|^4395 ≤ (790867364241/6250000000000 : ℝ)^3371
        have hw : |(-204832271/1000000000 : ℝ)|=(204832271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s5_3 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4302863503/10000000000 : ℝ)*x 0 + (2065647171/5000000000 : ℝ)*x 1 + (1120199989/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302863503/10000000000 : ℝ)^4395 ≤ (33304663365103/100000000000000 : ℝ)^3371 := by
    have hnat : (4302863503 : ℕ)^4395*100000000000000^3371 ≤ 33304663365103^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302863503 10000000000 33304663365103 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065647171/5000000000 : ℝ)^4395 ≤ (1973993094989/6250000000000 : ℝ)^3371 := by
    have hnat : (2065647171 : ℕ)^4395*6250000000000^3371 ≤ 1973993094989^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065647171 5000000000 1973993094989 6250000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120199989/2500000000 : ℝ)^4395 ≤ (35111447107703/100000000000000 : ℝ)^3371 := by
    have hnat : (1120199989 : ℕ)^4395*100000000000000^3371 ≤ 35111447107703^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120199989 2500000000 35111447107703 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302863503/10000000000 : ℝ), (2065647171/5000000000 : ℝ), (1120199989/2500000000 : ℝ)] ![(33304663365103/100000000000000 : ℝ), (1973993094989/6250000000000 : ℝ), (35111447107703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302863503/10000000000 : ℝ)|^4395 ≤ (33304663365103/100000000000000 : ℝ)^3371
        have hw : |(4302863503/10000000000 : ℝ)|=(4302863503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2065647171/5000000000 : ℝ)|^4395 ≤ (1973993094989/6250000000000 : ℝ)^3371
        have hw : |(2065647171/5000000000 : ℝ)|=(2065647171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1120199989/2500000000 : ℝ)|^4395 ≤ (35111447107703/100000000000000 : ℝ)^3371
        have hw : |(1120199989/2500000000 : ℝ)|=(1120199989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s5_4 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1966263429/10000000000 : ℝ)*x 0 + (2623730951/5000000000 : ℝ)*x 1 + (5407497329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1966263429/10000000000 : ℝ)^4395 ≤ (5998505515707/50000000000000 : ℝ)^3371 := by
    have hnat : (1966263429 : ℕ)^4395*50000000000000^3371 ≤ 5998505515707^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966263429 10000000000 5998505515707 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623730951/5000000000 : ℝ)^4395 ≤ (43139887829371/100000000000000 : ℝ)^3371 := by
    have hnat : (2623730951 : ℕ)^4395*100000000000000^3371 ≤ 43139887829371^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623730951 5000000000 43139887829371 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407497329/10000000000 : ℝ)^4395 ≤ (11215775280153/25000000000000 : ℝ)^3371 := by
    have hnat : (5407497329 : ℕ)^4395*25000000000000^3371 ≤ 11215775280153^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407497329 10000000000 11215775280153 25000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1966263429/10000000000 : ℝ), (2623730951/5000000000 : ℝ), (5407497329/10000000000 : ℝ)] ![(5998505515707/50000000000000 : ℝ), (43139887829371/100000000000000 : ℝ), (11215775280153/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1966263429/10000000000 : ℝ)|^4395 ≤ (5998505515707/50000000000000 : ℝ)^3371
        have hw : |(-1966263429/10000000000 : ℝ)|=(1966263429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623730951/5000000000 : ℝ)|^4395 ≤ (43139887829371/100000000000000 : ℝ)^3371
        have hw : |(2623730951/5000000000 : ℝ)|=(2623730951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407497329/10000000000 : ℝ)|^4395 ≤ (11215775280153/25000000000000 : ℝ)^3371
        have hw : |(5407497329/10000000000 : ℝ)|=(5407497329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s5_5 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652656091/5000000000 : ℝ)*x 0 + (-1887704283/10000000000 : ℝ)*x 1 + (5407497293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652656091/5000000000 : ℝ)^4395 ≤ (43760985712371/100000000000000 : ℝ)^3371 := by
    have hnat : (2652656091 : ℕ)^4395*100000000000000^3371 ≤ 43760985712371^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652656091 5000000000 43760985712371 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1887704283/10000000000 : ℝ)^4395 ≤ (11375913544991/100000000000000 : ℝ)^3371 := by
    have hnat : (1887704283 : ℕ)^4395*100000000000000^3371 ≤ 11375913544991^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887704283 10000000000 11375913544991 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407497293/10000000000 : ℝ)^4395 ≤ (11215775182803/25000000000000 : ℝ)^3371 := by
    have hnat : (5407497293 : ℕ)^4395*25000000000000^3371 ≤ 11215775182803^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407497293 10000000000 11215775182803 25000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652656091/5000000000 : ℝ), (-1887704283/10000000000 : ℝ), (5407497293/10000000000 : ℝ)] ![(43760985712371/100000000000000 : ℝ), (11375913544991/100000000000000 : ℝ), (11215775182803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652656091/5000000000 : ℝ)|^4395 ≤ (43760985712371/100000000000000 : ℝ)^3371
        have hw : |(2652656091/5000000000 : ℝ)|=(2652656091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1887704283/10000000000 : ℝ)|^4395 ≤ (11375913544991/100000000000000 : ℝ)^3371
        have hw : |(-1887704283/10000000000 : ℝ)|=(1887704283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407497293/10000000000 : ℝ)|^4395 ≤ (11215775182803/25000000000000 : ℝ)^3371
        have hw : |(5407497293/10000000000 : ℝ)|=(5407497293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s5_6 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652656191/5000000000 : ℝ)*x 0 + (5407497159/10000000000 : ℝ)*x 1 + (-1887704193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652656191/5000000000 : ℝ)^4395 ≤ (21880493931601/50000000000000 : ℝ)^3371 := by
    have hnat : (2652656191 : ℕ)^4395*50000000000000^3371 ≤ 21880493931601^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652656191 5000000000 21880493931601 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407497159/10000000000 : ℝ)^4395 ≤ (2243154964089/5000000000000 : ℝ)^3371 := by
    have hnat : (5407497159 : ℕ)^4395*5000000000000^3371 ≤ 2243154964089^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407497159 10000000000 2243154964089 5000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1887704193/10000000000 : ℝ)^4395 ≤ (2843978209467/25000000000000 : ℝ)^3371 := by
    have hnat : (1887704193 : ℕ)^4395*25000000000000^3371 ≤ 2843978209467^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887704193 10000000000 2843978209467 25000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652656191/5000000000 : ℝ), (5407497159/10000000000 : ℝ), (-1887704193/10000000000 : ℝ)] ![(21880493931601/50000000000000 : ℝ), (2243154964089/5000000000000 : ℝ), (2843978209467/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652656191/5000000000 : ℝ)|^4395 ≤ (21880493931601/50000000000000 : ℝ)^3371
        have hw : |(2652656191/5000000000 : ℝ)|=(2652656191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407497159/10000000000 : ℝ)|^4395 ≤ (2243154964089/5000000000000 : ℝ)^3371
        have hw : |(5407497159/10000000000 : ℝ)|=(5407497159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1887704193/10000000000 : ℝ)|^4395 ≤ (2843978209467/25000000000000 : ℝ)^3371
        have hw : |(-1887704193/10000000000 : ℝ)|=(1887704193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s5_7 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2151444079/5000000000 : ℝ)*x 0 + (4479536051/10000000000 : ℝ)*x 1 + (4132564737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151444079/5000000000 : ℝ)^4395 ≤ (166524560833/500000000000 : ℝ)^3371 := by
    have hnat : (2151444079 : ℕ)^4395*500000000000^3371 ≤ 166524560833^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151444079 5000000000 166524560833 500000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4479536051/10000000000 : ℝ)^4395 ≤ (7019707047659/20000000000000 : ℝ)^3371 := by
    have hnat : (4479536051 : ℕ)^4395*20000000000000^3371 ≤ 7019707047659^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479536051 10000000000 7019707047659 20000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4132564737/10000000000 : ℝ)^4395 ≤ (15798276289817/50000000000000 : ℝ)^3371 := by
    have hnat : (4132564737 : ℕ)^4395*50000000000000^3371 ≤ 15798276289817^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132564737 10000000000 15798276289817 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151444079/5000000000 : ℝ), (4479536051/10000000000 : ℝ), (4132564737/10000000000 : ℝ)] ![(166524560833/500000000000 : ℝ), (7019707047659/20000000000000 : ℝ), (15798276289817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151444079/5000000000 : ℝ)|^4395 ≤ (166524560833/500000000000 : ℝ)^3371
        have hw : |(2151444079/5000000000 : ℝ)|=(2151444079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4479536051/10000000000 : ℝ)|^4395 ≤ (7019707047659/20000000000000 : ℝ)^3371
        have hw : |(4479536051/10000000000 : ℝ)|=(4479536051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4132564737/10000000000 : ℝ)|^4395 ≤ (15798276289817/50000000000000 : ℝ)^3371
        have hw : |(4132564737/10000000000 : ℝ)|=(4132564737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1435_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79202277/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3697/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11349/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3691/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3697/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5663/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3697/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5663/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3697/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5663/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3697/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5663/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3697/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5663/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3697/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5663/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5663/50000 : ℝ) ^ (2197/512 : ℝ) ≤ (4365135522594859/50000000000000000000 : ℝ) := by
    have hpowers : (5663/50000 : ℝ)^2197 ≤ (4365135522594859/50000000000000000000 : ℝ)^512 := by
      have hnat : (5663 : ℕ)^2197*50000000000000000000^512 ≤ 4365135522594859^512*50000^2197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5663 50000 4365135522594859 50000000000000000000 2197 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5663/50000 : ℝ)) (X := (4365135522594859/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3697/25000 : ℝ) ^ (2197/512 : ℝ) ≤ (3427507849336451/12500000000000000000 : ℝ) := by
    have hpowers : (3697/25000 : ℝ)^2197 ≤ (3427507849336451/12500000000000000000 : ℝ)^512 := by
      have hnat : (3697 : ℕ)^2197*12500000000000000000^512 ≤ 3427507849336451^512*25000^2197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3697 25000 3427507849336451 12500000000000000000 2197 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3697/25000 : ℝ)) (X := (3427507849336451/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004365135522594859/25000000000000000000 : ℝ) ≤ (39064089383077/39062500000000 : ℝ) ^ (2197/512 : ℝ) := by
    have hpowers : (25004365135522594859/25000000000000000000 : ℝ)^512 ≤ (39064089383077/39062500000000 : ℝ)^2197 := by
      have hnat : (25004365135522594859 : ℕ)^512*39062500000000^2197 ≤ 39064089383077^2197*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004365135522594859 25000000000000000000 39064089383077 39062500000000 512 2197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39064089383077/39062500000000 : ℝ)) (X := (25004365135522594859/25000000000000000000 : ℝ)) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018075166919940663/50000000000000000000 : ℝ) ≤ (10000842348912311/10000000000000000 : ℝ) ^ (2197/512 : ℝ) := by
    have hpowers : (50018075166919940663/50000000000000000000 : ℝ)^512 ≤ (10000842348912311/10000000000000000 : ℝ)^2197 := by
      have hnat : (50018075166919940663 : ℕ)^512*10000000000000000^2197 ≤ 10000842348912311^2197*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018075166919940663 50000000000000000000 10000842348912311 10000000000000000 512 2197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000842348912311/10000000000000000 : ℝ)) (X := (50018075166919940663/50000000000000000000 : ℝ)) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253427507849336451/6250000000000000000 : ℝ) ≤ (1000127781575691/1000000000000000 : ℝ) ^ (2197/512 : ℝ) := by
    have hpowers : (6253427507849336451/6250000000000000000 : ℝ)^512 ≤ (1000127781575691/1000000000000000 : ℝ)^2197 := by
      have hnat : (6253427507849336451 : ℕ)^512*1000000000000000^2197 ≤ 1000127781575691^2197*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253427507849336451 6250000000000000000 1000127781575691 1000000000000000 512 2197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000127781575691/1000000000000000 : ℝ)) (X := (6253427507849336451/6250000000000000000 : ℝ)) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4365135522594859/50000000000000000000 : ℝ) ≤ ((8652886107688640599/8655000000000000000 : ℝ)+2*(435466844599/346200000000000 : ℝ)*(5663/50000 : ℝ))^(2197/512 : ℝ) := by
    rw [show (8652886107688640599/8655000000000000000 : ℝ)+2*(435466844599/346200000000000 : ℝ)*(5663/50000 : ℝ)=(39064089383077/39062500000000 : ℝ) by norm_num, show 1+2*(4365135522594859/50000000000000000000 : ℝ)=(25004365135522594859/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3427507849336451/12500000000000000000 : ℝ)+(4365135522594859/50000000000000000000 : ℝ) ≤ ((8652886107688640599/8655000000000000000 : ℝ)+(435466844599/346200000000000 : ℝ)*((3697/25000 : ℝ)+(5663/50000 : ℝ)))^(2197/512 : ℝ) := by
    rw [show (8652886107688640599/8655000000000000000 : ℝ)+(435466844599/346200000000000 : ℝ)*((3697/25000 : ℝ)+(5663/50000 : ℝ))=(10000842348912311/10000000000000000 : ℝ) by norm_num, show 1+(3427507849336451/12500000000000000000 : ℝ)+(4365135522594859/50000000000000000000 : ℝ)=(50018075166919940663/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3427507849336451/12500000000000000000 : ℝ) ≤ ((8652886107688640599/8655000000000000000 : ℝ)+2*(435466844599/346200000000000 : ℝ)*(3697/25000 : ℝ))^(2197/512 : ℝ) := by
    rw [show (8652886107688640599/8655000000000000000 : ℝ)+2*(435466844599/346200000000000 : ℝ)*(3697/25000 : ℝ)=(1000127781575691/1000000000000000 : ℝ) by norm_num, show 1+2*(3427507849336451/12500000000000000000 : ℝ)=(6253427507849336451/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8652886107688640599/8655000000000000000 : ℝ)*(X 1 0+X 2 0)+(435466844599/346200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2197/512 : ℝ)) (lo := (5663/50000 : ℝ)) (hi := (3697/25000 : ℝ)) (c := (8652886107688640599/8655000000000000000 : ℝ)) (alpha := (435466844599/346200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8652886107688640599/8655000000000000000 : ℝ)*(X 0 1+X 2 1)+(435466844599/346200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2197/512 : ℝ)) (lo := (5663/50000 : ℝ)) (hi := (3697/25000 : ℝ)) (c := (8652886107688640599/8655000000000000000 : ℝ)) (alpha := (435466844599/346200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8652886107688640599/8655000000000000000 : ℝ)*(X 0 2+X 1 2)+(435466844599/346200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2197/512 : ℝ)) (lo := (5663/50000 : ℝ)) (hi := (3697/25000 : ℝ)) (c := (8652886107688640599/8655000000000000000 : ℝ)) (alpha := (435466844599/346200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-491563037/2500000000 : ℝ)*X 0 0+(5408083259/10000000000 : ℝ)*X 0 1+(2623439477/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167101419/312500000 : ℝ)*X 1 0+(-204832271/1000000000 : ℝ)*X 1 1+(2623439477/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167101419/312500000 : ℝ)*X 2 0+(2623439477/5000000000 : ℝ)*X 2 1+(-204832271/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4302863503/10000000000 : ℝ)*X 0 0+(2065647171/5000000000 : ℝ)*X 0 1+(1120199989/2500000000 : ℝ)*X 0 2+(4302863503/10000000000 : ℝ)*X 1 0+(2065647171/5000000000 : ℝ)*X 1 1+(1120199989/2500000000 : ℝ)*X 1 2+(4302863503/10000000000 : ℝ)*X 2 0+(2065647171/5000000000 : ℝ)*X 2 1+(1120199989/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1966263429/10000000000 : ℝ)*X 0 0+(2623730951/5000000000 : ℝ)*X 0 1+(5407497329/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652656091/5000000000 : ℝ)*X 1 0+(-1887704283/10000000000 : ℝ)*X 1 1+(5407497293/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652656191/5000000000 : ℝ)*X 2 0+(5407497159/10000000000 : ℝ)*X 2 1+(-1887704193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2151444079/5000000000 : ℝ)*X 0 0+(4479536051/10000000000 : ℝ)*X 0 1+(4132564737/10000000000 : ℝ)*X 0 2+(2151444079/5000000000 : ℝ)*X 1 0+(4479536051/10000000000 : ℝ)*X 1 1+(4132564737/10000000000 : ℝ)*X 1 2+(2151444079/5000000000 : ℝ)*X 2 0+(4479536051/10000000000 : ℝ)*X 2 1+(4132564737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (724168505257528152329450491/144250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (182658769/20000000000000 : ℝ)*(base19) + (850807763/100000000000000 : ℝ)*(base23) + (33412841/100000000000000 : ℝ)*(lower2) + (3130541/2500000000000 : ℝ)*(upper3) + (39893821/50000000000000 : ℝ)*(upper5) + (4532275151818303/100000000000000 : ℝ)*(major0) + (4532275151818303/100000000000000 : ℝ)*(major1) + (4532275151818303/100000000000000 : ℝ)*(major2) + (3101664173625673/50000000000000 : ℝ)*(sp0) + (6203346664508123/100000000000000 : ℝ)*(sp1) + (1240669345398841/20000000000000 : ℝ)*(sp2) + (1430596481289577/50000000000000 : ℝ)*(sp3) + (19230550623/100000000000000 : ℝ)*(sp4) + (11994893/125000000000 : ℝ)*(sp7) + (1430601279246777/50000000000000 : ℝ)*(f.failure) + (6203347577801969/100000000000000 : ℝ)*(f.sum) + (56761030881473/17310000000000000000000000000 : ℝ)*base66 + (8529658489029491503/865500000000000000000000000000000 : ℝ)*base68 + (7554521663407991503/865500000000000000000000000000000 : ℝ)*base70 + (2334996486708491503/865500000000000000000000000000000 : ℝ)*base72 + (48219819049283/17310000000000000000000000000 : ℝ)*base74 + (6847741632768491503/865500000000000000000000000000000 : ℝ)*base76 + (6695741601876491503/865500000000000000000000000000000 : ℝ)*base78 + (5285574087684491503/865500000000000000000000000000000 : ℝ)*base80 + (3306395150557/17310000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (8311229/2500000000000000000000 : ℝ)*base89 + (8311229/2500000000000000000000 : ℝ)*base91 + (8311229/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (652420778833100071914230877/72125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1741676343/100000000000000 : ℝ)*(base19) + (2265207809/100000000000000 : ℝ)*(base23) + (41133909/25000000000000 : ℝ)*(upper3) + (58253831/50000000000000 : ℝ)*(lower4) + (188841299/100000000000000 : ℝ)*(upper5) + (2282674887892923/50000000000000 : ℝ)*(major0) + (2282674887892923/50000000000000 : ℝ)*(major1) + (2282674887892923/50000000000000 : ℝ)*(major2) + (38154713701/100000000000000 : ℝ)*(sp1) + (46804362777/100000000000000 : ℝ)*(sp2) + (3124308423713259/50000000000000 : ℝ)*(sp4) + (6248576951036473/100000000000000 : ℝ)*(sp5) + (1562141944463983/25000000000000 : ℝ)*(sp6) + (2882082402621989/100000000000000 : ℝ)*(sp7) + (2882082402621989/100000000000000 : ℝ)*(f.failure) + (3124308423713259/50000000000000 : ℝ)*(f.sum) + (1511660215559/2885000000000000000000000000 : ℝ)*base65 + (343182223147248041/144250000000000000000000000000000 : ℝ)*base68 + (577938948717248041/144250000000000000000000000000000 : ℝ)*base70 + (1749147772618501959/144250000000000000000000000000000 : ℝ)*base71 + (5946580796009/2885000000000000000000000000 : ℝ)*base73 + (1783197597821498041/144250000000000000000000000000000 : ℝ)*base76 + (858984059658001959/144250000000000000000000000000000 : ℝ)*base77 + (1132817572189748041/144250000000000000000000000000000 : ℝ)*base80 + (6154911269/11269531250000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (931047/5000000000000000000000 : ℝ)*base90 + (931047/5000000000000000000000 : ℝ)*base92 + (931047/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1435_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79202277/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3697/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1435_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1435_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79202277/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1435_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1435_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1435_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79202277/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1435_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

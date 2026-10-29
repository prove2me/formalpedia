-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1390_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:25:40.614825+00:00
-- url     : https://prove2.me/submissions/29cd5e3a-86d0-4591-81bd-29ebc105a60d

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
theorem support_rectangle_w1390_s6_0 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-250402059/1250000000 : ℝ)*x 0 + (5410234479/10000000000 : ℝ)*x 1 + (2622981781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (250402059/1250000000 : ℝ)^2175 ≤ (12210845251881/100000000000000 : ℝ)^1663 := by
    have hnat : (250402059 : ℕ)^2175*100000000000000^1663 ≤ 12210845251881^1663*1250000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250402059 1250000000 12210845251881 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410234479/10000000000 : ℝ)^2175 ≤ (44779513318179/100000000000000 : ℝ)^1663 := by
    have hnat : (5410234479 : ℕ)^2175*100000000000000^1663 ≤ 44779513318179^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410234479 10000000000 44779513318179 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622981781/5000000000 : ℝ)^2175 ≤ (8601928283783/20000000000000 : ℝ)^1663 := by
    have hnat : (2622981781 : ℕ)^2175*20000000000000^1663 ≤ 8601928283783^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622981781 5000000000 8601928283783 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-250402059/1250000000 : ℝ), (5410234479/10000000000 : ℝ), (2622981781/5000000000 : ℝ)] ![(12210845251881/100000000000000 : ℝ), (44779513318179/100000000000000 : ℝ), (8601928283783/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-250402059/1250000000 : ℝ)|^2175 ≤ (12210845251881/100000000000000 : ℝ)^1663
        have hw : |(-250402059/1250000000 : ℝ)|=(250402059/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410234479/10000000000 : ℝ)|^2175 ≤ (44779513318179/100000000000000 : ℝ)^1663
        have hw : |(5410234479/10000000000 : ℝ)|=(5410234479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622981781/5000000000 : ℝ)|^2175 ≤ (8601928283783/20000000000000 : ℝ)^1663
        have hw : |(2622981781/5000000000 : ℝ)|=(2622981781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s6_1 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337029583/2500000000 : ℝ)*x 0 + (-2086877399/10000000000 : ℝ)*x 1 + (5245963577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337029583/2500000000 : ℝ)^2175 ≤ (4410829391493/10000000000000 : ℝ)^1663 := by
    have hnat : (1337029583 : ℕ)^2175*10000000000000^1663 ≤ 4410829391493^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337029583 2500000000 4410829391493 10000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2086877399/10000000000 : ℝ)^2175 ≤ (2576412898409/20000000000000 : ℝ)^1663 := by
    have hnat : (2086877399 : ℕ)^2175*20000000000000^1663 ≤ 2576412898409^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086877399 10000000000 2576412898409 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245963577/10000000000 : ℝ)^2175 ≤ (43009641579757/100000000000000 : ℝ)^1663 := by
    have hnat : (5245963577 : ℕ)^2175*100000000000000^1663 ≤ 43009641579757^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245963577 10000000000 43009641579757 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337029583/2500000000 : ℝ), (-2086877399/10000000000 : ℝ), (5245963577/10000000000 : ℝ)] ![(4410829391493/10000000000000 : ℝ), (2576412898409/20000000000000 : ℝ), (43009641579757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337029583/2500000000 : ℝ)|^2175 ≤ (4410829391493/10000000000000 : ℝ)^1663
        have hw : |(1337029583/2500000000 : ℝ)|=(1337029583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2086877399/10000000000 : ℝ)|^2175 ≤ (2576412898409/20000000000000 : ℝ)^1663
        have hw : |(-2086877399/10000000000 : ℝ)|=(2086877399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245963577/10000000000 : ℝ)|^2175 ≤ (43009641579757/100000000000000 : ℝ)^1663
        have hw : |(5245963577/10000000000 : ℝ)|=(5245963577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s6_2 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668514797/1250000000 : ℝ)*x 0 + (5245963547/10000000000 : ℝ)*x 1 + (-104343869/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668514797/1250000000 : ℝ)^2175 ≤ (22054147194771/50000000000000 : ℝ)^1663 := by
    have hnat : (668514797 : ℕ)^2175*50000000000000^1663 ≤ 22054147194771^1663*1250000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668514797 1250000000 22054147194771 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245963547/10000000000 : ℝ)^2175 ≤ (21504820629037/50000000000000 : ℝ)^1663 := by
    have hnat : (5245963547 : ℕ)^2175*50000000000000^1663 ≤ 21504820629037^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245963547 10000000000 21504820629037 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104343869/500000000 : ℝ)^2175 ≤ (257641286773/2000000000000 : ℝ)^1663 := by
    have hnat : (104343869 : ℕ)^2175*2000000000000^1663 ≤ 257641286773^1663*500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104343869 500000000 257641286773 2000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668514797/1250000000 : ℝ), (5245963547/10000000000 : ℝ), (-104343869/500000000 : ℝ)] ![(22054147194771/50000000000000 : ℝ), (21504820629037/50000000000000 : ℝ), (257641286773/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668514797/1250000000 : ℝ)|^2175 ≤ (22054147194771/50000000000000 : ℝ)^1663
        have hw : |(668514797/1250000000 : ℝ)|=(668514797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245963547/10000000000 : ℝ)|^2175 ≤ (21504820629037/50000000000000 : ℝ)^1663
        have hw : |(5245963547/10000000000 : ℝ)|=(5245963547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-104343869/500000000 : ℝ)|^2175 ≤ (257641286773/2000000000000 : ℝ)^1663
        have hw : |(-104343869/500000000 : ℝ)|=(104343869/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s6_3 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4314222581/10000000000 : ℝ)*x 0 + (2071162419/5000000000 : ℝ)*x 1 + (4492626181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314222581/10000000000 : ℝ)^2175 ≤ (6660814123589/20000000000000 : ℝ)^1663 := by
    have hnat : (4314222581 : ℕ)^2175*20000000000000^1663 ≤ 6660814123589^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314222581 10000000000 6660814123589 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071162419/5000000000 : ℝ)^2175 ≤ (986852683333/3125000000000 : ℝ)^1663 := by
    have hnat : (2071162419 : ℕ)^2175*3125000000000^1663 ≤ 986852683333^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071162419 5000000000 986852683333 3125000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4492626181/10000000000 : ℝ)^2175 ≤ (4389580437979/12500000000000 : ℝ)^1663 := by
    have hnat : (4492626181 : ℕ)^2175*12500000000000^1663 ≤ 4389580437979^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492626181 10000000000 4389580437979 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314222581/10000000000 : ℝ), (2071162419/5000000000 : ℝ), (4492626181/10000000000 : ℝ)] ![(6660814123589/20000000000000 : ℝ), (986852683333/3125000000000 : ℝ), (4389580437979/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314222581/10000000000 : ℝ)|^2175 ≤ (6660814123589/20000000000000 : ℝ)^1663
        have hw : |(4314222581/10000000000 : ℝ)|=(4314222581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2071162419/5000000000 : ℝ)|^2175 ≤ (986852683333/3125000000000 : ℝ)^1663
        have hw : |(2071162419/5000000000 : ℝ)|=(2071162419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4492626181/10000000000 : ℝ)|^2175 ≤ (4389580437979/12500000000000 : ℝ)^1663
        have hw : |(4492626181/10000000000 : ℝ)|=(4492626181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s6_4 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2003228061/10000000000 : ℝ)*x 0 + (2623277031/5000000000 : ℝ)*x 1 + (5409641003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2003228061/10000000000 : ℝ)^2175 ≤ (12210937643209/100000000000000 : ℝ)^1663 := by
    have hnat : (2003228061 : ℕ)^2175*100000000000000^1663 ≤ 12210937643209^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003228061 10000000000 12210937643209 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623277031/5000000000 : ℝ)^2175 ≤ (1720638933307/4000000000000 : ℝ)^1663 := by
    have hnat : (2623277031 : ℕ)^2175*4000000000000^1663 ≤ 1720638933307^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623277031 5000000000 1720638933307 4000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409641003/10000000000 : ℝ)^2175 ≤ (8954617802727/20000000000000 : ℝ)^1663 := by
    have hnat : (5409641003 : ℕ)^2175*20000000000000^1663 ≤ 8954617802727^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409641003 10000000000 8954617802727 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2003228061/10000000000 : ℝ), (2623277031/5000000000 : ℝ), (5409641003/10000000000 : ℝ)] ![(12210937643209/100000000000000 : ℝ), (1720638933307/4000000000000 : ℝ), (8954617802727/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2003228061/10000000000 : ℝ)|^2175 ≤ (12210937643209/100000000000000 : ℝ)^1663
        have hw : |(-2003228061/10000000000 : ℝ)|=(2003228061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623277031/5000000000 : ℝ)|^2175 ≤ (1720638933307/4000000000000 : ℝ)^1663
        have hw : |(2623277031/5000000000 : ℝ)|=(2623277031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409641003/10000000000 : ℝ)|^2175 ≤ (8954617802727/20000000000000 : ℝ)^1663
        have hw : |(5409641003/10000000000 : ℝ)|=(5409641003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s6_5 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305581173/10000000000 : ℝ)*x 0 + (-1923199971/10000000000 : ℝ)*x 1 + (2704820509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305581173/10000000000 : ℝ)^2175 ≤ (21825011814641/50000000000000 : ℝ)^1663 := by
    have hnat : (5305581173 : ℕ)^2175*50000000000000^1663 ≤ 21825011814641^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305581173 10000000000 21825011814641 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1923199971/10000000000 : ℝ)^2175 ≤ (11576887182579/100000000000000 : ℝ)^1663 := by
    have hnat : (1923199971 : ℕ)^2175*100000000000000^1663 ≤ 11576887182579^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923199971 10000000000 11576887182579 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704820509/5000000000 : ℝ)^2175 ≤ (22386544588003/50000000000000 : ℝ)^1663 := by
    have hnat : (2704820509 : ℕ)^2175*50000000000000^1663 ≤ 22386544588003^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704820509 5000000000 22386544588003 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305581173/10000000000 : ℝ), (-1923199971/10000000000 : ℝ), (2704820509/5000000000 : ℝ)] ![(21825011814641/50000000000000 : ℝ), (11576887182579/100000000000000 : ℝ), (22386544588003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305581173/10000000000 : ℝ)|^2175 ≤ (21825011814641/50000000000000 : ℝ)^1663
        have hw : |(5305581173/10000000000 : ℝ)|=(5305581173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1923199971/10000000000 : ℝ)|^2175 ≤ (11576887182579/100000000000000 : ℝ)^1663
        have hw : |(-1923199971/10000000000 : ℝ)|=(1923199971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704820509/5000000000 : ℝ)|^2175 ≤ (22386544588003/50000000000000 : ℝ)^1663
        have hw : |(2704820509/5000000000 : ℝ)|=(2704820509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s6_6 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (41449853/78125000 : ℝ)*x 0 + (2704820483/5000000000 : ℝ)*x 1 + (-480800007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41449853/78125000 : ℝ)^2175 ≤ (10912505936911/25000000000000 : ℝ)^1663 := by
    have hnat : (41449853 : ℕ)^2175*25000000000000^1663 ≤ 10912505936911^1663*78125000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41449853 78125000 10912505936911 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704820483/5000000000 : ℝ)^2175 ≤ (44773088613121/100000000000000 : ℝ)^1663 := by
    have hnat : (2704820483 : ℕ)^2175*100000000000000^1663 ≤ 44773088613121^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704820483 5000000000 44773088613121 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (480800007/2500000000 : ℝ)^2175 ≤ (5788443815667/50000000000000 : ℝ)^1663 := by
    have hnat : (480800007 : ℕ)^2175*50000000000000^1663 ≤ 5788443815667^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480800007 2500000000 5788443815667 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41449853/78125000 : ℝ), (2704820483/5000000000 : ℝ), (-480800007/2500000000 : ℝ)] ![(10912505936911/25000000000000 : ℝ), (44773088613121/100000000000000 : ℝ), (5788443815667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41449853/78125000 : ℝ)|^2175 ≤ (10912505936911/25000000000000 : ℝ)^1663
        have hw : |(41449853/78125000 : ℝ)|=(41449853/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704820483/5000000000 : ℝ)|^2175 ≤ (44773088613121/100000000000000 : ℝ)^1663
        have hw : |(2704820483/5000000000 : ℝ)|=(2704820483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-480800007/2500000000 : ℝ)|^2175 ≤ (5788443815667/50000000000000 : ℝ)^1663
        have hw : |(-480800007/2500000000 : ℝ)|=(480800007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s6_7 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (862849489/2000000000 : ℝ)*x 0 + (2245683503/5000000000 : ℝ)*x 1 + (1035897647/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862849489/2000000000 : ℝ)^2175 ≤ (33304321652303/100000000000000 : ℝ)^1663 := by
    have hnat : (862849489 : ℕ)^2175*100000000000000^1663 ≤ 33304321652303^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862849489 2000000000 33304321652303 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245683503/5000000000 : ℝ)^2175 ≤ (7020754294547/20000000000000 : ℝ)^1663 := by
    have hnat : (2245683503 : ℕ)^2175*20000000000000^1663 ≤ 7020754294547^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245683503 5000000000 7020754294547 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035897647/2500000000 : ℝ)^2175 ≤ (3948988357459/12500000000000 : ℝ)^1663 := by
    have hnat : (1035897647 : ℕ)^2175*12500000000000^1663 ≤ 3948988357459^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035897647 2500000000 3948988357459 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862849489/2000000000 : ℝ), (2245683503/5000000000 : ℝ), (1035897647/2500000000 : ℝ)] ![(33304321652303/100000000000000 : ℝ), (7020754294547/20000000000000 : ℝ), (3948988357459/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862849489/2000000000 : ℝ)|^2175 ≤ (33304321652303/100000000000000 : ℝ)^1663
        have hw : |(862849489/2000000000 : ℝ)|=(862849489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245683503/5000000000 : ℝ)|^2175 ≤ (7020754294547/20000000000000 : ℝ)^1663
        have hw : |(2245683503/5000000000 : ℝ)|=(2245683503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035897647/2500000000 : ℝ)|^2175 ≤ (3948988357459/12500000000000 : ℝ)^1663
        have hw : |(1035897647/2500000000 : ℝ)|=(1035897647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1390_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11257/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (921/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14741/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14741/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14741/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14741/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14741/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14741/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11253/100000 : ℝ) ^ (4349/1024 : ℝ) ≤ (934694834362293/10000000000000000000 : ℝ) := by
    have hpowers : (11253/100000 : ℝ)^4349 ≤ (934694834362293/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11253 : ℕ)^4349*10000000000000000000^1024 ≤ 934694834362293^1024*100000^4349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11253 100000 934694834362293 10000000000000000000 4349 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11253/100000 : ℝ)) (X := (934694834362293/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14741/100000 : ℝ) ^ (4349/1024 : ℝ) ≤ (29422222642452307/100000000000000000000 : ℝ) := by
    have hpowers : (14741/100000 : ℝ)^4349 ≤ (29422222642452307/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14741 : ℕ)^4349*100000000000000000000^1024 ≤ 29422222642452307^1024*100000^4349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14741 100000 29422222642452307 100000000000000000000 4349 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14741/100000 : ℝ)) (X := (29422222642452307/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000934694834362293/5000000000000000000 : ℝ) ≤ (1000044012836061/1000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (5000934694834362293/5000000000000000000 : ℝ)^1024 ≤ (1000044012836061/1000000000000000 : ℝ)^4349 := by
      have hnat : (5000934694834362293 : ℕ)^1024*1000000000000000^4349 ≤ 1000044012836061^4349*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000934694834362293 5000000000000000000 1000044012836061 1000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000044012836061/1000000000000000 : ℝ)) (X := (5000934694834362293/5000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038769170986075237/100000000000000000000 : ℝ) ≤ (10000912709790819/10000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (100038769170986075237/100000000000000000000 : ℝ)^1024 ≤ (10000912709790819/10000000000000000 : ℝ)^4349 := by
      have hnat : (100038769170986075237 : ℕ)^1024*10000000000000000^4349 ≤ 10000912709790819^4349*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038769170986075237 100000000000000000000 10000912709790819 10000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000912709790819/10000000000000000 : ℝ)) (X := (100038769170986075237/100000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029422222642452307/50000000000000000000 : ℝ) ≤ (2500346322805257/2500000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (50029422222642452307/50000000000000000000 : ℝ)^1024 ≤ (2500346322805257/2500000000000000 : ℝ)^4349 := by
      have hnat : (50029422222642452307 : ℕ)^1024*2500000000000000^4349 ≤ 2500346322805257^4349*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029422222642452307 50000000000000000000 2500346322805257 2500000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500346322805257/2500000000000000 : ℝ)) (X := (50029422222642452307/50000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(934694834362293/10000000000000000000 : ℝ) ≤ ((17435449625026761963/17440000000000000000 : ℝ)+2*(472581430209/348800000000000 : ℝ)*(11253/100000 : ℝ))^(4349/1024 : ℝ) := by
    rw [show (17435449625026761963/17440000000000000000 : ℝ)+2*(472581430209/348800000000000 : ℝ)*(11253/100000 : ℝ)=(1000044012836061/1000000000000000 : ℝ) by norm_num, show 1+2*(934694834362293/10000000000000000000 : ℝ)=(5000934694834362293/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29422222642452307/100000000000000000000 : ℝ)+(934694834362293/10000000000000000000 : ℝ) ≤ ((17435449625026761963/17440000000000000000 : ℝ)+(472581430209/348800000000000 : ℝ)*((14741/100000 : ℝ)+(11253/100000 : ℝ)))^(4349/1024 : ℝ) := by
    rw [show (17435449625026761963/17440000000000000000 : ℝ)+(472581430209/348800000000000 : ℝ)*((14741/100000 : ℝ)+(11253/100000 : ℝ))=(10000912709790819/10000000000000000 : ℝ) by norm_num, show 1+(29422222642452307/100000000000000000000 : ℝ)+(934694834362293/10000000000000000000 : ℝ)=(100038769170986075237/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29422222642452307/100000000000000000000 : ℝ) ≤ ((17435449625026761963/17440000000000000000 : ℝ)+2*(472581430209/348800000000000 : ℝ)*(14741/100000 : ℝ))^(4349/1024 : ℝ) := by
    rw [show (17435449625026761963/17440000000000000000 : ℝ)+2*(472581430209/348800000000000 : ℝ)*(14741/100000 : ℝ)=(2500346322805257/2500000000000000 : ℝ) by norm_num, show 1+2*(29422222642452307/100000000000000000000 : ℝ)=(50029422222642452307/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17435449625026761963/17440000000000000000 : ℝ)*(X 1 0+X 2 0)+(472581430209/348800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (14741/100000 : ℝ)) (c := (17435449625026761963/17440000000000000000 : ℝ)) (alpha := (472581430209/348800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17435449625026761963/17440000000000000000 : ℝ)*(X 0 1+X 2 1)+(472581430209/348800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (14741/100000 : ℝ)) (c := (17435449625026761963/17440000000000000000 : ℝ)) (alpha := (472581430209/348800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17435449625026761963/17440000000000000000 : ℝ)*(X 0 2+X 1 2)+(472581430209/348800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (14741/100000 : ℝ)) (c := (17435449625026761963/17440000000000000000 : ℝ)) (alpha := (472581430209/348800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-250402059/1250000000 : ℝ)*X 0 0+(5410234479/10000000000 : ℝ)*X 0 1+(2622981781/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337029583/2500000000 : ℝ)*X 1 0+(-2086877399/10000000000 : ℝ)*X 1 1+(5245963577/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668514797/1250000000 : ℝ)*X 2 0+(5245963547/10000000000 : ℝ)*X 2 1+(-104343869/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4314222581/10000000000 : ℝ)*X 0 0+(2071162419/5000000000 : ℝ)*X 0 1+(4492626181/10000000000 : ℝ)*X 0 2+(4314222581/10000000000 : ℝ)*X 1 0+(2071162419/5000000000 : ℝ)*X 1 1+(4492626181/10000000000 : ℝ)*X 1 2+(4314222581/10000000000 : ℝ)*X 2 0+(2071162419/5000000000 : ℝ)*X 2 1+(4492626181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2003228061/10000000000 : ℝ)*X 0 0+(2623277031/5000000000 : ℝ)*X 0 1+(5409641003/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305581173/10000000000 : ℝ)*X 1 0+(-1923199971/10000000000 : ℝ)*X 1 1+(2704820509/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41449853/78125000 : ℝ)*X 2 0+(2704820483/5000000000 : ℝ)*X 2 1+(-480800007/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((862849489/2000000000 : ℝ)*X 0 0+(2245683503/5000000000 : ℝ)*X 0 1+(1035897647/2500000000 : ℝ)*X 0 2+(862849489/2000000000 : ℝ)*X 1 0+(2245683503/5000000000 : ℝ)*X 1 1+(1035897647/2500000000 : ℝ)*X 1 2+(862849489/2000000000 : ℝ)*X 2 0+(2245683503/5000000000 : ℝ)*X 2 1+(1035897647/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10000111690753099131991240179/872000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8343923/400000000000 : ℝ)*(base19) + (987883321/50000000000000 : ℝ)*(base23) + (21432303/25000000000000 : ℝ)*(lower2) + (69523613/25000000000000 : ℝ)*(upper3) + (96561527/50000000000000 : ℝ)*(upper5) + (4471160380080463/100000000000000 : ℝ)*(major0) + (4471160380080463/100000000000000 : ℝ)*(major1) + (4471160380080463/100000000000000 : ℝ)*(major2) + (6087549534094271/100000000000000 : ℝ)*(sp0) + (6087591603238413/100000000000000 : ℝ)*(sp1) + (6087591713452521/100000000000000 : ℝ)*(sp2) + (713676182695829/25000000000000 : ℝ)*(sp3) + (11038781223/25000000000000 : ℝ)*(sp4) + (2744736397/12500000000000 : ℝ)*(sp7) + (713681672168623/25000000000000 : ℝ)*(f.failure) + (6087593689219163/100000000000000 : ℝ)*(f.sum) + (39614837702287/17440000000000000000000000000 : ℝ)*base65 + (12665788627738178869/1744000000000000000000000000000000 : ℝ)*base67 + (5708057577098178869/1744000000000000000000000000000000 : ℝ)*base69 + (22459101939818178869/1744000000000000000000000000000000 : ℝ)*base71 + (13103657403887/17440000000000000000000000000 : ℝ)*base73 + (7177929861786178869/1744000000000000000000000000000000 : ℝ)*base75 + (10544549507498178869/1744000000000000000000000000000000 : ℝ)*base77 + (6665084223482178869/1744000000000000000000000000000000 : ℝ)*base79 + (3805370949007/17440000000000000000000000000 : ℝ)*base81 + (11752249/2500000000000000000000 : ℝ)*base89 + (11752249/2500000000000000000000 : ℝ)*base91 + (11752249/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2785264461677649893335091169/436000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (150058019/20000000000000 : ℝ)*(base19) + (59035393/6250000000000 : ℝ)*(base23) + (3333957/5000000000000 : ℝ)*(upper3) + (11908041/12500000000000 : ℝ)*(lower4) + (114518387/100000000000000 : ℝ)*(upper5) + (2251776965362507/50000000000000 : ℝ)*(major0) + (2251776965362507/50000000000000 : ℝ)*(major1) + (2251776965362507/50000000000000 : ℝ)*(major2) + (701204747/4000000000000 : ℝ)*(sp1) + (4445154791/25000000000000 : ℝ)*(sp2) + (6131698469003603/100000000000000 : ℝ)*(sp4) + (6131680188594833/100000000000000 : ℝ)*(sp5) + (6131679743818151/100000000000000 : ℝ)*(sp6) + (179713073719107/6250000000000 : ℝ)*(sp7) + (179713073719107/6250000000000 : ℝ)*(f.failure) + (6131698469003603/100000000000000 : ℝ)*(f.sum) + (50212763836923/8720000000000000000000000000 : ℝ)*base65 + (3187308382383928759/872000000000000000000000000000000 : ℝ)*base68 + (11643134942087928759/872000000000000000000000000000000 : ℝ)*base70 + (700548715335928759/872000000000000000000000000000000 : ℝ)*base72 + (3366927772917/8720000000000000000000000000 : ℝ)*base74 + (1679337389607928759/872000000000000000000000000000000 : ℝ)*base76 + (6557336051743928759/872000000000000000000000000000000 : ℝ)*base78 + (10098172762319928759/872000000000000000000000000000000 : ℝ)*base80 + (2456193567797/8720000000000000000000000000 : ℝ)*base82 + (2464741/625000000000000000000 : ℝ)*base89 + (2464741/625000000000000000000 : ℝ)*base91 + (2464741/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1390_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (921/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1390_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1390_s7_0 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-62600699/312500000 : ℝ)*x 0 + (5410198983/10000000000 : ℝ)*x 1 + (5245995013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (62600699/312500000 : ℝ)^2175 ≤ (3052723064179/25000000000000 : ℝ)^1663 := by
    have hnat : (62600699 : ℕ)^2175*25000000000000^1663 ≤ 3052723064179^1663*312500000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62600699 312500000 3052723064179 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410198983/10000000000 : ℝ)^2175 ≤ (22389564536127/50000000000000 : ℝ)^1663 := by
    have hnat : (5410198983 : ℕ)^2175*50000000000000^1663 ≤ 22389564536127^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410198983 10000000000 22389564536127 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245995013/10000000000 : ℝ)^2175 ≤ (43009978661511/100000000000000 : ℝ)^1663 := by
    have hnat : (5245995013 : ℕ)^2175*100000000000000^1663 ≤ 43009978661511^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245995013 10000000000 43009978661511 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-62600699/312500000 : ℝ), (5410198983/10000000000 : ℝ), (5245995013/10000000000 : ℝ)] ![(3052723064179/25000000000000 : ℝ), (22389564536127/50000000000000 : ℝ), (43009978661511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-62600699/312500000 : ℝ)|^2175 ≤ (3052723064179/25000000000000 : ℝ)^1663
        have hw : |(-62600699/312500000 : ℝ)|=(62600699/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410198983/10000000000 : ℝ)|^2175 ≤ (22389564536127/50000000000000 : ℝ)^1663
        have hw : |(5410198983/10000000000 : ℝ)|=(5410198983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245995013/10000000000 : ℝ)|^2175 ≤ (43009978661511/100000000000000 : ℝ)^1663
        have hw : |(5245995013/10000000000 : ℝ)|=(5245995013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s7_1 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (334256813/625000000 : ℝ)*x 0 + (-521712029/2500000000 : ℝ)*x 1 + (1311498751/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334256813/625000000 : ℝ)^2175 ≤ (44108193340307/100000000000000 : ℝ)^1663 := by
    have hnat : (334256813 : ℕ)^2175*100000000000000^1663 ≤ 44108193340307^1663*625000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334256813 625000000 44108193340307 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521712029/2500000000 : ℝ)^2175 ≤ (12881828079687/100000000000000 : ℝ)^1663 := by
    have hnat : (521712029 : ℕ)^2175*100000000000000^1663 ≤ 12881828079687^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521712029 2500000000 12881828079687 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311498751/2500000000 : ℝ)^2175 ≤ (21504989282503/50000000000000 : ℝ)^1663 := by
    have hnat : (1311498751 : ℕ)^2175*50000000000000^1663 ≤ 21504989282503^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311498751 2500000000 21504989282503 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334256813/625000000 : ℝ), (-521712029/2500000000 : ℝ), (1311498751/2500000000 : ℝ)] ![(44108193340307/100000000000000 : ℝ), (12881828079687/100000000000000 : ℝ), (21504989282503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334256813/625000000 : ℝ)|^2175 ≤ (44108193340307/100000000000000 : ℝ)^1663
        have hw : |(334256813/625000000 : ℝ)|=(334256813/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-521712029/2500000000 : ℝ)|^2175 ≤ (12881828079687/100000000000000 : ℝ)^1663
        have hw : |(-521712029/2500000000 : ℝ)|=(521712029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311498751/2500000000 : ℝ)|^2175 ≤ (21504989282503/50000000000000 : ℝ)^1663
        have hw : |(1311498751/2500000000 : ℝ)|=(1311498751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s7_2 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (534810863/1000000000 : ℝ)*x 0 + (81968679/156250000 : ℝ)*x 1 + (-2086848021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534810863/1000000000 : ℝ)^2175 ≤ (44108189262959/100000000000000 : ℝ)^1663 := by
    have hnat : (534810863 : ℕ)^2175*100000000000000^1663 ≤ 44108189262959^1663*1000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534810863 1000000000 44108189262959 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81968679/156250000 : ℝ)^2175 ≤ (43009983411713/100000000000000 : ℝ)^1663 := by
    have hnat : (81968679 : ℕ)^2175*100000000000000^1663 ≤ 43009983411713^1663*156250000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81968679 156250000 43009983411713 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086848021/10000000000 : ℝ)^2175 ≤ (12881827312719/100000000000000 : ℝ)^1663 := by
    have hnat : (2086848021 : ℕ)^2175*100000000000000^1663 ≤ 12881827312719^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086848021 10000000000 12881827312719 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534810863/1000000000 : ℝ), (81968679/156250000 : ℝ), (-2086848021/10000000000 : ℝ)] ![(44108189262959/100000000000000 : ℝ), (43009983411713/100000000000000 : ℝ), (12881827312719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534810863/1000000000 : ℝ)|^2175 ≤ (44108189262959/100000000000000 : ℝ)^1663
        have hw : |(534810863/1000000000 : ℝ)|=(534810863/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81968679/156250000 : ℝ)|^2175 ≤ (43009983411713/100000000000000 : ℝ)^1663
        have hw : |(81968679/156250000 : ℝ)|=(81968679/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2086848021/10000000000 : ℝ)|^2175 ≤ (12881827312719/100000000000000 : ℝ)^1663
        have hw : |(-2086848021/10000000000 : ℝ)|=(2086848021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s7_3 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4314224563/10000000000 : ℝ)*x 0 + (517799607/1250000000 : ℝ)*x 1 + (4492553983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314224563/10000000000 : ℝ)^2175 ≤ (4163011328599/12500000000000 : ℝ)^1663 := by
    have hnat : (4314224563 : ℕ)^2175*12500000000000^1663 ≤ 4163011328599^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314224563 10000000000 4163011328599 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517799607/1250000000 : ℝ)^2175 ≤ (1973750246103/6250000000000 : ℝ)^1663 := by
    have hnat : (517799607 : ℕ)^2175*6250000000000^1663 ≤ 1973750246103^1663*1250000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517799607 1250000000 1973750246103 6250000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4492553983/10000000000 : ℝ)^2175 ≤ (17557952711591/50000000000000 : ℝ)^1663 := by
    have hnat : (4492553983 : ℕ)^2175*50000000000000^1663 ≤ 17557952711591^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492553983 10000000000 17557952711591 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314224563/10000000000 : ℝ), (517799607/1250000000 : ℝ), (4492553983/10000000000 : ℝ)] ![(4163011328599/12500000000000 : ℝ), (1973750246103/6250000000000 : ℝ), (17557952711591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314224563/10000000000 : ℝ)|^2175 ≤ (4163011328599/12500000000000 : ℝ)^1663
        have hw : |(4314224563/10000000000 : ℝ)|=(4314224563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517799607/1250000000 : ℝ)|^2175 ≤ (1973750246103/6250000000000 : ℝ)^1663
        have hw : |(517799607/1250000000 : ℝ)|=(517799607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4492553983/10000000000 : ℝ)|^2175 ≤ (17557952711591/50000000000000 : ℝ)^1663
        have hw : |(4492553983/10000000000 : ℝ)|=(4492553983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s7_4 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2003233933/10000000000 : ℝ)*x 0 + (5246585331/10000000000 : ℝ)*x 1 + (2704802851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2003233933/10000000000 : ℝ)^2175 ≤ (12210984456791/100000000000000 : ℝ)^1663 := by
    have hnat : (2003233933 : ℕ)^2175*100000000000000^1663 ≤ 12210984456791^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003233933 10000000000 12210984456791 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246585331/10000000000 : ℝ)^2175 ≤ (2150815431767/5000000000000 : ℝ)^1663 := by
    have hnat : (5246585331 : ℕ)^2175*5000000000000^1663 ≤ 2150815431767^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246585331 10000000000 2150815431767 5000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704802851/5000000000 : ℝ)^2175 ≤ (44772706891499/100000000000000 : ℝ)^1663 := by
    have hnat : (2704802851 : ℕ)^2175*100000000000000^1663 ≤ 44772706891499^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704802851 5000000000 44772706891499 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2003233933/10000000000 : ℝ), (5246585331/10000000000 : ℝ), (2704802851/5000000000 : ℝ)] ![(12210984456791/100000000000000 : ℝ), (2150815431767/5000000000000 : ℝ), (44772706891499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2003233933/10000000000 : ℝ)|^2175 ≤ (12210984456791/100000000000000 : ℝ)^1663
        have hw : |(-2003233933/10000000000 : ℝ)|=(2003233933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246585331/10000000000 : ℝ)|^2175 ≤ (2150815431767/5000000000000 : ℝ)^1663
        have hw : |(5246585331/10000000000 : ℝ)|=(5246585331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704802851/5000000000 : ℝ)|^2175 ≤ (44772706891499/100000000000000 : ℝ)^1663
        have hw : |(2704802851/5000000000 : ℝ)|=(2704802851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s7_5 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305589039/10000000000 : ℝ)*x 0 + (-48080943/250000000 : ℝ)*x 1 + (338100359/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305589039/10000000000 : ℝ)^2175 ≤ (43650108268681/100000000000000 : ℝ)^1663 := by
    have hnat : (5305589039 : ℕ)^2175*100000000000000^1663 ≤ 43650108268681^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305589039 10000000000 43650108268681 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48080943/250000000 : ℝ)^2175 ≤ (723574023583/6250000000000 : ℝ)^1663 := by
    have hnat : (48080943 : ℕ)^2175*6250000000000^1663 ≤ 723574023583^1663*250000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48080943 250000000 723574023583 6250000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338100359/625000000 : ℝ)^2175 ≤ (8954541469227/20000000000000 : ℝ)^1663 := by
    have hnat : (338100359 : ℕ)^2175*20000000000000^1663 ≤ 8954541469227^1663*625000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338100359 625000000 8954541469227 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305589039/10000000000 : ℝ), (-48080943/250000000 : ℝ), (338100359/625000000 : ℝ)] ![(43650108268681/100000000000000 : ℝ), (723574023583/6250000000000 : ℝ), (8954541469227/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305589039/10000000000 : ℝ)|^2175 ≤ (43650108268681/100000000000000 : ℝ)^1663
        have hw : |(5305589039/10000000000 : ℝ)|=(5305589039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-48080943/250000000 : ℝ)|^2175 ≤ (723574023583/6250000000000 : ℝ)^1663
        have hw : |(-48080943/250000000 : ℝ)|=(48080943/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338100359/625000000 : ℝ)|^2175 ≤ (8954541469227/20000000000000 : ℝ)^1663
        have hw : |(338100359/625000000 : ℝ)|=(338100359/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s7_6 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305589003/10000000000 : ℝ)*x 0 + (5409605749/10000000000 : ℝ)*x 1 + (-961618881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305589003/10000000000 : ℝ)^2175 ≤ (10912526970329/25000000000000 : ℝ)^1663 := by
    have hnat : (5305589003 : ℕ)^2175*25000000000000^1663 ≤ 10912526970329^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305589003 10000000000 10912526970329 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409605749/10000000000 : ℝ)^2175 ≤ (22386353700129/50000000000000 : ℝ)^1663 := by
    have hnat : (5409605749 : ℕ)^2175*50000000000000^1663 ≤ 22386353700129^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409605749 10000000000 22386353700129 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (961618881/5000000000 : ℝ)^2175 ≤ (1447148088499/12500000000000 : ℝ)^1663 := by
    have hnat : (961618881 : ℕ)^2175*12500000000000^1663 ≤ 1447148088499^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961618881 5000000000 1447148088499 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305589003/10000000000 : ℝ), (5409605749/10000000000 : ℝ), (-961618881/5000000000 : ℝ)] ![(10912526970329/25000000000000 : ℝ), (22386353700129/50000000000000 : ℝ), (1447148088499/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305589003/10000000000 : ℝ)|^2175 ≤ (10912526970329/25000000000000 : ℝ)^1663
        have hw : |(5305589003/10000000000 : ℝ)|=(5305589003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409605749/10000000000 : ℝ)|^2175 ≤ (22386353700129/50000000000000 : ℝ)^1663
        have hw : |(5409605749/10000000000 : ℝ)|=(5409605749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-961618881/5000000000 : ℝ)|^2175 ≤ (1447148088499/12500000000000 : ℝ)^1663
        have hw : |(-961618881/5000000000 : ℝ)|=(961618881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s7_7 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1078562471/2500000000 : ℝ)*x 0 + (4491295761/10000000000 : ℝ)*x 1 + (4143661153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078562471/2500000000 : ℝ)^2175 ≤ (33304346277199/100000000000000 : ℝ)^1663 := by
    have hnat : (1078562471 : ℕ)^2175*100000000000000^1663 ≤ 33304346277199^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078562471 2500000000 33304346277199 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491295761/10000000000 : ℝ)^2175 ≤ (17551521598721/50000000000000 : ℝ)^1663 := by
    have hnat : (4491295761 : ℕ)^2175*50000000000000^1663 ≤ 17551521598721^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491295761 10000000000 17551521598721 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4143661153/10000000000 : ℝ)^2175 ≤ (31592610509359/100000000000000 : ℝ)^1663 := by
    have hnat : (4143661153 : ℕ)^2175*100000000000000^1663 ≤ 31592610509359^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143661153 10000000000 31592610509359 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078562471/2500000000 : ℝ), (4491295761/10000000000 : ℝ), (4143661153/10000000000 : ℝ)] ![(33304346277199/100000000000000 : ℝ), (17551521598721/50000000000000 : ℝ), (31592610509359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078562471/2500000000 : ℝ)|^2175 ≤ (33304346277199/100000000000000 : ℝ)^1663
        have hw : |(1078562471/2500000000 : ℝ)|=(1078562471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491295761/10000000000 : ℝ)|^2175 ≤ (17551521598721/50000000000000 : ℝ)^1663
        have hw : |(4491295761/10000000000 : ℝ)|=(4491295761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4143661153/10000000000 : ℝ)|^2175 ≤ (31592610509359/100000000000000 : ℝ)^1663
        have hw : |(4143661153/10000000000 : ℝ)|=(4143661153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1390_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (921/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5629/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2947/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (921/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11257/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (921/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11257/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (921/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11257/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (921/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11257/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (921/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11257/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (921/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11257/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11257/100000 : ℝ) ^ (4349/1024 : ℝ) ≤ (9361067267382797/100000000000000000000 : ℝ) := by
    have hpowers : (11257/100000 : ℝ)^4349 ≤ (9361067267382797/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11257 : ℕ)^4349*100000000000000000000^1024 ≤ 9361067267382797^1024*100000^4349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11257 100000 9361067267382797 100000000000000000000 4349 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11257/100000 : ℝ)) (X := (9361067267382797/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (921/6250 : ℝ) ^ (4349/1024 : ℝ) ≤ (14689930693568367/50000000000000000000 : ℝ) := by
    have hpowers : (921/6250 : ℝ)^4349 ≤ (14689930693568367/50000000000000000000 : ℝ)^1024 := by
      have hnat : (921 : ℕ)^4349*50000000000000000000^1024 ≤ 14689930693568367^1024*6250^4349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        921 6250 14689930693568367 50000000000000000000 4349 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (921/6250 : ℝ)) (X := (14689930693568367/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009361067267382797/50000000000000000000 : ℝ) ≤ (2000088158628759/2000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (50009361067267382797/50000000000000000000 : ℝ)^1024 ≤ (2000088158628759/2000000000000000 : ℝ)^4349 := by
      have hnat : (50009361067267382797 : ℕ)^1024*2000000000000000^4349 ≤ 2000088158628759^4349*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009361067267382797 50000000000000000000 2000088158628759 2000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000088158628759/2000000000000000 : ℝ)) (X := (50009361067267382797/50000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038740928654519531/100000000000000000000 : ℝ) ≤ (10000912045003939/10000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (100038740928654519531/100000000000000000000 : ℝ)^1024 ≤ (10000912045003939/10000000000000000 : ℝ)^4349 := by
      have hnat : (100038740928654519531 : ℕ)^1024*10000000000000000^4349 ≤ 10000912045003939^4349*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038740928654519531 100000000000000000000 10000912045003939 10000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000912045003939/10000000000000000 : ℝ)) (X := (100038740928654519531/100000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014689930693568367/25000000000000000000 : ℝ) ≤ (10001383296864083/10000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (25014689930693568367/25000000000000000000 : ℝ)^1024 ≤ (10001383296864083/10000000000000000 : ℝ)^4349 := by
      have hnat : (25014689930693568367 : ℕ)^1024*10000000000000000^4349 ≤ 10001383296864083^4349*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014689930693568367 25000000000000000000 10001383296864083 10000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001383296864083/10000000000000000 : ℝ)) (X := (25014689930693568367/25000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9361067267382797/100000000000000000000 : ℝ) ≤ ((34780923754967980789/34790000000000000000 : ℝ)+2*(29453241259/21743750000000 : ℝ)*(11257/100000 : ℝ))^(4349/1024 : ℝ) := by
    rw [show (34780923754967980789/34790000000000000000 : ℝ)+2*(29453241259/21743750000000 : ℝ)*(11257/100000 : ℝ)=(2000088158628759/2000000000000000 : ℝ) by norm_num, show 1+2*(9361067267382797/100000000000000000000 : ℝ)=(50009361067267382797/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14689930693568367/50000000000000000000 : ℝ)+(9361067267382797/100000000000000000000 : ℝ) ≤ ((34780923754967980789/34790000000000000000 : ℝ)+(29453241259/21743750000000 : ℝ)*((921/6250 : ℝ)+(11257/100000 : ℝ)))^(4349/1024 : ℝ) := by
    rw [show (34780923754967980789/34790000000000000000 : ℝ)+(29453241259/21743750000000 : ℝ)*((921/6250 : ℝ)+(11257/100000 : ℝ))=(10000912045003939/10000000000000000 : ℝ) by norm_num, show 1+(14689930693568367/50000000000000000000 : ℝ)+(9361067267382797/100000000000000000000 : ℝ)=(100038740928654519531/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14689930693568367/50000000000000000000 : ℝ) ≤ ((34780923754967980789/34790000000000000000 : ℝ)+2*(29453241259/21743750000000 : ℝ)*(921/6250 : ℝ))^(4349/1024 : ℝ) := by
    rw [show (34780923754967980789/34790000000000000000 : ℝ)+2*(29453241259/21743750000000 : ℝ)*(921/6250 : ℝ)=(10001383296864083/10000000000000000 : ℝ) by norm_num, show 1+2*(14689930693568367/50000000000000000000 : ℝ)=(25014689930693568367/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34780923754967980789/34790000000000000000 : ℝ)*(X 1 0+X 2 0)+(29453241259/21743750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (11257/100000 : ℝ)) (hi := (921/6250 : ℝ)) (c := (34780923754967980789/34790000000000000000 : ℝ)) (alpha := (29453241259/21743750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34780923754967980789/34790000000000000000 : ℝ)*(X 0 1+X 2 1)+(29453241259/21743750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (11257/100000 : ℝ)) (hi := (921/6250 : ℝ)) (c := (34780923754967980789/34790000000000000000 : ℝ)) (alpha := (29453241259/21743750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34780923754967980789/34790000000000000000 : ℝ)*(X 0 2+X 1 2)+(29453241259/21743750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (11257/100000 : ℝ)) (hi := (921/6250 : ℝ)) (c := (34780923754967980789/34790000000000000000 : ℝ)) (alpha := (29453241259/21743750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-62600699/312500000 : ℝ)*X 0 0+(5410198983/10000000000 : ℝ)*X 0 1+(5245995013/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334256813/625000000 : ℝ)*X 1 0+(-521712029/2500000000 : ℝ)*X 1 1+(1311498751/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534810863/1000000000 : ℝ)*X 2 0+(81968679/156250000 : ℝ)*X 2 1+(-2086848021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4314224563/10000000000 : ℝ)*X 0 0+(517799607/1250000000 : ℝ)*X 0 1+(4492553983/10000000000 : ℝ)*X 0 2+(4314224563/10000000000 : ℝ)*X 1 0+(517799607/1250000000 : ℝ)*X 1 1+(4492553983/10000000000 : ℝ)*X 1 2+(4314224563/10000000000 : ℝ)*X 2 0+(517799607/1250000000 : ℝ)*X 2 1+(4492553983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2003233933/10000000000 : ℝ)*X 0 0+(5246585331/10000000000 : ℝ)*X 0 1+(2704802851/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305589039/10000000000 : ℝ)*X 1 0+(-48080943/250000000 : ℝ)*X 1 1+(338100359/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305589003/10000000000 : ℝ)*X 2 0+(5409605749/10000000000 : ℝ)*X 2 1+(-961618881/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1078562471/2500000000 : ℝ)*X 0 0+(4491295761/10000000000 : ℝ)*X 0 1+(4143661153/10000000000 : ℝ)*X 0 2+(1078562471/2500000000 : ℝ)*X 1 0+(4491295761/10000000000 : ℝ)*X 1 1+(4143661153/10000000000 : ℝ)*X 1 2+(1078562471/2500000000 : ℝ)*X 2 0+(4491295761/10000000000 : ℝ)*X 2 1+(4143661153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8025110720455943792697/1087187500000000000000000000 : ℝ) := by norm_num
    linear_combination (2063633223/100000000000000 : ℝ)*(base19) + (346102429/25000000000000 : ℝ)*(base23) + (50189509/25000000000000 : ℝ)*(upper3) + (13305093/10000000000000 : ℝ)*(upper4) + (69503577/100000000000000 : ℝ)*(upper5) + (1118247740199837/25000000000000 : ℝ)*(major0) + (1118247740199837/25000000000000 : ℝ)*(major1) + (1118247740199837/25000000000000 : ℝ)*(major2) + (1522509712168853/25000000000000 : ℝ)*(sp0) + (6090084142165213/100000000000000 : ℝ)*(sp1) + (76126060267359/1250000000000 : ℝ)*(sp2) + (178492335937533/6250000000000 : ℝ)*(sp3) + (2959820189/6250000000000 : ℝ)*(sp4) + (2261843577/12500000000000 : ℝ)*(sp7) + (356986933718643/12500000000000 : ℝ)*(f.failure) + (1522521551449609/25000000000000 : ℝ)*(f.sum) + (6306256919/8493652343750000000000000 : ℝ)*base65 + (3344815436269268607/869750000000000000000000000000000 : ℝ)*base68 + (7236565853888731393/869750000000000000000000000000000 : ℝ)*base69 + (4366462775422268607/869750000000000000000000000000000 : ℝ)*base72 + (1155201099973/4348750000000000000000000000 : ℝ)*base73 + (16641178998290731393/869750000000000000000000000000000 : ℝ)*base75 + (1071984043781731393/869750000000000000000000000000000 : ℝ)*base77 + (8345346849524268607/869750000000000000000000000000000 : ℝ)*base80 + (7900186451509/2174375000000000000000000000 : ℝ)*base81 + (3136491/1250000000000000000000 : ℝ)*base90 + (3136491/1250000000000000000000 : ℝ)*base92 + (3136491/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10798469589612496904103219/3479000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (592757877/100000000000000 : ℝ)*(base19) + (118830961/20000000000000 : ℝ)*(base23) + (10612891/5000000000000 : ℝ)*(lower1) + (8853151/12500000000000 : ℝ)*(upper3) + (26665279/100000000000000 : ℝ)*(lower4) + (76421089/100000000000000 : ℝ)*(upper5) + (9010765982681/200000000000 : ℝ)*(major0) + (9010765982681/200000000000 : ℝ)*(major1) + (9010765982681/200000000000 : ℝ)*(major2) + (36134061/4000000000000 : ℝ)*(sp1) + (6134188889186167/100000000000000 : ℝ)*(sp4) + (1226837478615353/20000000000000 : ℝ)*(sp5) + (3067094147515681/50000000000000 : ℝ)*(sp6) + (1438288495015737/50000000000000 : ℝ)*(sp7) + (1438288495015737/50000000000000 : ℝ)*(f.failure) + (6134188889186167/100000000000000 : ℝ)*(f.sum) + (2884444196559/695800000000000000000000000 : ℝ)*base66 + (77153455099737309/6958000000000000000000000000000 : ℝ)*base67 + (78618421886867309/6958000000000000000000000000000 : ℝ)*base69 + (72191238696257309/6958000000000000000000000000000 : ℝ)*base71 + (6732721566653/1739500000000000000000000000 : ℝ)*base74 + (108955336495959309/6958000000000000000000000000000 : ℝ)*base75 + (25887863573399309/6958000000000000000000000000000 : ℝ)*base77 + (107071575794899309/6958000000000000000000000000000 : ℝ)*base79 + (936370962319/1739500000000000000000000000 : ℝ)*base81 + (37857569/5000000000000000000000 : ℝ)*base90 + (37857569/5000000000000000000000 : ℝ)*base92 + (37857569/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1390_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (921/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2947/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1390_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1390_box_0 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-459920923/2500000000 : ℝ)*x 0 + (1346979601/2500000000 : ℝ)*x 1 + (1077583667/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (459920923/2500000000 : ℝ)^2175 ≤ (10923812703153/100000000000000 : ℝ)^1663 := by
    have hnat : (459920923 : ℕ)^2175*100000000000000^1663 ≤ 10923812703153^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459920923 2500000000 10923812703153 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346979601/2500000000 : ℝ)^2175 ≤ (44538094014161/100000000000000 : ℝ)^1663 := by
    have hnat : (1346979601 : ℕ)^2175*100000000000000^1663 ≤ 44538094014161^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346979601 2500000000 44538094014161 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077583667/2000000000 : ℝ)^2175 ≤ (22269046634091/50000000000000 : ℝ)^1663 := by
    have hnat : (1077583667 : ℕ)^2175*50000000000000^1663 ≤ 22269046634091^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077583667 2000000000 22269046634091 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-459920923/2500000000 : ℝ), (1346979601/2500000000 : ℝ), (1077583667/2000000000 : ℝ)] ![(10923812703153/100000000000000 : ℝ), (44538094014161/100000000000000 : ℝ), (22269046634091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-459920923/2500000000 : ℝ)|^2175 ≤ (10923812703153/100000000000000 : ℝ)^1663
        have hw : |(-459920923/2500000000 : ℝ)|=(459920923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346979601/2500000000 : ℝ)|^2175 ≤ (44538094014161/100000000000000 : ℝ)^1663
        have hw : |(1346979601/2500000000 : ℝ)|=(1346979601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077583667/2000000000 : ℝ)|^2175 ≤ (22269046634091/50000000000000 : ℝ)^1663
        have hw : |(1077583667/2000000000 : ℝ)|=(1077583667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_box_1 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5285731637/10000000000 : ℝ)*x 0 + (-3093603/15625000 : ℝ)*x 1 + (673489841/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285731637/10000000000 : ℝ)^2175 ≤ (43436562657607/100000000000000 : ℝ)^1663 := by
    have hnat : (5285731637 : ℕ)^2175*100000000000000^1663 ≤ 43436562657607^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285731637 10000000000 43436562657607 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3093603/15625000 : ℝ)^2175 ≤ (481013592381/4000000000000 : ℝ)^1663 := by
    have hnat : (3093603 : ℕ)^2175*4000000000000^1663 ≤ 481013592381^1663*15625000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3093603 15625000 481013592381 4000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673489841/1250000000 : ℝ)^2175 ≤ (2226904875851/5000000000000 : ℝ)^1663 := by
    have hnat : (673489841 : ℕ)^2175*5000000000000^1663 ≤ 2226904875851^1663*1250000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673489841 1250000000 2226904875851 5000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285731637/10000000000 : ℝ), (-3093603/15625000 : ℝ), (673489841/1250000000 : ℝ)] ![(43436562657607/100000000000000 : ℝ), (481013592381/4000000000000 : ℝ), (2226904875851/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285731637/10000000000 : ℝ)|^2175 ≤ (43436562657607/100000000000000 : ℝ)^1663
        have hw : |(5285731637/10000000000 : ℝ)|=(5285731637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3093603/15625000 : ℝ)|^2175 ≤ (481013592381/4000000000000 : ℝ)^1663
        have hw : |(-3093603/15625000 : ℝ)|=(3093603/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673489841/1250000000 : ℝ)|^2175 ≤ (2226904875851/5000000000000 : ℝ)^1663
        have hw : |(673489841/1250000000 : ℝ)|=(673489841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_box_2 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5285731211/10000000000 : ℝ)*x 0 + (1346979757/2500000000 : ℝ)*x 1 + (-1979906089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285731211/10000000000 : ℝ)^2175 ≤ (10859139519767/25000000000000 : ℝ)^1663 := by
    have hnat : (5285731211 : ℕ)^2175*25000000000000^1663 ≤ 10859139519767^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285731211 10000000000 10859139519767 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346979757/2500000000 : ℝ)^2175 ≤ (5567262595051/12500000000000 : ℝ)^1663 := by
    have hnat : (1346979757 : ℕ)^2175*12500000000000^1663 ≤ 5567262595051^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346979757 2500000000 5567262595051 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1979906089/10000000000 : ℝ)^2175 ≤ (12025341152001/100000000000000 : ℝ)^1663 := by
    have hnat : (1979906089 : ℕ)^2175*100000000000000^1663 ≤ 12025341152001^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1979906089 10000000000 12025341152001 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285731211/10000000000 : ℝ), (1346979757/2500000000 : ℝ), (-1979906089/10000000000 : ℝ)] ![(10859139519767/25000000000000 : ℝ), (5567262595051/12500000000000 : ℝ), (12025341152001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285731211/10000000000 : ℝ)|^2175 ≤ (10859139519767/25000000000000 : ℝ)^1663
        have hw : |(5285731211/10000000000 : ℝ)|=(5285731211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346979757/2500000000 : ℝ)|^2175 ≤ (5567262595051/12500000000000 : ℝ)^1663
        have hw : |(1346979757/2500000000 : ℝ)|=(1346979757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1979906089/10000000000 : ℝ)|^2175 ≤ (12025341152001/100000000000000 : ℝ)^1663
        have hw : |(-1979906089/10000000000 : ℝ)|=(1979906089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_box_3 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2230666307/5000000000 : ℝ)*x 0 + (66319647/156250000 : ℝ)*x 1 + (4244457959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2230666307/5000000000 : ℝ)^2175 ≤ (17398535974429/50000000000000 : ℝ)^1663 := by
    have hnat : (2230666307 : ℕ)^2175*50000000000000^1663 ≤ 17398535974429^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230666307 5000000000 17398535974429 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66319647/156250000 : ℝ)^2175 ≤ (32601461253493/100000000000000 : ℝ)^1663 := by
    have hnat : (66319647 : ℕ)^2175*100000000000000^1663 ≤ 32601461253493^1663*156250000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66319647 156250000 32601461253493 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4244457959/10000000000 : ℝ)^2175 ≤ (4075183348587/12500000000000 : ℝ)^1663 := by
    have hnat : (4244457959 : ℕ)^2175*12500000000000^1663 ≤ 4075183348587^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244457959 10000000000 4075183348587 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2230666307/5000000000 : ℝ), (66319647/156250000 : ℝ), (4244457959/10000000000 : ℝ)] ![(17398535974429/50000000000000 : ℝ), (32601461253493/100000000000000 : ℝ), (4075183348587/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2230666307/5000000000 : ℝ)|^2175 ≤ (17398535974429/50000000000000 : ℝ)^1663
        have hw : |(2230666307/5000000000 : ℝ)|=(2230666307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(66319647/156250000 : ℝ)|^2175 ≤ (32601461253493/100000000000000 : ℝ)^1663
        have hw : |(66319647/156250000 : ℝ)|=(66319647/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4244457959/10000000000 : ℝ)|^2175 ≤ (4075183348587/12500000000000 : ℝ)^1663
        have hw : |(4244457959/10000000000 : ℝ)|=(4244457959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_box_4 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1084751771/5000000000 : ℝ)*x 0 + (1316472253/2500000000 : ℝ)*x 1 + (2632943981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084751771/5000000000 : ℝ)^2175 ≤ (2710633240161/20000000000000 : ℝ)^1663 := by
    have hnat : (1084751771 : ℕ)^2175*20000000000000^1663 ≤ 2710633240161^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084751771 5000000000 2710633240161 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316472253/2500000000 : ℝ)^2175 ≤ (43223422533387/100000000000000 : ℝ)^1663 := by
    have hnat : (1316472253 : ℕ)^2175*100000000000000^1663 ≤ 43223422533387^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316472253 2500000000 43223422533387 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632943981/5000000000 : ℝ)^2175 ≤ (10805852815329/25000000000000 : ℝ)^1663 := by
    have hnat : (2632943981 : ℕ)^2175*25000000000000^1663 ≤ 10805852815329^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632943981 5000000000 10805852815329 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1084751771/5000000000 : ℝ), (1316472253/2500000000 : ℝ), (2632943981/5000000000 : ℝ)] ![(2710633240161/20000000000000 : ℝ), (43223422533387/100000000000000 : ℝ), (10805852815329/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1084751771/5000000000 : ℝ)|^2175 ≤ (2710633240161/20000000000000 : ℝ)^1663
        have hw : |(-1084751771/5000000000 : ℝ)|=(1084751771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316472253/2500000000 : ℝ)|^2175 ≤ (43223422533387/100000000000000 : ℝ)^1663
        have hw : |(1316472253/2500000000 : ℝ)|=(1316472253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632943981/5000000000 : ℝ)|^2175 ≤ (10805852815329/25000000000000 : ℝ)^1663
        have hw : |(2632943981/5000000000 : ℝ)|=(2632943981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_box_5 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1074254229/2000000000 : ℝ)*x 0 + (-101459833/500000000 : ℝ)*x 1 + (2632944329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074254229/2000000000 : ℝ)^2175 ≤ (44358201286933/100000000000000 : ℝ)^1663 := by
    have hnat : (1074254229 : ℕ)^2175*100000000000000^1663 ≤ 44358201286933^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074254229 2000000000 44358201286933 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (101459833/500000000 : ℝ)^2175 ≤ (97018593523/781250000000 : ℝ)^1663 := by
    have hnat : (101459833 : ℕ)^2175*781250000000^1663 ≤ 97018593523^1663*500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101459833 500000000 97018593523 781250000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632944329/5000000000 : ℝ)^2175 ≤ (43223418733089/100000000000000 : ℝ)^1663 := by
    have hnat : (2632944329 : ℕ)^2175*100000000000000^1663 ≤ 43223418733089^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632944329 5000000000 43223418733089 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074254229/2000000000 : ℝ), (-101459833/500000000 : ℝ), (2632944329/5000000000 : ℝ)] ![(44358201286933/100000000000000 : ℝ), (97018593523/781250000000 : ℝ), (43223418733089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074254229/2000000000 : ℝ)|^2175 ≤ (44358201286933/100000000000000 : ℝ)^1663
        have hw : |(1074254229/2000000000 : ℝ)|=(1074254229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-101459833/500000000 : ℝ)|^2175 ≤ (97018593523/781250000000 : ℝ)^1663
        have hw : |(-101459833/500000000 : ℝ)|=(101459833/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632944329/5000000000 : ℝ)|^2175 ≤ (43223418733089/100000000000000 : ℝ)^1663
        have hw : |(2632944329/5000000000 : ℝ)|=(2632944329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_box_6 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2685635289/5000000000 : ℝ)*x 0 + (5265888991/10000000000 : ℝ)*x 1 + (-1014598489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685635289/5000000000 : ℝ)^2175 ≤ (2772387197673/6250000000000 : ℝ)^1663 := by
    have hnat : (2685635289 : ℕ)^2175*6250000000000^1663 ≤ 2772387197673^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685635289 5000000000 2772387197673 6250000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265888991/10000000000 : ℝ)^2175 ≤ (21611711153973/50000000000000 : ℝ)^1663 := by
    have hnat : (5265888991 : ℕ)^2175*50000000000000^1663 ≤ 21611711153973^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265888991 10000000000 21611711153973 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1014598489/5000000000 : ℝ)^2175 ≤ (620919125811/5000000000000 : ℝ)^1663 := by
    have hnat : (1014598489 : ℕ)^2175*5000000000000^1663 ≤ 620919125811^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014598489 5000000000 620919125811 5000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685635289/5000000000 : ℝ), (5265888991/10000000000 : ℝ), (-1014598489/5000000000 : ℝ)] ![(2772387197673/6250000000000 : ℝ), (21611711153973/50000000000000 : ℝ), (620919125811/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685635289/5000000000 : ℝ)|^2175 ≤ (2772387197673/6250000000000 : ℝ)^1663
        have hw : |(2685635289/5000000000 : ℝ)|=(2685635289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265888991/10000000000 : ℝ)|^2175 ≤ (21611711153973/50000000000000 : ℝ)^1663
        have hw : |(5265888991/10000000000 : ℝ)|=(5265888991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1014598489/5000000000 : ℝ)|^2175 ≤ (620919125811/5000000000000 : ℝ)^1663
        have hw : |(-1014598489/5000000000 : ℝ)|=(1014598489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_box_7 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2083061231/5000000000 : ℝ)*x 0 + (1098002599/2500000000 : ℝ)*x 1 + (2196005509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083061231/5000000000 : ℝ)^2175 ≤ (31816774137233/100000000000000 : ℝ)^1663 := by
    have hnat : (2083061231 : ℕ)^2175*100000000000000^1663 ≤ 31816774137233^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083061231 5000000000 31816774137233 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098002599/2500000000 : ℝ)^2175 ≤ (681832195293/2000000000000 : ℝ)^1663 := by
    have hnat : (1098002599 : ℕ)^2175*2000000000000^1663 ≤ 681832195293^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098002599 2500000000 681832195293 2000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2196005509/5000000000 : ℝ)^2175 ≤ (34091616079187/100000000000000 : ℝ)^1663 := by
    have hnat : (2196005509 : ℕ)^2175*100000000000000^1663 ≤ 34091616079187^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196005509 5000000000 34091616079187 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2083061231/5000000000 : ℝ), (1098002599/2500000000 : ℝ), (2196005509/5000000000 : ℝ)] ![(31816774137233/100000000000000 : ℝ), (681832195293/2000000000000 : ℝ), (34091616079187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2083061231/5000000000 : ℝ)|^2175 ≤ (31816774137233/100000000000000 : ℝ)^1663
        have hw : |(2083061231/5000000000 : ℝ)|=(2083061231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1098002599/2500000000 : ℝ)|^2175 ≤ (681832195293/2000000000000 : ℝ)^1663
        have hw : |(1098002599/2500000000 : ℝ)|=(1098002599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2196005509/5000000000 : ℝ)|^2175 ≤ (34091616079187/100000000000000 : ℝ)^1663
        have hw : |(2196005509/5000000000 : ℝ)|=(2196005509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_box_8 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1050061407/5000000000 : ℝ)*x 0 + (207266341/400000000 : ℝ)*x 1 + (42202463/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050061407/5000000000 : ℝ)^2175 ≤ (3247276031559/25000000000000 : ℝ)^1663 := by
    have hnat : (1050061407 : ℕ)^2175*25000000000000^1663 ≤ 3247276031559^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050061407 5000000000 3247276031559 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207266341/400000000 : ℝ)^2175 ≤ (42321417213471/100000000000000 : ℝ)^1663 := by
    have hnat : (207266341 : ℕ)^2175*100000000000000^1663 ≤ 42321417213471^1663*400000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207266341 400000000 42321417213471 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42202463/78125000 : ℝ)^2175 ≤ (44689478645129/100000000000000 : ℝ)^1663 := by
    have hnat : (42202463 : ℕ)^2175*100000000000000^1663 ≤ 44689478645129^1663*78125000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42202463 78125000 44689478645129 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1050061407/5000000000 : ℝ), (207266341/400000000 : ℝ), (42202463/78125000 : ℝ)] ![(3247276031559/25000000000000 : ℝ), (42321417213471/100000000000000 : ℝ), (44689478645129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1050061407/5000000000 : ℝ)|^2175 ≤ (3247276031559/25000000000000 : ℝ)^1663
        have hw : |(-1050061407/5000000000 : ℝ)|=(1050061407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207266341/400000000 : ℝ)|^2175 ≤ (42321417213471/100000000000000 : ℝ)^1663
        have hw : |(207266341/400000000 : ℝ)|=(207266341/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42202463/78125000 : ℝ)|^2175 ≤ (44689478645129/100000000000000 : ℝ)^1663
        have hw : |(42202463/78125000 : ℝ)|=(42202463/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_box_9 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5275916057/10000000000 : ℝ)*x 0 + (-1974123579/10000000000 : ℝ)*x 1 + (2700957459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275916057/10000000000 : ℝ)^2175 ≤ (8666219495451/20000000000000 : ℝ)^1663 := by
    have hnat : (5275916057 : ℕ)^2175*20000000000000^1663 ≤ 8666219495451^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275916057 10000000000 8666219495451 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1974123579/10000000000 : ℝ)^2175 ≤ (11979427611053/100000000000000 : ℝ)^1663 := by
    have hnat : (1974123579 : ℕ)^2175*100000000000000^1663 ≤ 11979427611053^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1974123579 10000000000 11979427611053 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700957459/5000000000 : ℝ)^2175 ≤ (44689474901433/100000000000000 : ℝ)^1663 := by
    have hnat : (2700957459 : ℕ)^2175*100000000000000^1663 ≤ 44689474901433^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700957459 5000000000 44689474901433 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275916057/10000000000 : ℝ), (-1974123579/10000000000 : ℝ), (2700957459/5000000000 : ℝ)] ![(8666219495451/20000000000000 : ℝ), (11979427611053/100000000000000 : ℝ), (44689474901433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275916057/10000000000 : ℝ)|^2175 ≤ (8666219495451/20000000000000 : ℝ)^1663
        have hw : |(5275916057/10000000000 : ℝ)|=(5275916057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1974123579/10000000000 : ℝ)|^2175 ≤ (11979427611053/100000000000000 : ℝ)^1663
        have hw : |(-1974123579/10000000000 : ℝ)|=(1974123579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700957459/5000000000 : ℝ)|^2175 ≤ (44689474901433/100000000000000 : ℝ)^1663
        have hw : |(2700957459/5000000000 : ℝ)|=(2700957459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_box_10 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2637957833/5000000000 : ℝ)*x 0 + (1350478791/2500000000 : ℝ)*x 1 + (-493530943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637957833/5000000000 : ℝ)^2175 ≤ (43331093277291/100000000000000 : ℝ)^1663 := by
    have hnat : (2637957833 : ℕ)^2175*100000000000000^1663 ≤ 43331093277291^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637957833 5000000000 43331093277291 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350478791/2500000000 : ℝ)^2175 ≤ (174568271731/390625000000 : ℝ)^1663 := by
    have hnat : (1350478791 : ℕ)^2175*390625000000^1663 ≤ 174568271731^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350478791 2500000000 174568271731 390625000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (493530943/2500000000 : ℝ)^2175 ≤ (11979429142797/100000000000000 : ℝ)^1663 := by
    have hnat : (493530943 : ℕ)^2175*100000000000000^1663 ≤ 11979429142797^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493530943 2500000000 11979429142797 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637957833/5000000000 : ℝ), (1350478791/2500000000 : ℝ), (-493530943/2500000000 : ℝ)] ![(43331093277291/100000000000000 : ℝ), (174568271731/390625000000 : ℝ), (11979429142797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637957833/5000000000 : ℝ)|^2175 ≤ (43331093277291/100000000000000 : ℝ)^1663
        have hw : |(2637957833/5000000000 : ℝ)|=(2637957833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350478791/2500000000 : ℝ)|^2175 ≤ (174568271731/390625000000 : ℝ)^1663
        have hw : |(1350478791/2500000000 : ℝ)|=(1350478791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-493530943/2500000000 : ℝ)|^2175 ≤ (11979429142797/100000000000000 : ℝ)^1663
        have hw : |(-493530943/2500000000 : ℝ)|=(493530943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_box_11 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4494634017/10000000000 : ℝ)*x 0 + (4227519333/10000000000 : ℝ)*x 1 + (4227520141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4494634017/10000000000 : ℝ)^2175 ≤ (17568585543927/50000000000000 : ℝ)^1663 := by
    have hnat : (4494634017 : ℕ)^2175*50000000000000^1663 ≤ 17568585543927^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494634017 10000000000 17568585543927 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227519333/10000000000 : ℝ)^2175 ≤ (6486282078969/20000000000000 : ℝ)^1663 := by
    have hnat : (4227519333 : ℕ)^2175*20000000000000^1663 ≤ 6486282078969^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227519333 10000000000 6486282078969 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227520141/10000000000 : ℝ)^2175 ≤ (4053927312727/12500000000000 : ℝ)^1663 := by
    have hnat : (4227520141 : ℕ)^2175*12500000000000^1663 ≤ 4053927312727^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227520141 10000000000 4053927312727 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4494634017/10000000000 : ℝ), (4227519333/10000000000 : ℝ), (4227520141/10000000000 : ℝ)] ![(17568585543927/50000000000000 : ℝ), (6486282078969/20000000000000 : ℝ), (4053927312727/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4494634017/10000000000 : ℝ)|^2175 ≤ (17568585543927/50000000000000 : ℝ)^1663
        have hw : |(4494634017/10000000000 : ℝ)|=(4494634017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227519333/10000000000 : ℝ)|^2175 ≤ (6486282078969/20000000000000 : ℝ)^1663
        have hw : |(4227519333/10000000000 : ℝ)|=(4227519333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227520141/10000000000 : ℝ)|^2175 ≤ (4053927312727/12500000000000 : ℝ)^1663
        have hw : |(4227520141/10000000000 : ℝ)|=(4227520141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_box_12 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1909311939/10000000000 : ℝ)*x 0 + (5470046401/10000000000 : ℝ)*x 1 + (2627392209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1909311939/10000000000 : ℝ)^2175 ≤ (11467669936199/100000000000000 : ℝ)^1663 := by
    have hnat : (1909311939 : ℕ)^2175*100000000000000^1663 ≤ 11467669936199^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909311939 10000000000 11467669936199 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470046401/10000000000 : ℝ)^2175 ≤ (1817123201009/4000000000000 : ℝ)^1663 := by
    have hnat : (5470046401 : ℕ)^2175*4000000000000^1663 ≤ 1817123201009^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470046401 10000000000 1817123201009 4000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627392209/5000000000 : ℝ)^2175 ≤ (43104250026681/100000000000000 : ℝ)^1663 := by
    have hnat : (2627392209 : ℕ)^2175*100000000000000^1663 ≤ 43104250026681^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627392209 5000000000 43104250026681 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1909311939/10000000000 : ℝ), (5470046401/10000000000 : ℝ), (2627392209/5000000000 : ℝ)] ![(11467669936199/100000000000000 : ℝ), (1817123201009/4000000000000 : ℝ), (43104250026681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1909311939/10000000000 : ℝ)|^2175 ≤ (11467669936199/100000000000000 : ℝ)^1663
        have hw : |(-1909311939/10000000000 : ℝ)|=(1909311939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470046401/10000000000 : ℝ)|^2175 ≤ (1817123201009/4000000000000 : ℝ)^1663
        have hw : |(5470046401/10000000000 : ℝ)|=(5470046401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627392209/5000000000 : ℝ)|^2175 ≤ (43104250026681/100000000000000 : ℝ)^1663
        have hw : |(2627392209/5000000000 : ℝ)|=(2627392209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_box_13 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5379052923/10000000000 : ℝ)*x 0 + (-1016790219/5000000000 : ℝ)*x 1 + (5254784373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379052923/10000000000 : ℝ)^2175 ≤ (2777641936887/6250000000000 : ℝ)^1663 := by
    have hnat : (5379052923 : ℕ)^2175*6250000000000^1663 ≤ 2777641936887^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379052923 10000000000 2777641936887 6250000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016790219/5000000000 : ℝ)^2175 ≤ (12453479452677/100000000000000 : ℝ)^1663 := by
    have hnat : (1016790219 : ℕ)^2175*100000000000000^1663 ≤ 12453479452677^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016790219 5000000000 12453479452677 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254784373/10000000000 : ℝ)^2175 ≤ (21552124771953/50000000000000 : ℝ)^1663 := by
    have hnat : (5254784373 : ℕ)^2175*50000000000000^1663 ≤ 21552124771953^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254784373 10000000000 21552124771953 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379052923/10000000000 : ℝ), (-1016790219/5000000000 : ℝ), (5254784373/10000000000 : ℝ)] ![(2777641936887/6250000000000 : ℝ), (12453479452677/100000000000000 : ℝ), (21552124771953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379052923/10000000000 : ℝ)|^2175 ≤ (2777641936887/6250000000000 : ℝ)^1663
        have hw : |(5379052923/10000000000 : ℝ)|=(5379052923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1016790219/5000000000 : ℝ)|^2175 ≤ (12453479452677/100000000000000 : ℝ)^1663
        have hw : |(-1016790219/5000000000 : ℝ)|=(1016790219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254784373/10000000000 : ℝ)|^2175 ≤ (21552124771953/50000000000000 : ℝ)^1663
        have hw : |(5254784373/10000000000 : ℝ)|=(5254784373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_box_14 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (268952647/500000000 : ℝ)*x 0 + (2627392093/5000000000 : ℝ)*x 1 + (-406716133/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268952647/500000000 : ℝ)^2175 ≤ (44442271173891/100000000000000 : ℝ)^1663 := by
    have hnat : (268952647 : ℕ)^2175*100000000000000^1663 ≤ 44442271173891^1663*500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268952647 500000000 44442271173891 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627392093/5000000000 : ℝ)^2175 ≤ (10776061884427/25000000000000 : ℝ)^1663 := by
    have hnat : (2627392093 : ℕ)^2175*25000000000000^1663 ≤ 10776061884427^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627392093 5000000000 10776061884427 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (406716133/2000000000 : ℝ)^2175 ≤ (3113370317699/25000000000000 : ℝ)^1663 := by
    have hnat : (406716133 : ℕ)^2175*25000000000000^1663 ≤ 3113370317699^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406716133 2000000000 3113370317699 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268952647/500000000 : ℝ), (2627392093/5000000000 : ℝ), (-406716133/2000000000 : ℝ)] ![(44442271173891/100000000000000 : ℝ), (10776061884427/25000000000000 : ℝ), (3113370317699/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268952647/500000000 : ℝ)|^2175 ≤ (44442271173891/100000000000000 : ℝ)^1663
        have hw : |(268952647/500000000 : ℝ)|=(268952647/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627392093/5000000000 : ℝ)|^2175 ≤ (10776061884427/25000000000000 : ℝ)^1663
        have hw : |(2627392093/5000000000 : ℝ)|=(2627392093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-406716133/2000000000 : ℝ)|^2175 ≤ (3113370317699/25000000000000 : ℝ)^1663
        have hw : |(-406716133/2000000000 : ℝ)|=(406716133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_box_15 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1034702811/2500000000 : ℝ)*x 0 + (4405426043/10000000000 : ℝ)*x 1 + (4405426433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034702811/2500000000 : ℝ)^2175 ≤ (31544257489399/100000000000000 : ℝ)^1663 := by
    have hnat : (1034702811 : ℕ)^2175*100000000000000^1663 ≤ 31544257489399^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034702811 2500000000 31544257489399 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4405426043/10000000000 : ℝ)^2175 ≤ (6845573853713/20000000000000 : ℝ)^1663 := by
    have hnat : (4405426043 : ℕ)^2175*20000000000000^1663 ≤ 6845573853713^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4405426043 10000000000 6845573853713 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4405426433/10000000000 : ℝ)^2175 ≤ (34227873231561/100000000000000 : ℝ)^1663 := by
    have hnat : (4405426433 : ℕ)^2175*100000000000000^1663 ≤ 34227873231561^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4405426433 10000000000 34227873231561 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034702811/2500000000 : ℝ), (4405426043/10000000000 : ℝ), (4405426433/10000000000 : ℝ)] ![(31544257489399/100000000000000 : ℝ), (6845573853713/20000000000000 : ℝ), (34227873231561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034702811/2500000000 : ℝ)|^2175 ≤ (31544257489399/100000000000000 : ℝ)^1663
        have hw : |(1034702811/2500000000 : ℝ)|=(1034702811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4405426043/10000000000 : ℝ)|^2175 ≤ (6845573853713/20000000000000 : ℝ)^1663
        have hw : |(4405426043/10000000000 : ℝ)|=(4405426043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4405426433/10000000000 : ℝ)|^2175 ≤ (34227873231561/100000000000000 : ℝ)^1663
        have hw : |(4405426433/10000000000 : ℝ)|=(4405426433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1390_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2947/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62877/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11807/20000 : ℝ) ∧ (80231/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84537/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2947/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5629/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2947/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5629/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2947/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5629/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2947/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5629/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2947/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5629/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2947/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5629/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5629/50000 : ℝ) ^ (4349/1024 : ℝ) ≤ (9364599544651647/100000000000000000000 : ℝ) := by
    have hpowers : (5629/50000 : ℝ)^4349 ≤ (9364599544651647/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5629 : ℕ)^4349*100000000000000000000^1024 ≤ 9364599544651647^1024*50000^4349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5629 50000 9364599544651647 100000000000000000000 4349 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5629/50000 : ℝ)) (X := (9364599544651647/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2947/20000 : ℝ) ^ (4349/1024 : ℝ) ≤ (734284868367413/2500000000000000000 : ℝ) := by
    have hpowers : (2947/20000 : ℝ)^4349 ≤ (734284868367413/2500000000000000000 : ℝ)^1024 := by
      have hnat : (2947 : ℕ)^4349*2500000000000000000^1024 ≤ 734284868367413^1024*20000^4349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2947 20000 734284868367413 2500000000000000000 4349 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2947/20000 : ℝ)) (X := (734284868367413/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009364599544651647/50000000000000000000 : ℝ) ≤ (5000220479729731/5000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (50009364599544651647/50000000000000000000 : ℝ)^1024 ≤ (5000220479729731/5000000000000000 : ℝ)^4349 := by
      have hnat : (50009364599544651647 : ℕ)^1024*5000000000000000^4349 ≤ 5000220479729731^4349*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009364599544651647 50000000000000000000 5000220479729731 5000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000220479729731/5000000000000000 : ℝ)) (X := (50009364599544651647/50000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038735994279348167/100000000000000000000 : ℝ) ≤ (5000455964427651/5000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (100038735994279348167/100000000000000000000 : ℝ)^1024 ≤ (5000455964427651/5000000000000000 : ℝ)^4349 := by
      have hnat : (100038735994279348167 : ℕ)^1024*5000000000000000^4349 ≤ 5000455964427651^4349*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038735994279348167 100000000000000000000 5000455964427651 5000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000455964427651/5000000000000000 : ℝ)) (X := (100038735994279348167/100000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250734284868367413/1250000000000000000 : ℝ) ≤ (5000691449125571/5000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (1250734284868367413/1250000000000000000 : ℝ)^1024 ≤ (5000691449125571/5000000000000000 : ℝ)^4349 := by
      have hnat : (1250734284868367413 : ℕ)^1024*5000000000000000^4349 ≤ 5000691449125571^4349*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250734284868367413 1250000000000000000 5000691449125571 5000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000691449125571/5000000000000000 : ℝ)) (X := (1250734284868367413/1250000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9364599544651647/100000000000000000000 : ℝ) ≤ ((17380464434561907967/17385000000000000000 : ℝ)+2*(735889681/543281250000 : ℝ)*(5629/50000 : ℝ))^(4349/1024 : ℝ) := by
    rw [show (17380464434561907967/17385000000000000000 : ℝ)+2*(735889681/543281250000 : ℝ)*(5629/50000 : ℝ)=(5000220479729731/5000000000000000 : ℝ) by norm_num, show 1+2*(9364599544651647/100000000000000000000 : ℝ)=(50009364599544651647/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(734284868367413/2500000000000000000 : ℝ)+(9364599544651647/100000000000000000000 : ℝ) ≤ ((17380464434561907967/17385000000000000000 : ℝ)+(735889681/543281250000 : ℝ)*((2947/20000 : ℝ)+(5629/50000 : ℝ)))^(4349/1024 : ℝ) := by
    rw [show (17380464434561907967/17385000000000000000 : ℝ)+(735889681/543281250000 : ℝ)*((2947/20000 : ℝ)+(5629/50000 : ℝ))=(5000455964427651/5000000000000000 : ℝ) by norm_num, show 1+(734284868367413/2500000000000000000 : ℝ)+(9364599544651647/100000000000000000000 : ℝ)=(100038735994279348167/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(734284868367413/2500000000000000000 : ℝ) ≤ ((17380464434561907967/17385000000000000000 : ℝ)+2*(735889681/543281250000 : ℝ)*(2947/20000 : ℝ))^(4349/1024 : ℝ) := by
    rw [show (17380464434561907967/17385000000000000000 : ℝ)+2*(735889681/543281250000 : ℝ)*(2947/20000 : ℝ)=(5000691449125571/5000000000000000 : ℝ) by norm_num, show 1+2*(734284868367413/2500000000000000000 : ℝ)=(1250734284868367413/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17380464434561907967/17385000000000000000 : ℝ)*(X 1 0+X 2 0)+(735889681/543281250000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (2947/20000 : ℝ)) (c := (17380464434561907967/17385000000000000000 : ℝ)) (alpha := (735889681/543281250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17380464434561907967/17385000000000000000 : ℝ)*(X 0 1+X 2 1)+(735889681/543281250000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (2947/20000 : ℝ)) (c := (17380464434561907967/17385000000000000000 : ℝ)) (alpha := (735889681/543281250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17380464434561907967/17385000000000000000 : ℝ)*(X 0 2+X 1 2)+(735889681/543281250000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (2947/20000 : ℝ)) (c := (17380464434561907967/17385000000000000000 : ℝ)) (alpha := (735889681/543281250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-459920923/2500000000 : ℝ)*X 0 0+(1346979601/2500000000 : ℝ)*X 0 1+(1077583667/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285731637/10000000000 : ℝ)*X 1 0+(-3093603/15625000 : ℝ)*X 1 1+(673489841/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285731211/10000000000 : ℝ)*X 2 0+(1346979757/2500000000 : ℝ)*X 2 1+(-1979906089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2230666307/5000000000 : ℝ)*X 0 0+(66319647/156250000 : ℝ)*X 0 1+(4244457959/10000000000 : ℝ)*X 0 2+(2230666307/5000000000 : ℝ)*X 1 0+(66319647/156250000 : ℝ)*X 1 1+(4244457959/10000000000 : ℝ)*X 1 2+(2230666307/5000000000 : ℝ)*X 2 0+(66319647/156250000 : ℝ)*X 2 1+(4244457959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1084751771/5000000000 : ℝ)*X 0 0+(1316472253/2500000000 : ℝ)*X 0 1+(2632943981/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1074254229/2000000000 : ℝ)*X 1 0+(-101459833/500000000 : ℝ)*X 1 1+(2632944329/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2685635289/5000000000 : ℝ)*X 2 0+(5265888991/10000000000 : ℝ)*X 2 1+(-1014598489/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2083061231/5000000000 : ℝ)*X 0 0+(1098002599/2500000000 : ℝ)*X 0 1+(2196005509/5000000000 : ℝ)*X 0 2+(2083061231/5000000000 : ℝ)*X 1 0+(1098002599/2500000000 : ℝ)*X 1 1+(2196005509/5000000000 : ℝ)*X 1 2+(2083061231/5000000000 : ℝ)*X 2 0+(1098002599/2500000000 : ℝ)*X 2 1+(2196005509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1050061407/5000000000 : ℝ)*X 0 0+(207266341/400000000 : ℝ)*X 0 1+(42202463/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275916057/10000000000 : ℝ)*X 1 0+(-1974123579/10000000000 : ℝ)*X 1 1+(2700957459/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2637957833/5000000000 : ℝ)*X 2 0+(1350478791/2500000000 : ℝ)*X 2 1+(-493530943/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4494634017/10000000000 : ℝ)*X 0 0+(4227519333/10000000000 : ℝ)*X 0 1+(4227520141/10000000000 : ℝ)*X 0 2+(4494634017/10000000000 : ℝ)*X 1 0+(4227519333/10000000000 : ℝ)*X 1 1+(4227520141/10000000000 : ℝ)*X 1 2+(4494634017/10000000000 : ℝ)*X 2 0+(4227519333/10000000000 : ℝ)*X 2 1+(4227520141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1909311939/10000000000 : ℝ)*X 0 0+(5470046401/10000000000 : ℝ)*X 0 1+(2627392209/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5379052923/10000000000 : ℝ)*X 1 0+(-1016790219/5000000000 : ℝ)*X 1 1+(5254784373/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((268952647/500000000 : ℝ)*X 2 0+(2627392093/5000000000 : ℝ)*X 2 1+(-406716133/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1034702811/2500000000 : ℝ)*X 0 0+(4405426043/10000000000 : ℝ)*X 0 1+(4405426433/10000000000 : ℝ)*X 0 2+(1034702811/2500000000 : ℝ)*X 1 0+(4405426043/10000000000 : ℝ)*X 1 1+(4405426433/10000000000 : ℝ)*X 1 2+(1034702811/2500000000 : ℝ)*X 2 0+(4405426043/10000000000 : ℝ)*X 2 1+(4405426433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62877/100000 : ℝ) ≤ (-18217963734749873509930359542373/28975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60382633/50000000000000 : ℝ)*(upper0) + (169475813/100000000000000 : ℝ)*(upper3) + (16440209/10000000000000 : ℝ)*(lower4) + (297403525157673/10000000000000 : ℝ)*(major0) + (297403525157673/10000000000000 : ℝ)*(major1) + (297403525157673/10000000000000 : ℝ)*(major2) + (1025055953/12500000000000 : ℝ)*(sp3) + (254385970193401/6250000000000 : ℝ)*(sp4) + (2035065482829183/50000000000000 : ℝ)*(sp5) + (203502283880123/5000000000000 : ℝ)*(sp6) + (29669385358421/1562500000000 : ℝ)*(sp7) + (2186167553/50000000000000 : ℝ)*(sp8) + (48929771157/100000000000000 : ℝ)*(sp13) + (67108913531/50000000000000 : ℝ)*(sp14) + (1898848863386569/100000000000000 : ℝ)*(f.failure) + (2035089947714761/50000000000000 : ℝ)*(f.sum) + (1870693299277/289750000000000000000000000 : ℝ)*base65 + (589100647574193597/57950000000000000000000000000000 : ℝ)*base67 + (752183159392493597/57950000000000000000000000000000 : ℝ)*base69 + (142053242937543597/57950000000000000000000000000000 : ℝ)*base71 + (860082810143/115900000000000000000000000 : ℝ)*base74 + (134223818249143597/57950000000000000000000000000000 : ℝ)*base75 + (476106413214493597/57950000000000000000000000000000 : ℝ)*base77 + (562772586261693597/57950000000000000000000000000000 : ℝ)*base79 + (3371918961749/579500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (10159153/10000000000000000000000 : ℝ)*base90 + (10159153/10000000000000000000000 : ℝ)*base92 + (10159153/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (11807/20000 : ℝ) ≤ (6842487713861292511190240594081/11590000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27870521/100000000000000 : ℝ)*(lower1) + (87812399/100000000000000 : ℝ)*(upper2) + (2856659/4000000000000 : ℝ)*(lower4) + (121773443611819/4000000000000 : ℝ)*(major0) + (121773443611819/4000000000000 : ℝ)*(major1) + (121773443611819/4000000000000 : ℝ)*(major2) + (2062627017674823/50000000000000 : ℝ)*(sp0) + (128913831647151/3125000000000 : ℝ)*(sp1) + (2062620341455407/50000000000000 : ℝ)*(sp2) + (971865585035157/50000000000000 : ℝ)*(sp3) + (16050246107/100000000000000 : ℝ)*(sp5) + (143840353/800000000000 : ℝ)*(sp6) + (3061647191/100000000000000 : ℝ)*(sp7) + (4627605293/100000000000000 : ℝ)*(sp12) + (971867115858753/50000000000000 : ℝ)*(f.failure) + (4125258662954939/100000000000000 : ℝ)*(f.sum) + (18793706557483/3477000000000000000000000000 : ℝ)*base66 + (254162162697653991/23180000000000000000000000000000 : ℝ)*base67 + (342635720608513991/23180000000000000000000000000000 : ℝ)*base69 + (68547007385493991/23180000000000000000000000000000 : ℝ)*base71 + (1048755857203/434625000000000000000000000 : ℝ)*base73 + (167073269875273991/23180000000000000000000000000000 : ℝ)*base75 + (360752476259593991/23180000000000000000000000000000 : ℝ)*base77 + (202521499313453991/23180000000000000000000000000000 : ℝ)*base79 + (1057503464809/869250000000000000000000000 : ℝ)*base82 + (20220439/5000000000000000000000 : ℝ)*base89 + (20220439/5000000000000000000000 : ℝ)*base91 + (20220439/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (80231/100000 : ℝ) ≤ (58118895255842687877663805892899/72437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2834181/10000000000000 : ℝ)*(upper0) + (180433543/100000000000000 : ℝ)*(upper2) + (79639993/100000000000000 : ℝ)*(lower3) + (17695217/50000000000000 : ℝ)*(lower4) + (1677129709647103/50000000000000 : ℝ)*(major0) + (1677129709647103/50000000000000 : ℝ)*(major1) + (1677129709647103/50000000000000 : ℝ)*(major2) + (49264273969/100000000000000 : ℝ)*(sp1) + (320030931/3125000000000 : ℝ)*(sp2) + (5381302683/50000000000000 : ℝ)*(sp4) + (2270075491164641/50000000000000 : ℝ)*(sp8) + (113502812016517/2500000000000 : ℝ)*(sp9) + (567518937993107/12500000000000 : ℝ)*(sp10) + (535403176748977/25000000000000 : ℝ)*(sp11) + (535403176748977/25000000000000 : ℝ)*(f.failure) + (567520218116831/12500000000000 : ℝ)*(f.sum) + (4938356673619/869250000000000000000000000 : ℝ)*base65 + (2348094779964889867/289750000000000000000000000000000 : ℝ)*base67 + (1512777181675389867/289750000000000000000000000000000 : ℝ)*base69 + (730829761094360133/289750000000000000000000000000000 : ℝ)*base72 + (143703201631/173850000000000000000000000 : ℝ)*base74 + (527612366178389867/289750000000000000000000000000000 : ℝ)*base75 + (336054021404389867/289750000000000000000000000000000 : ℝ)*base77 + (1312907528524389867/289750000000000000000000000000000 : ℝ)*base79 + (4447166963777/869250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (9856551/2500000000000000000000 : ℝ)*base89 + (9856551/2500000000000000000000 : ℝ)*base91 + (9856551/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84537/100000 : ℝ) ≤ (-3222886599270438008691234600821/3812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5011837/12500000000000 : ℝ)*(upper3) + (116285613/100000000000000 : ℝ)*(lower4) + (11129521/12500000000000 : ℝ)*(upper5) + (1695646367981503/50000000000000 : ℝ)*(major0) + (1695646367981503/50000000000000 : ℝ)*(major1) + (1695646367981503/50000000000000 : ℝ)*(major2) + (1045136341/50000000000000 : ℝ)*(sp4) + (3563963051/6250000000000 : ℝ)*(sp5) + (216588902447/100000000000000 : ℝ)*(sp6) + (15254572631/25000000000000 : ℝ)*(sp7) + (185820162001721/4000000000000 : ℝ)*(sp12) + (1161362279226723/25000000000000 : ℝ)*(sp13) + (4645289551413261/100000000000000 : ℝ)*(sp14) + (270649569601333/12500000000000 : ℝ)*(sp15) + (541314393775297/25000000000000 : ℝ)*(f.failure) + (4645506140315707/100000000000000 : ℝ)*(f.sum) + (26475486623/183000000000000000000000000 : ℝ)*base66 + (5600964447033607/15250000000000000000000000000000 : ℝ)*base68 + (191533799804716393/15250000000000000000000000000000 : ℝ)*base69 + (45881284690783607/15250000000000000000000000000000 : ℝ)*base72 + (4751502503/714843750000000000000000 : ℝ)*base74 + (73943829122783607/15250000000000000000000000000000 : ℝ)*base76 + (24065886258283607/15250000000000000000000000000000 : ℝ)*base78 + (85812583735533607/15250000000000000000000000000000 : ℝ)*base80 + (1047362981653/183000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (125289/2500000000000000000000 : ℝ)*base90 + (125289/2500000000000000000000 : ℝ)*base92 + (125289/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1390_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2947/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62877/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11807/20000 : ℝ) else (80231/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84537/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1390_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1390_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62877/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11807/20000 : ℝ) else (80231/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84537/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1390_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1390_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1390_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62877/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11807/20000 : ℝ) else (80231/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84537/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1390_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

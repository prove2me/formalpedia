-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1277_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:49.022824+00:00
-- url     : https://prove2.me/submissions/22696acb-c823-48b7-9d13-033e5084cae8

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
theorem support_rectangle_w1277_s9_0 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-525373621/2500000000 : ℝ)*x 0 + (2707980309/5000000000 : ℝ)*x 1 + (2621237289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525373621/2500000000 : ℝ)^4237 ≤ (12782460097057/100000000000000 : ℝ)^3213 := by
    have hnat : (525373621 : ℕ)^4237*100000000000000^3213 ≤ 12782460097057^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525373621 2500000000 12782460097057 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707980309/5000000000 : ℝ)^4237 ≤ (44544745091817/100000000000000 : ℝ)^3213 := by
    have hnat : (2707980309 : ℕ)^4237*100000000000000^3213 ≤ 44544745091817^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707980309 5000000000 44544745091817 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621237289/5000000000 : ℝ)^4237 ≤ (21336397398151/50000000000000 : ℝ)^3213 := by
    have hnat : (2621237289 : ℕ)^4237*50000000000000^3213 ≤ 21336397398151^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621237289 5000000000 21336397398151 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-525373621/2500000000 : ℝ), (2707980309/5000000000 : ℝ), (2621237289/5000000000 : ℝ)] ![(12782460097057/100000000000000 : ℝ), (44544745091817/100000000000000 : ℝ), (21336397398151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-525373621/2500000000 : ℝ)|^4237 ≤ (12782460097057/100000000000000 : ℝ)^3213
        have hw : |(-525373621/2500000000 : ℝ)|=(525373621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707980309/5000000000 : ℝ)|^4237 ≤ (44544745091817/100000000000000 : ℝ)^3213
        have hw : |(2707980309/5000000000 : ℝ)|=(2707980309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621237289/5000000000 : ℝ)|^4237 ≤ (21336397398151/50000000000000 : ℝ)^3213
        have hw : |(2621237289/5000000000 : ℝ)|=(2621237289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s9_1 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674993347/5000000000 : ℝ)*x 0 + (-218994201/1000000000 : ℝ)*x 1 + (1310618621/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674993347/5000000000 : ℝ)^4237 ≤ (10957646552503/25000000000000 : ℝ)^3213 := by
    have hnat : (2674993347 : ℕ)^4237*25000000000000^3213 ≤ 10957646552503^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674993347 5000000000 10957646552503 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218994201/1000000000 : ℝ)^4237 ≤ (84353874901/625000000000 : ℝ)^3213 := by
    have hnat : (218994201 : ℕ)^4237*625000000000^3213 ≤ 84353874901^3213*1000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218994201 1000000000 84353874901 625000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310618621/2500000000 : ℝ)^4237 ≤ (5334099223413/12500000000000 : ℝ)^3213 := by
    have hnat : (1310618621 : ℕ)^4237*12500000000000^3213 ≤ 5334099223413^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310618621 2500000000 5334099223413 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674993347/5000000000 : ℝ), (-218994201/1000000000 : ℝ), (1310618621/2500000000 : ℝ)] ![(10957646552503/25000000000000 : ℝ), (84353874901/625000000000 : ℝ), (5334099223413/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674993347/5000000000 : ℝ)|^4237 ≤ (10957646552503/25000000000000 : ℝ)^3213
        have hw : |(2674993347/5000000000 : ℝ)|=(2674993347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-218994201/1000000000 : ℝ)|^4237 ≤ (84353874901/625000000000 : ℝ)^3213
        have hw : |(-218994201/1000000000 : ℝ)|=(218994201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310618621/2500000000 : ℝ)|^4237 ≤ (5334099223413/12500000000000 : ℝ)^3213
        have hw : |(1310618621/2500000000 : ℝ)|=(1310618621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s9_2 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167187069/312500000 : ℝ)*x 0 + (655309279/1250000000 : ℝ)*x 1 + (-2189942989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167187069/312500000 : ℝ)^4237 ≤ (5478822619927/12500000000000 : ℝ)^3213 := by
    have hnat : (167187069 : ℕ)^4237*12500000000000^3213 ≤ 5478822619927^3213*312500000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167187069 312500000 5478822619927 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655309279/1250000000 : ℝ)^4237 ≤ (42672791082331/100000000000000 : ℝ)^3213 := by
    have hnat : (655309279 : ℕ)^4237*100000000000000^3213 ≤ 42672791082331^3213*1250000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655309279 1250000000 42672791082331 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2189942989/10000000000 : ℝ)^4237 ≤ (539865117627/4000000000000 : ℝ)^3213 := by
    have hnat : (2189942989 : ℕ)^4237*4000000000000^3213 ≤ 539865117627^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189942989 10000000000 539865117627 4000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167187069/312500000 : ℝ), (655309279/1250000000 : ℝ), (-2189942989/10000000000 : ℝ)] ![(5478822619927/12500000000000 : ℝ), (42672791082331/100000000000000 : ℝ), (539865117627/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167187069/312500000 : ℝ)|^4237 ≤ (5478822619927/12500000000000 : ℝ)^3213
        have hw : |(167187069/312500000 : ℝ)|=(167187069/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655309279/1250000000 : ℝ)|^4237 ≤ (42672791082331/100000000000000 : ℝ)^3213
        have hw : |(655309279/1250000000 : ℝ)|=(655309279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2189942989/10000000000 : ℝ)|^4237 ≤ (539865117627/4000000000000 : ℝ)^3213
        have hw : |(-2189942989/10000000000 : ℝ)|=(2189942989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s9_3 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (135747207/312500000 : ℝ)*x 0 + (2085066831/5000000000 : ℝ)*x 1 + (4524650803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135747207/312500000 : ℝ)^4237 ≤ (16651049715009/50000000000000 : ℝ)^3213 := by
    have hnat : (135747207 : ℕ)^4237*50000000000000^3213 ≤ 16651049715009^3213*312500000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135747207 312500000 16651049715009 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085066831/5000000000 : ℝ)^4237 ≤ (3155656872273/10000000000000 : ℝ)^3213 := by
    have hnat : (2085066831 : ℕ)^4237*10000000000000^3213 ≤ 3155656872273^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085066831 5000000000 3155656872273 10000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4524650803/10000000000 : ℝ)^4237 ≤ (17570665914909/50000000000000 : ℝ)^3213 := by
    have hnat : (4524650803 : ℕ)^4237*50000000000000^3213 ≤ 17570665914909^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524650803 10000000000 17570665914909 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135747207/312500000 : ℝ), (2085066831/5000000000 : ℝ), (4524650803/10000000000 : ℝ)] ![(16651049715009/50000000000000 : ℝ), (3155656872273/10000000000000 : ℝ), (17570665914909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135747207/312500000 : ℝ)|^4237 ≤ (16651049715009/50000000000000 : ℝ)^3213
        have hw : |(135747207/312500000 : ℝ)|=(135747207/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085066831/5000000000 : ℝ)|^4237 ≤ (3155656872273/10000000000000 : ℝ)^3213
        have hw : |(2085066831/5000000000 : ℝ)|=(2085066831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4524650803/10000000000 : ℝ)|^4237 ≤ (17570665914909/50000000000000 : ℝ)^3213
        have hw : |(4524650803/10000000000 : ℝ)|=(4524650803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s9_4 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061131103/2000000000 : ℝ)*x 0 + (1083068013/2000000000 : ℝ)*x 1 + (-1008538017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061131103/2000000000 : ℝ)^4237 ≤ (43352279274723/100000000000000 : ℝ)^3213 := by
    have hnat : (1061131103 : ℕ)^4237*100000000000000^3213 ≤ 43352279274723^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061131103 2000000000 43352279274723 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083068013/2000000000 : ℝ)^4237 ≤ (4453801471053/10000000000000 : ℝ)^3213 := by
    have hnat : (1083068013 : ℕ)^4237*10000000000000^3213 ≤ 4453801471053^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083068013 2000000000 4453801471053 10000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1008538017/5000000000 : ℝ)^4237 ≤ (12109706000689/100000000000000 : ℝ)^3213 := by
    have hnat : (1008538017 : ℕ)^4237*100000000000000^3213 ≤ 12109706000689^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008538017 5000000000 12109706000689 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061131103/2000000000 : ℝ), (1083068013/2000000000 : ℝ), (-1008538017/5000000000 : ℝ)] ![(43352279274723/100000000000000 : ℝ), (4453801471053/10000000000000 : ℝ), (12109706000689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061131103/2000000000 : ℝ)|^4237 ≤ (43352279274723/100000000000000 : ℝ)^3213
        have hw : |(1061131103/2000000000 : ℝ)|=(1061131103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083068013/2000000000 : ℝ)|^4237 ≤ (4453801471053/10000000000000 : ℝ)^3213
        have hw : |(1083068013/2000000000 : ℝ)|=(1083068013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1008538017/5000000000 : ℝ)|^4237 ≤ (12109706000689/100000000000000 : ℝ)^3213
        have hw : |(-1008538017/5000000000 : ℝ)|=(1008538017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s9_5 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4343937407/10000000000 : ℝ)*x 0 + (4523387941/10000000000 : ℝ)*x 1 + (4171402541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343937407/10000000000 : ℝ)^4237 ≤ (6660474039701/20000000000000 : ℝ)^3213 := by
    have hnat : (4343937407 : ℕ)^4237*20000000000000^3213 ≤ 6660474039701^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343937407 10000000000 6660474039701 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4523387941/10000000000 : ℝ)^4237 ≤ (2195524893011/6250000000000 : ℝ)^3213 := by
    have hnat : (4523387941 : ℕ)^4237*6250000000000^3213 ≤ 2195524893011^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523387941 10000000000 2195524893011 6250000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4171402541/10000000000 : ℝ)^4237 ≤ (31569231495199/100000000000000 : ℝ)^3213 := by
    have hnat : (4171402541 : ℕ)^4237*100000000000000^3213 ≤ 31569231495199^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171402541 10000000000 31569231495199 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343937407/10000000000 : ℝ), (4523387941/10000000000 : ℝ), (4171402541/10000000000 : ℝ)] ![(6660474039701/20000000000000 : ℝ), (2195524893011/6250000000000 : ℝ), (31569231495199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343937407/10000000000 : ℝ)|^4237 ≤ (6660474039701/20000000000000 : ℝ)^3213
        have hw : |(4343937407/10000000000 : ℝ)|=(4343937407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4523387941/10000000000 : ℝ)|^4237 ≤ (2195524893011/6250000000000 : ℝ)^3213
        have hw : |(4523387941/10000000000 : ℝ)|=(4523387941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4171402541/10000000000 : ℝ)|^4237 ≤ (31569231495199/100000000000000 : ℝ)^3213
        have hw : |(4171402541/10000000000 : ℝ)|=(4171402541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s9_6 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1768354361/2500000000 : ℝ)*x 0 + (280227367/1000000000 : ℝ)*x 1 + (544262273/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1768354361/2500000000 : ℝ)^4237 ≤ (63343980778137/100000000000000 : ℝ)^3213 := by
    have hnat : (1768354361 : ℕ)^4237*100000000000000^3213 ≤ 63343980778137^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768354361 2500000000 63343980778137 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280227367/1000000000 : ℝ)^4237 ≤ (2335281636549/12500000000000 : ℝ)^3213 := by
    have hnat : (280227367 : ℕ)^4237*12500000000000^3213 ≤ 2335281636549^3213*1000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280227367 1000000000 2335281636549 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544262273/2000000000 : ℝ)^4237 ≤ (17973766112219/100000000000000 : ℝ)^3213 := by
    have hnat : (544262273 : ℕ)^4237*100000000000000^3213 ≤ 17973766112219^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544262273 2000000000 17973766112219 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1768354361/2500000000 : ℝ), (280227367/1000000000 : ℝ), (544262273/2000000000 : ℝ)] ![(63343980778137/100000000000000 : ℝ), (2335281636549/12500000000000 : ℝ), (17973766112219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1768354361/2500000000 : ℝ)|^4237 ≤ (63343980778137/100000000000000 : ℝ)^3213
        have hw : |(-1768354361/2500000000 : ℝ)|=(1768354361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280227367/1000000000 : ℝ)|^4237 ≤ (2335281636549/12500000000000 : ℝ)^3213
        have hw : |(280227367/1000000000 : ℝ)|=(280227367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(544262273/2000000000 : ℝ)|^4237 ≤ (17973766112219/100000000000000 : ℝ)^3213
        have hw : |(544262273/2000000000 : ℝ)|=(544262273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s9_7 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4201459047/5000000000 : ℝ)*x 0 + (-182523401/2000000000 : ℝ)*x 1 + (630213487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4201459047/5000000000 : ℝ)^4237 ≤ (39748030989379/50000000000000 : ℝ)^3213 := by
    have hnat : (4201459047 : ℕ)^4237*50000000000000^3213 ≤ 39748030989379^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4201459047 5000000000 39748030989379 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182523401/2000000000 : ℝ)^4237 ≤ (4255269309439/100000000000000 : ℝ)^3213 := by
    have hnat : (182523401 : ℕ)^4237*100000000000000^3213 ≤ 4255269309439^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182523401 2000000000 4255269309439 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (630213487/2500000000 : ℝ)^4237 ≤ (812433434877/5000000000000 : ℝ)^3213 := by
    have hnat : (630213487 : ℕ)^4237*5000000000000^3213 ≤ 812433434877^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      630213487 2500000000 812433434877 5000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4201459047/5000000000 : ℝ), (-182523401/2000000000 : ℝ), (630213487/2500000000 : ℝ)] ![(39748030989379/50000000000000 : ℝ), (4255269309439/100000000000000 : ℝ), (812433434877/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4201459047/5000000000 : ℝ)|^4237 ≤ (39748030989379/50000000000000 : ℝ)^3213
        have hw : |(4201459047/5000000000 : ℝ)|=(4201459047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-182523401/2000000000 : ℝ)|^4237 ≤ (4255269309439/100000000000000 : ℝ)^3213
        have hw : |(-182523401/2000000000 : ℝ)|=(182523401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(630213487/2500000000 : ℝ)|^4237 ≤ (812433434877/5000000000000 : ℝ)^3213
        have hw : |(630213487/2500000000 : ℝ)|=(630213487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s9_8 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66929293/80000000 : ℝ)*x 0 + (2746805329/10000000000 : ℝ)*x 1 + (-164577377/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66929293/80000000 : ℝ)^4237 ≤ (39518910524977/50000000000000 : ℝ)^3213 := by
    have hnat : (66929293 : ℕ)^4237*50000000000000^3213 ≤ 39518910524977^3213*80000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66929293 80000000 39518910524977 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2746805329/10000000000 : ℝ)^4237 ≤ (3639228886113/20000000000000 : ℝ)^3213 := by
    have hnat : (2746805329 : ℕ)^4237*20000000000000^3213 ≤ 3639228886113^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746805329 10000000000 3639228886113 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164577377/2500000000 : ℝ)^4237 ≤ (2766034511491/100000000000000 : ℝ)^3213 := by
    have hnat : (164577377 : ℕ)^4237*100000000000000^3213 ≤ 2766034511491^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164577377 2500000000 2766034511491 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66929293/80000000 : ℝ), (2746805329/10000000000 : ℝ), (-164577377/2500000000 : ℝ)] ![(39518910524977/50000000000000 : ℝ), (3639228886113/20000000000000 : ℝ), (2766034511491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66929293/80000000 : ℝ)|^4237 ≤ (39518910524977/50000000000000 : ℝ)^3213
        have hw : |(66929293/80000000 : ℝ)|=(66929293/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2746805329/10000000000 : ℝ)|^4237 ≤ (3639228886113/20000000000000 : ℝ)^3213
        have hw : |(2746805329/10000000000 : ℝ)|=(2746805329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-164577377/2500000000 : ℝ)|^4237 ≤ (2766034511491/100000000000000 : ℝ)^3213
        have hw : |(-164577377/2500000000 : ℝ)|=(164577377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1277_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14661/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1099/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14661/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14661/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10989/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14661/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10989/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14661/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10989/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14661/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10989/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14661/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10989/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14661/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10989/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10989/100000 : ℝ) ^ (1059/256 : ℝ) ≤ (2156471334147663/20000000000000000000 : ℝ) := by
    have hpowers : (10989/100000 : ℝ)^1059 ≤ (2156471334147663/20000000000000000000 : ℝ)^256 := by
      have hnat : (10989 : ℕ)^1059*20000000000000000000^256 ≤ 2156471334147663^256*100000^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10989 100000 2156471334147663 20000000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10989/100000 : ℝ)) (X := (2156471334147663/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14661/100000 : ℝ) ^ (1059/256 : ℝ) ≤ (8883688307086633/25000000000000000000 : ℝ) := by
    have hpowers : (14661/100000 : ℝ)^1059 ≤ (8883688307086633/25000000000000000000 : ℝ)^256 := by
      have hnat : (14661 : ℕ)^1059*25000000000000000000^256 ≤ 8883688307086633^256*100000^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14661 100000 8883688307086633 25000000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14661/100000 : ℝ)) (X := (8883688307086633/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002156471334147663/10000000000000000000 : ℝ) ≤ (2500130314337083/2500000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (10002156471334147663/10000000000000000000 : ℝ)^256 ≤ (2500130314337083/2500000000000000 : ℝ)^1059 := by
      have hnat : (10002156471334147663 : ℕ)^256*2500000000000000^1059 ≤ 2500130314337083^1059*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002156471334147663 10000000000000000000 2500130314337083 2500000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500130314337083/2500000000000000 : ℝ)) (X := (10002156471334147663/10000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046317109899084847/100000000000000000000 : ℝ) ≤ (1250139932702397/1250000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (100046317109899084847/100000000000000000000 : ℝ)^256 ≤ (1250139932702397/1250000000000000 : ℝ)^1059 := by
      have hnat : (100046317109899084847 : ℕ)^256*1250000000000000^1059 ≤ 1250139932702397^1059*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046317109899084847 100000000000000000000 1250139932702397 1250000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250139932702397/1250000000000000 : ℝ)) (X := (100046317109899084847/100000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508883688307086633/12500000000000000000 : ℝ) ≤ (500085883294501/500000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (12508883688307086633/12500000000000000000 : ℝ)^256 ≤ (500085883294501/500000000000000 : ℝ)^1059 := by
      have hnat : (12508883688307086633 : ℕ)^256*500000000000000^1059 ≤ 500085883294501^1059*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508883688307086633 12500000000000000000 500085883294501 500000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500085883294501/500000000000000 : ℝ)) (X := (12508883688307086633/12500000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2156471334147663/20000000000000000000 : ℝ) ≤ ((169947994090363267/170000000000000000 : ℝ)+2*(149551067711/91800000000000 : ℝ)*(10989/100000 : ℝ))^(1059/256 : ℝ) := by
    rw [show (169947994090363267/170000000000000000 : ℝ)+2*(149551067711/91800000000000 : ℝ)*(10989/100000 : ℝ)=(2500130314337083/2500000000000000 : ℝ) by norm_num, show 1+2*(2156471334147663/20000000000000000000 : ℝ)=(10002156471334147663/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8883688307086633/25000000000000000000 : ℝ)+(2156471334147663/20000000000000000000 : ℝ) ≤ ((169947994090363267/170000000000000000 : ℝ)+(149551067711/91800000000000 : ℝ)*((14661/100000 : ℝ)+(10989/100000 : ℝ)))^(1059/256 : ℝ) := by
    rw [show (169947994090363267/170000000000000000 : ℝ)+(149551067711/91800000000000 : ℝ)*((14661/100000 : ℝ)+(10989/100000 : ℝ))=(1250139932702397/1250000000000000 : ℝ) by norm_num, show 1+(8883688307086633/25000000000000000000 : ℝ)+(2156471334147663/20000000000000000000 : ℝ)=(100046317109899084847/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8883688307086633/25000000000000000000 : ℝ) ≤ ((169947994090363267/170000000000000000 : ℝ)+2*(149551067711/91800000000000 : ℝ)*(14661/100000 : ℝ))^(1059/256 : ℝ) := by
    rw [show (169947994090363267/170000000000000000 : ℝ)+2*(149551067711/91800000000000 : ℝ)*(14661/100000 : ℝ)=(500085883294501/500000000000000 : ℝ) by norm_num, show 1+2*(8883688307086633/25000000000000000000 : ℝ)=(12508883688307086633/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (169947994090363267/170000000000000000 : ℝ)*(X 1 0+X 2 0)+(149551067711/91800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (14661/100000 : ℝ)) (c := (169947994090363267/170000000000000000 : ℝ)) (alpha := (149551067711/91800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (169947994090363267/170000000000000000 : ℝ)*(X 0 1+X 2 1)+(149551067711/91800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (14661/100000 : ℝ)) (c := (169947994090363267/170000000000000000 : ℝ)) (alpha := (149551067711/91800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (169947994090363267/170000000000000000 : ℝ)*(X 0 2+X 1 2)+(149551067711/91800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (14661/100000 : ℝ)) (c := (169947994090363267/170000000000000000 : ℝ)) (alpha := (149551067711/91800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-525373621/2500000000 : ℝ)*X 0 0+(2707980309/5000000000 : ℝ)*X 0 1+(2621237289/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674993347/5000000000 : ℝ)*X 1 0+(-218994201/1000000000 : ℝ)*X 1 1+(1310618621/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167187069/312500000 : ℝ)*X 2 0+(655309279/1250000000 : ℝ)*X 2 1+(-2189942989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((135747207/312500000 : ℝ)*X 0 0+(2085066831/5000000000 : ℝ)*X 0 1+(4524650803/10000000000 : ℝ)*X 0 2+(135747207/312500000 : ℝ)*X 1 0+(2085066831/5000000000 : ℝ)*X 1 1+(4524650803/10000000000 : ℝ)*X 1 2+(135747207/312500000 : ℝ)*X 2 0+(2085066831/5000000000 : ℝ)*X 2 1+(4524650803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1061131103/2000000000 : ℝ)*X 2 0+(1083068013/2000000000 : ℝ)*X 2 1+(-1008538017/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s9_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4343937407/10000000000 : ℝ)*X 0 0+(4523387941/10000000000 : ℝ)*X 0 1+(4171402541/10000000000 : ℝ)*X 0 2+(4343937407/10000000000 : ℝ)*X 1 0+(4523387941/10000000000 : ℝ)*X 1 1+(4171402541/10000000000 : ℝ)*X 1 2+(4343937407/10000000000 : ℝ)*X 2 0+(4523387941/10000000000 : ℝ)*X 2 1+(4171402541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((-1768354361/2500000000 : ℝ)*X 0 0+(280227367/1000000000 : ℝ)*X 0 1+(544262273/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s9_6 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4201459047/5000000000 : ℝ)*X 1 0+(-182523401/2000000000 : ℝ)*X 1 1+(630213487/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s9_7 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((66929293/80000000 : ℝ)*X 2 0+(2746805329/10000000000 : ℝ)*X 2 1+(-164577377/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s9_8 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6444766473929487259646289/8500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44196299/20000000000000 : ℝ)*(lower2) + (9099747/2500000000000 : ℝ)*(lower5) + (4292465156954089/100000000000000 : ℝ)*(major0) + (4292465156954089/100000000000000 : ℝ)*(major1) + (4292465156954089/100000000000000 : ℝ)*(major2) + (5764153293724261/100000000000000 : ℝ)*(sp0) + (5764153543045983/100000000000000 : ℝ)*(sp1) + (230565461533619/4000000000000 : ℝ)*(sp2) + (1410376007291923/50000000000000 : ℝ)*(sp3) + (3778956217/25000000000000 : ℝ)*(sp4) + (24298242943/100000000000000 : ℝ)*(sp5) + (27283341/4000000000000 : ℝ)*(sp6) + (216380901/50000000000000 : ℝ)*(sp7) + (1160821221/50000000000000 : ℝ)*(sp8) + (2820776312826789/100000000000000 : ℝ)*(f.failure) + (1152830795161557/20000000000000 : ℝ)*(f.sum) + (30754622450489/4590000000000000000000000000 : ℝ)*base65 + (9944892630724733399/459000000000000000000000000000000 : ℝ)*base68 + (1623362160136266601/459000000000000000000000000000000 : ℝ)*base69 + (276576223612733399/459000000000000000000000000000000 : ℝ)*base72 + (15541601468971/4590000000000000000000000000 : ℝ)*base74 + (641983495378733399/459000000000000000000000000000000 : ℝ)*base76 + (3087798084067266601/459000000000000000000000000000000 : ℝ)*base77 + (4517956616134733399/459000000000000000000000000000000 : ℝ)*base80 + (17035330948259/4590000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (12909407/2000000000000000000000 : ℝ)*base90 + (12909407/2000000000000000000000 : ℝ)*base92 + (12909407/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1277_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14661/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1099/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14661/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1277_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1277_box_0 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-964438269/5000000000 : ℝ)*x 0 + (5392625807/10000000000 : ℝ)*x 1 + (5392625047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (964438269/5000000000 : ℝ)^4237 ≤ (1427043482343/12500000000000 : ℝ)^3213 := by
    have hnat : (964438269 : ℕ)^4237*12500000000000^3213 ≤ 1427043482343^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964438269 5000000000 1427043482343 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392625807/10000000000 : ℝ)^4237 ≤ (5536478772519/12500000000000 : ℝ)^3213 := by
    have hnat : (5392625807 : ℕ)^4237*12500000000000^3213 ≤ 5536478772519^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392625807 10000000000 5536478772519 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392625047/10000000000 : ℝ)^4237 ≤ (346029858973/781250000000 : ℝ)^3213 := by
    have hnat : (5392625047 : ℕ)^4237*781250000000^3213 ≤ 346029858973^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392625047 10000000000 346029858973 781250000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-964438269/5000000000 : ℝ), (5392625807/10000000000 : ℝ), (5392625047/10000000000 : ℝ)] ![(1427043482343/12500000000000 : ℝ), (5536478772519/12500000000000 : ℝ), (346029858973/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-964438269/5000000000 : ℝ)|^4237 ≤ (1427043482343/12500000000000 : ℝ)^3213
        have hw : |(-964438269/5000000000 : ℝ)|=(964438269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392625807/10000000000 : ℝ)|^4237 ≤ (5536478772519/12500000000000 : ℝ)^3213
        have hw : |(5392625807/10000000000 : ℝ)|=(5392625807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392625047/10000000000 : ℝ)|^4237 ≤ (346029858973/781250000000 : ℝ)^3213
        have hw : |(5392625047/10000000000 : ℝ)|=(5392625047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_box_1 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642044069/5000000000 : ℝ)*x 0 + (-2077222467/10000000000 : ℝ)*x 1 + (5392625719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642044069/5000000000 : ℝ)^4237 ≤ (8624007934059/20000000000000 : ℝ)^3213 := by
    have hnat : (2642044069 : ℕ)^4237*20000000000000^3213 ≤ 8624007934059^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642044069 5000000000 8624007934059 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077222467/10000000000 : ℝ)^4237 ≤ (786758193191/6250000000000 : ℝ)^3213 := by
    have hnat : (2077222467 : ℕ)^4237*6250000000000^3213 ≤ 786758193191^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077222467 10000000000 786758193191 6250000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392625719/10000000000 : ℝ)^4237 ≤ (44291829227019/100000000000000 : ℝ)^3213 := by
    have hnat : (5392625719 : ℕ)^4237*100000000000000^3213 ≤ 44291829227019^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392625719 10000000000 44291829227019 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642044069/5000000000 : ℝ), (-2077222467/10000000000 : ℝ), (5392625719/10000000000 : ℝ)] ![(8624007934059/20000000000000 : ℝ), (786758193191/6250000000000 : ℝ), (44291829227019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642044069/5000000000 : ℝ)|^4237 ≤ (8624007934059/20000000000000 : ℝ)^3213
        have hw : |(2642044069/5000000000 : ℝ)|=(2642044069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2077222467/10000000000 : ℝ)|^4237 ≤ (786758193191/6250000000000 : ℝ)^3213
        have hw : |(-2077222467/10000000000 : ℝ)|=(2077222467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392625719/10000000000 : ℝ)|^4237 ≤ (44291829227019/100000000000000 : ℝ)^3213
        have hw : |(5392625719/10000000000 : ℝ)|=(5392625719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_box_2 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5284088041/10000000000 : ℝ)*x 0 + (5392625937/10000000000 : ℝ)*x 1 + (-1038611151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284088041/10000000000 : ℝ)^4237 ≤ (10780009656617/25000000000000 : ℝ)^3213 := by
    have hnat : (5284088041 : ℕ)^4237*25000000000000^3213 ≤ 10780009656617^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284088041 10000000000 10780009656617 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392625937/10000000000 : ℝ)^4237 ≤ (4429183158819/10000000000000 : ℝ)^3213 := by
    have hnat : (5392625937 : ℕ)^4237*10000000000000^3213 ≤ 4429183158819^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392625937 10000000000 4429183158819 10000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038611151/5000000000 : ℝ)^4237 ≤ (2517625954493/20000000000000 : ℝ)^3213 := by
    have hnat : (1038611151 : ℕ)^4237*20000000000000^3213 ≤ 2517625954493^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038611151 5000000000 2517625954493 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284088041/10000000000 : ℝ), (5392625937/10000000000 : ℝ), (-1038611151/5000000000 : ℝ)] ![(10780009656617/25000000000000 : ℝ), (4429183158819/10000000000000 : ℝ), (2517625954493/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284088041/10000000000 : ℝ)|^4237 ≤ (10780009656617/25000000000000 : ℝ)^3213
        have hw : |(5284088041/10000000000 : ℝ)|=(5284088041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392625937/10000000000 : ℝ)|^4237 ≤ (4429183158819/10000000000000 : ℝ)^3213
        have hw : |(5392625937/10000000000 : ℝ)|=(5392625937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1038611151/5000000000 : ℝ)|^4237 ≤ (2517625954493/20000000000000 : ℝ)^3213
        have hw : |(-1038611151/5000000000 : ℝ)|=(1038611151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_box_3 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (898745033/2000000000 : ℝ)*x 0 + (4273043711/10000000000 : ℝ)*x 1 + (854608931/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (898745033/2000000000 : ℝ)^4237 ≤ (8706234948407/25000000000000 : ℝ)^3213 := by
    have hnat : (898745033 : ℕ)^4237*25000000000000^3213 ≤ 8706234948407^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898745033 2000000000 8706234948407 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4273043711/10000000000 : ℝ)^4237 ≤ (32587525346783/100000000000000 : ℝ)^3213 := by
    have hnat : (4273043711 : ℕ)^4237*100000000000000^3213 ≤ 32587525346783^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273043711 10000000000 32587525346783 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (854608931/2000000000 : ℝ)^4237 ≤ (16293767420223/50000000000000 : ℝ)^3213 := by
    have hnat : (854608931 : ℕ)^4237*50000000000000^3213 ≤ 16293767420223^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854608931 2000000000 16293767420223 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(898745033/2000000000 : ℝ), (4273043711/10000000000 : ℝ), (854608931/2000000000 : ℝ)] ![(8706234948407/25000000000000 : ℝ), (32587525346783/100000000000000 : ℝ), (16293767420223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(898745033/2000000000 : ℝ)|^4237 ≤ (8706234948407/25000000000000 : ℝ)^3213
        have hw : |(898745033/2000000000 : ℝ)|=(898745033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4273043711/10000000000 : ℝ)|^4237 ≤ (32587525346783/100000000000000 : ℝ)^3213
        have hw : |(4273043711/10000000000 : ℝ)|=(4273043711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(854608931/2000000000 : ℝ)|^4237 ≤ (16293767420223/50000000000000 : ℝ)^3213
        have hw : |(854608931/2000000000 : ℝ)|=(854608931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_box_4 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2276869757/10000000000 : ℝ)*x 0 + (657909677/1250000000 : ℝ)*x 1 + (1315819471/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2276869757/10000000000 : ℝ)^4237 ≤ (22732043139/160000000000 : ℝ)^3213 := by
    have hnat : (2276869757 : ℕ)^4237*160000000000^3213 ≤ 22732043139^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276869757 10000000000 22732043139 160000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657909677/1250000000 : ℝ)^4237 ≤ (343169871957/800000000000 : ℝ)^3213 := by
    have hnat : (657909677 : ℕ)^4237*800000000000^3213 ≤ 343169871957^3213*1250000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657909677 1250000000 343169871957 800000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315819471/2500000000 : ℝ)^4237 ≤ (10724059756123/25000000000000 : ℝ)^3213 := by
    have hnat : (1315819471 : ℕ)^4237*25000000000000^3213 ≤ 10724059756123^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315819471 2500000000 10724059756123 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2276869757/10000000000 : ℝ), (657909677/1250000000 : ℝ), (1315819471/2500000000 : ℝ)] ![(22732043139/160000000000 : ℝ), (343169871957/800000000000 : ℝ), (10724059756123/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2276869757/10000000000 : ℝ)|^4237 ≤ (22732043139/160000000000 : ℝ)^3213
        have hw : |(-2276869757/10000000000 : ℝ)|=(2276869757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657909677/1250000000 : ℝ)|^4237 ≤ (343169871957/800000000000 : ℝ)^3213
        have hw : |(657909677/1250000000 : ℝ)|=(657909677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315819471/2500000000 : ℝ)|^4237 ≤ (10724059756123/25000000000000 : ℝ)^3213
        have hw : |(1315819471/2500000000 : ℝ)|=(1315819471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_box_5 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075038591/2000000000 : ℝ)*x 0 + (-425728177/2000000000 : ℝ)*x 1 + (5263277769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075038591/2000000000 : ℝ)^4237 ≤ (8820622240411/20000000000000 : ℝ)^3213 := by
    have hnat : (1075038591 : ℕ)^4237*20000000000000^3213 ≤ 8820622240411^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075038591 2000000000 8820622240411 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425728177/2000000000 : ℝ)^4237 ≤ (3250162750983/25000000000000 : ℝ)^3213 := by
    have hnat : (425728177 : ℕ)^4237*25000000000000^3213 ≤ 3250162750983^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425728177 2000000000 3250162750983 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263277769/10000000000 : ℝ)^4237 ≤ (1072405944713/2500000000000 : ℝ)^3213 := by
    have hnat : (5263277769 : ℕ)^4237*2500000000000^3213 ≤ 1072405944713^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263277769 10000000000 1072405944713 2500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075038591/2000000000 : ℝ), (-425728177/2000000000 : ℝ), (5263277769/10000000000 : ℝ)] ![(8820622240411/20000000000000 : ℝ), (3250162750983/25000000000000 : ℝ), (1072405944713/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075038591/2000000000 : ℝ)|^4237 ≤ (8820622240411/20000000000000 : ℝ)^3213
        have hw : |(1075038591/2000000000 : ℝ)|=(1075038591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-425728177/2000000000 : ℝ)|^4237 ≤ (3250162750983/25000000000000 : ℝ)^3213
        have hw : |(-425728177/2000000000 : ℝ)|=(425728177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263277769/10000000000 : ℝ)|^4237 ≤ (1072405944713/2500000000000 : ℝ)^3213
        have hw : |(5263277769/10000000000 : ℝ)|=(5263277769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_box_6 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375193401/10000000000 : ℝ)*x 0 + (5263277389/10000000000 : ℝ)*x 1 + (-266080099/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375193401/10000000000 : ℝ)^4237 ≤ (22051558013863/50000000000000 : ℝ)^3213 := by
    have hnat : (5375193401 : ℕ)^4237*50000000000000^3213 ≤ 22051558013863^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375193401 10000000000 22051558013863 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263277389/10000000000 : ℝ)^4237 ≤ (1072405842611/2500000000000 : ℝ)^3213 := by
    have hnat : (5263277389 : ℕ)^4237*2500000000000^3213 ≤ 1072405842611^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263277389 10000000000 1072405842611 2500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266080099/1250000000 : ℝ)^4237 ≤ (203135160233/1562500000000 : ℝ)^3213 := by
    have hnat : (266080099 : ℕ)^4237*1562500000000^3213 ≤ 203135160233^3213*1250000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266080099 1250000000 203135160233 1562500000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375193401/10000000000 : ℝ), (5263277389/10000000000 : ℝ), (-266080099/1250000000 : ℝ)] ![(22051558013863/50000000000000 : ℝ), (1072405842611/2500000000000 : ℝ), (203135160233/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375193401/10000000000 : ℝ)|^4237 ≤ (22051558013863/50000000000000 : ℝ)^3213
        have hw : |(5375193401/10000000000 : ℝ)|=(5375193401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263277389/10000000000 : ℝ)|^4237 ≤ (1072405842611/2500000000000 : ℝ)^3213
        have hw : |(5263277389/10000000000 : ℝ)|=(5263277389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-266080099/1250000000 : ℝ)|^4237 ≤ (203135160233/1562500000000 : ℝ)^3213
        have hw : |(-266080099/1250000000 : ℝ)|=(266080099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_box_7 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1048317069/2500000000 : ℝ)*x 0 + (276451057/625000000 : ℝ)*x 1 + (884643299/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048317069/2500000000 : ℝ)^4237 ≤ (15893816571433/50000000000000 : ℝ)^3213 := by
    have hnat : (1048317069 : ℕ)^4237*50000000000000^3213 ≤ 15893816571433^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048317069 2500000000 15893816571433 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276451057/625000000 : ℝ)^4237 ≤ (34106185541551/100000000000000 : ℝ)^3213 := by
    have hnat : (276451057 : ℕ)^4237*100000000000000^3213 ≤ 34106185541551^3213*625000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276451057 625000000 34106185541551 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (884643299/2000000000 : ℝ)^4237 ≤ (1364247252057/4000000000000 : ℝ)^3213 := by
    have hnat : (884643299 : ℕ)^4237*4000000000000^3213 ≤ 1364247252057^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884643299 2000000000 1364247252057 4000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048317069/2500000000 : ℝ), (276451057/625000000 : ℝ), (884643299/2000000000 : ℝ)] ![(15893816571433/50000000000000 : ℝ), (34106185541551/100000000000000 : ℝ), (1364247252057/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048317069/2500000000 : ℝ)|^4237 ≤ (15893816571433/50000000000000 : ℝ)^3213
        have hw : |(1048317069/2500000000 : ℝ)|=(1048317069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(276451057/625000000 : ℝ)|^4237 ≤ (34106185541551/100000000000000 : ℝ)^3213
        have hw : |(276451057/625000000 : ℝ)|=(276451057/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(884643299/2000000000 : ℝ)|^4237 ≤ (1364247252057/4000000000000 : ℝ)^3213
        have hw : |(884643299/2000000000 : ℝ)|=(884643299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_box_8 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-440795821/2000000000 : ℝ)*x 0 + (5174549701/10000000000 : ℝ)*x 1 + (1081333581/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (440795821/2000000000 : ℝ)^4237 ≤ (1701352300989/12500000000000 : ℝ)^3213 := by
    have hnat : (440795821 : ℕ)^4237*12500000000000^3213 ≤ 1701352300989^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440795821 2000000000 1701352300989 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174549701/10000000000 : ℝ)^4237 ≤ (41945197476091/100000000000000 : ℝ)^3213 := by
    have hnat : (5174549701 : ℕ)^4237*100000000000000^3213 ≤ 41945197476091^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174549701 10000000000 41945197476091 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081333581/2000000000 : ℝ)^4237 ≤ (44443984099259/100000000000000 : ℝ)^3213 := by
    have hnat : (1081333581 : ℕ)^4237*100000000000000^3213 ≤ 44443984099259^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081333581 2000000000 44443984099259 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-440795821/2000000000 : ℝ), (5174549701/10000000000 : ℝ), (1081333581/2000000000 : ℝ)] ![(1701352300989/12500000000000 : ℝ), (41945197476091/100000000000000 : ℝ), (44443984099259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-440795821/2000000000 : ℝ)|^4237 ≤ (1701352300989/12500000000000 : ℝ)^3213
        have hw : |(-440795821/2000000000 : ℝ)|=(440795821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174549701/10000000000 : ℝ)|^4237 ≤ (41945197476091/100000000000000 : ℝ)^3213
        have hw : |(5174549701/10000000000 : ℝ)|=(5174549701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081333581/2000000000 : ℝ)|^4237 ≤ (44443984099259/100000000000000 : ℝ)^3213
        have hw : |(1081333581/2000000000 : ℝ)|=(1081333581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_box_9 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26370959/50000000 : ℝ)*x 0 + (-258937963/1250000000 : ℝ)*x 1 + (2703333493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26370959/50000000 : ℝ)^4237 ≤ (43013575942299/100000000000000 : ℝ)^3213 := by
    have hnat : (26370959 : ℕ)^4237*100000000000000^3213 ≤ 43013575942299^3213*50000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26370959 50000000 43013575942299 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258937963/1250000000 : ℝ)^4237 ≤ (627122495141/5000000000000 : ℝ)^3213 := by
    have hnat : (258937963 : ℕ)^4237*5000000000000^3213 ≤ 627122495141^3213*1250000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258937963 1250000000 627122495141 5000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703333493/5000000000 : ℝ)^4237 ≤ (44443974137259/100000000000000 : ℝ)^3213 := by
    have hnat : (2703333493 : ℕ)^4237*100000000000000^3213 ≤ 44443974137259^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703333493 5000000000 44443974137259 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26370959/50000000 : ℝ), (-258937963/1250000000 : ℝ), (2703333493/5000000000 : ℝ)] ![(43013575942299/100000000000000 : ℝ), (627122495141/5000000000000 : ℝ), (44443974137259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26370959/50000000 : ℝ)|^4237 ≤ (43013575942299/100000000000000 : ℝ)^3213
        have hw : |(26370959/50000000 : ℝ)|=(26370959/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-258937963/1250000000 : ℝ)|^4237 ≤ (627122495141/5000000000000 : ℝ)^3213
        have hw : |(-258937963/1250000000 : ℝ)|=(258937963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703333493/5000000000 : ℝ)|^4237 ≤ (44443974137259/100000000000000 : ℝ)^3213
        have hw : |(2703333493/5000000000 : ℝ)|=(2703333493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_box_10 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637096031/5000000000 : ℝ)*x 0 + (5406666629/10000000000 : ℝ)*x 1 + (-517875959/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637096031/5000000000 : ℝ)^4237 ≤ (5376697345003/12500000000000 : ℝ)^3213 := by
    have hnat : (2637096031 : ℕ)^4237*12500000000000^3213 ≤ 5376697345003^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637096031 5000000000 5376697345003 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406666629/10000000000 : ℝ)^4237 ≤ (11110992566841/25000000000000 : ℝ)^3213 := by
    have hnat : (5406666629 : ℕ)^4237*25000000000000^3213 ≤ 11110992566841^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406666629 10000000000 11110992566841 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517875959/2500000000 : ℝ)^4237 ≤ (6271225478383/50000000000000 : ℝ)^3213 := by
    have hnat : (517875959 : ℕ)^4237*50000000000000^3213 ≤ 6271225478383^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517875959 2500000000 6271225478383 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637096031/5000000000 : ℝ), (5406666629/10000000000 : ℝ), (-517875959/2500000000 : ℝ)] ![(5376697345003/12500000000000 : ℝ), (11110992566841/25000000000000 : ℝ), (6271225478383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637096031/5000000000 : ℝ)|^4237 ≤ (5376697345003/12500000000000 : ℝ)^3213
        have hw : |(2637096031/5000000000 : ℝ)|=(2637096031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406666629/10000000000 : ℝ)|^4237 ≤ (11110992566841/25000000000000 : ℝ)^3213
        have hw : |(5406666629/10000000000 : ℝ)|=(5406666629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-517875959/2500000000 : ℝ)|^4237 ≤ (6271225478383/50000000000000 : ℝ)^3213
        have hw : |(-517875959/2500000000 : ℝ)|=(517875959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_box_11 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1131445401/2500000000 : ℝ)*x 0 + (2128364429/5000000000 : ℝ)*x 1 + (4256727617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1131445401/2500000000 : ℝ)^4237 ≤ (35152913851307/100000000000000 : ℝ)^3213 := by
    have hnat : (1131445401 : ℕ)^4237*100000000000000^3213 ≤ 35152913851307^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131445401 2500000000 35152913851307 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2128364429/5000000000 : ℝ)^4237 ≤ (4052943662803/12500000000000 : ℝ)^3213 := by
    have hnat : (2128364429 : ℕ)^4237*12500000000000^3213 ≤ 4052943662803^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128364429 5000000000 4052943662803 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4256727617/10000000000 : ℝ)^4237 ≤ (16211768418543/50000000000000 : ℝ)^3213 := by
    have hnat : (4256727617 : ℕ)^4237*50000000000000^3213 ≤ 16211768418543^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256727617 10000000000 16211768418543 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1131445401/2500000000 : ℝ), (2128364429/5000000000 : ℝ), (4256727617/10000000000 : ℝ)] ![(35152913851307/100000000000000 : ℝ), (4052943662803/12500000000000 : ℝ), (16211768418543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1131445401/2500000000 : ℝ)|^4237 ≤ (35152913851307/100000000000000 : ℝ)^3213
        have hw : |(1131445401/2500000000 : ℝ)|=(1131445401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2128364429/5000000000 : ℝ)|^4237 ≤ (4052943662803/12500000000000 : ℝ)^3213
        have hw : |(2128364429/5000000000 : ℝ)|=(2128364429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4256727617/10000000000 : ℝ)|^4237 ≤ (16211768418543/50000000000000 : ℝ)^3213
        have hw : |(4256727617/10000000000 : ℝ)|=(4256727617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_box_12 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1001118933/5000000000 : ℝ)*x 0 + (2739496041/5000000000 : ℝ)*x 1 + (210090843/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1001118933/5000000000 : ℝ)^4237 ≤ (11992370588973/100000000000000 : ℝ)^3213 := by
    have hnat : (1001118933 : ℕ)^4237*100000000000000^3213 ≤ 11992370588973^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001118933 5000000000 11992370588973 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2739496041/5000000000 : ℝ)^4237 ≤ (45229647476523/100000000000000 : ℝ)^3213 := by
    have hnat : (2739496041 : ℕ)^4237*100000000000000^3213 ≤ 45229647476523^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739496041 5000000000 45229647476523 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210090843/400000000 : ℝ)^4237 ≤ (42777981913311/100000000000000 : ℝ)^3213 := by
    have hnat : (210090843 : ℕ)^4237*100000000000000^3213 ≤ 42777981913311^3213*400000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210090843 400000000 42777981913311 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1001118933/5000000000 : ℝ), (2739496041/5000000000 : ℝ), (210090843/400000000 : ℝ)] ![(11992370588973/100000000000000 : ℝ), (45229647476523/100000000000000 : ℝ), (42777981913311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1001118933/5000000000 : ℝ)|^4237 ≤ (11992370588973/100000000000000 : ℝ)^3213
        have hw : |(-1001118933/5000000000 : ℝ)|=(1001118933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2739496041/5000000000 : ℝ)|^4237 ≤ (45229647476523/100000000000000 : ℝ)^3213
        have hw : |(2739496041/5000000000 : ℝ)|=(2739496041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210090843/400000000 : ℝ)|^4237 ≤ (42777981913311/100000000000000 : ℝ)^3213
        have hw : |(210090843/400000000 : ℝ)|=(210090843/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_box_13 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538294237/1000000000 : ℝ)*x 0 + (-426581841/2000000000 : ℝ)*x 1 + (2626135577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538294237/1000000000 : ℝ)^4237 ≤ (44186978288551/100000000000000 : ℝ)^3213 := by
    have hnat : (538294237 : ℕ)^4237*100000000000000^3213 ≤ 44186978288551^3213*1000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538294237 1000000000 44186978288551 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (426581841/2000000000 : ℝ)^4237 ≤ (13035038938841/100000000000000 : ℝ)^3213 := by
    have hnat : (426581841 : ℕ)^4237*100000000000000^3213 ≤ 13035038938841^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426581841 2000000000 13035038938841 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626135577/5000000000 : ℝ)^4237 ≤ (10694495690451/25000000000000 : ℝ)^3213 := by
    have hnat : (2626135577 : ℕ)^4237*25000000000000^3213 ≤ 10694495690451^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626135577 5000000000 10694495690451 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538294237/1000000000 : ℝ), (-426581841/2000000000 : ℝ), (2626135577/5000000000 : ℝ)] ![(44186978288551/100000000000000 : ℝ), (13035038938841/100000000000000 : ℝ), (10694495690451/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538294237/1000000000 : ℝ)|^4237 ≤ (44186978288551/100000000000000 : ℝ)^3213
        have hw : |(538294237/1000000000 : ℝ)|=(538294237/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-426581841/2000000000 : ℝ)|^4237 ≤ (13035038938841/100000000000000 : ℝ)^3213
        have hw : |(-426581841/2000000000 : ℝ)|=(426581841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626135577/5000000000 : ℝ)|^4237 ≤ (10694495690451/25000000000000 : ℝ)^3213
        have hw : |(2626135577/5000000000 : ℝ)|=(2626135577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_box_14 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134573559/250000000 : ℝ)*x 0 + (525227113/1000000000 : ℝ)*x 1 + (-8531637/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134573559/250000000 : ℝ)^4237 ≤ (44186978180303/100000000000000 : ℝ)^3213 := by
    have hnat : (134573559 : ℕ)^4237*100000000000000^3213 ≤ 44186978180303^3213*250000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134573559 250000000 44186978180303 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525227113/1000000000 : ℝ)^4237 ≤ (21388991252017/50000000000000 : ℝ)^3213 := by
    have hnat : (525227113 : ℕ)^4237*50000000000000^3213 ≤ 21388991252017^3213*1000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525227113 1000000000 21388991252017 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8531637/40000000 : ℝ)^4237 ≤ (6517519650751/50000000000000 : ℝ)^3213 := by
    have hnat : (8531637 : ℕ)^4237*50000000000000^3213 ≤ 6517519650751^3213*40000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8531637 40000000 6517519650751 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134573559/250000000 : ℝ), (525227113/1000000000 : ℝ), (-8531637/40000000 : ℝ)] ![(44186978180303/100000000000000 : ℝ), (21388991252017/50000000000000 : ℝ), (6517519650751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134573559/250000000 : ℝ)|^4237 ≤ (44186978180303/100000000000000 : ℝ)^3213
        have hw : |(134573559/250000000 : ℝ)|=(134573559/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525227113/1000000000 : ℝ)|^4237 ≤ (21388991252017/50000000000000 : ℝ)^3213
        have hw : |(525227113/1000000000 : ℝ)|=(525227113/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8531637/40000000 : ℝ)|^4237 ≤ (6517519650751/50000000000000 : ℝ)^3213
        have hw : |(-8531637/40000000 : ℝ)|=(8531637/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_box_15 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4167255353/10000000000 : ℝ)*x 0 + (554498139/1250000000 : ℝ)*x 1 + (887197061/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4167255353/10000000000 : ℝ)^4237 ≤ (6305569840563/20000000000000 : ℝ)^3213 := by
    have hnat : (4167255353 : ℕ)^4237*20000000000000^3213 ≤ 6305569840563^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167255353 10000000000 6305569840563 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554498139/1250000000 : ℝ)^4237 ≤ (34236074407091/100000000000000 : ℝ)^3213 := by
    have hnat : (554498139 : ℕ)^4237*100000000000000^3213 ≤ 34236074407091^3213*1250000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554498139 1250000000 34236074407091 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (887197061/2000000000 : ℝ)^4237 ≤ (34236076371351/100000000000000 : ℝ)^3213 := by
    have hnat : (887197061 : ℕ)^4237*100000000000000^3213 ≤ 34236076371351^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887197061 2000000000 34236076371351 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4167255353/10000000000 : ℝ), (554498139/1250000000 : ℝ), (887197061/2000000000 : ℝ)] ![(6305569840563/20000000000000 : ℝ), (34236074407091/100000000000000 : ℝ), (34236076371351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4167255353/10000000000 : ℝ)|^4237 ≤ (6305569840563/20000000000000 : ℝ)^3213
        have hw : |(4167255353/10000000000 : ℝ)|=(4167255353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(554498139/1250000000 : ℝ)|^4237 ≤ (34236074407091/100000000000000 : ℝ)^3213
        have hw : |(554498139/1250000000 : ℝ)|=(554498139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(887197061/2000000000 : ℝ)|^4237 ≤ (34236076371351/100000000000000 : ℝ)^3213
        have hw : |(887197061/2000000000 : ℝ)|=(887197061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1277_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14661/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1099/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15709/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58817/100000 : ℝ) ∧ (15913/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (16819/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14661/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1099/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14661/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1099/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14661/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1099/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14661/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1099/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14661/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1099/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14661/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1099/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1099/10000 : ℝ) ^ (1059/256 : ℝ) ≤ (431456647185459/4000000000000000000 : ℝ) := by
    have hpowers : (1099/10000 : ℝ)^1059 ≤ (431456647185459/4000000000000000000 : ℝ)^256 := by
      have hnat : (1099 : ℕ)^1059*4000000000000000000^256 ≤ 431456647185459^256*10000^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1099 10000 431456647185459 4000000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1099/10000 : ℝ)) (X := (431456647185459/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14661/100000 : ℝ) ^ (1059/256 : ℝ) ≤ (8883688307086633/25000000000000000000 : ℝ) := by
    have hpowers : (14661/100000 : ℝ)^1059 ≤ (8883688307086633/25000000000000000000 : ℝ)^256 := by
      have hnat : (14661 : ℕ)^1059*25000000000000000000^256 ≤ 8883688307086633^256*100000^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14661 100000 8883688307086633 25000000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14661/100000 : ℝ)) (X := (8883688307086633/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000431456647185459/2000000000000000000 : ℝ) ≤ (1250065181697917/1250000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (2000431456647185459/2000000000000000000 : ℝ)^256 ≤ (1250065181697917/1250000000000000 : ℝ)^1059 := by
      have hnat : (2000431456647185459 : ℕ)^256*1250000000000000^1059 ≤ 1250065181697917^1059*2000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000431456647185459 2000000000000000000 1250065181697917 1250000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250065181697917/1250000000000000 : ℝ)) (X := (2000431456647185459/2000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046321169407983007/100000000000000000000 : ℝ) ≤ (10001119559718271/10000000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (100046321169407983007/100000000000000000000 : ℝ)^256 ≤ (10001119559718271/10000000000000000 : ℝ)^1059 := by
      have hnat : (100046321169407983007 : ℕ)^256*10000000000000000^1059 ≤ 10001119559718271^1059*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046321169407983007 100000000000000000000 10001119559718271 10000000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001119559718271/10000000000000000 : ℝ)) (X := (100046321169407983007/100000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508883688307086633/12500000000000000000 : ℝ) ≤ (5000858832926603/5000000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (12508883688307086633/12500000000000000000 : ℝ)^256 ≤ (5000858832926603/5000000000000000 : ℝ)^1059 := by
      have hnat : (12508883688307086633 : ℕ)^256*5000000000000000^1059 ≤ 5000858832926603^1059*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508883688307086633 12500000000000000000 5000858832926603 5000000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000858832926603/5000000000000000 : ℝ)) (X := (12508883688307086633/12500000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(431456647185459/4000000000000000000 : ℝ) ≤ ((9174691970814638789/9177500000000000000 : ℝ)+2*(119621226987/73420000000000 : ℝ)*(1099/10000 : ℝ))^(1059/256 : ℝ) := by
    rw [show (9174691970814638789/9177500000000000000 : ℝ)+2*(119621226987/73420000000000 : ℝ)*(1099/10000 : ℝ)=(1250065181697917/1250000000000000 : ℝ) by norm_num, show 1+2*(431456647185459/4000000000000000000 : ℝ)=(2000431456647185459/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8883688307086633/25000000000000000000 : ℝ)+(431456647185459/4000000000000000000 : ℝ) ≤ ((9174691970814638789/9177500000000000000 : ℝ)+(119621226987/73420000000000 : ℝ)*((14661/100000 : ℝ)+(1099/10000 : ℝ)))^(1059/256 : ℝ) := by
    rw [show (9174691970814638789/9177500000000000000 : ℝ)+(119621226987/73420000000000 : ℝ)*((14661/100000 : ℝ)+(1099/10000 : ℝ))=(10001119559718271/10000000000000000 : ℝ) by norm_num, show 1+(8883688307086633/25000000000000000000 : ℝ)+(431456647185459/4000000000000000000 : ℝ)=(100046321169407983007/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8883688307086633/25000000000000000000 : ℝ) ≤ ((9174691970814638789/9177500000000000000 : ℝ)+2*(119621226987/73420000000000 : ℝ)*(14661/100000 : ℝ))^(1059/256 : ℝ) := by
    rw [show (9174691970814638789/9177500000000000000 : ℝ)+2*(119621226987/73420000000000 : ℝ)*(14661/100000 : ℝ)=(5000858832926603/5000000000000000 : ℝ) by norm_num, show 1+2*(8883688307086633/25000000000000000000 : ℝ)=(12508883688307086633/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9174691970814638789/9177500000000000000 : ℝ)*(X 1 0+X 2 0)+(119621226987/73420000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (1099/10000 : ℝ)) (hi := (14661/100000 : ℝ)) (c := (9174691970814638789/9177500000000000000 : ℝ)) (alpha := (119621226987/73420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9174691970814638789/9177500000000000000 : ℝ)*(X 0 1+X 2 1)+(119621226987/73420000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (1099/10000 : ℝ)) (hi := (14661/100000 : ℝ)) (c := (9174691970814638789/9177500000000000000 : ℝ)) (alpha := (119621226987/73420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9174691970814638789/9177500000000000000 : ℝ)*(X 0 2+X 1 2)+(119621226987/73420000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (1099/10000 : ℝ)) (hi := (14661/100000 : ℝ)) (c := (9174691970814638789/9177500000000000000 : ℝ)) (alpha := (119621226987/73420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-964438269/5000000000 : ℝ)*X 0 0+(5392625807/10000000000 : ℝ)*X 0 1+(5392625047/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642044069/5000000000 : ℝ)*X 1 0+(-2077222467/10000000000 : ℝ)*X 1 1+(5392625719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5284088041/10000000000 : ℝ)*X 2 0+(5392625937/10000000000 : ℝ)*X 2 1+(-1038611151/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((898745033/2000000000 : ℝ)*X 0 0+(4273043711/10000000000 : ℝ)*X 0 1+(854608931/2000000000 : ℝ)*X 0 2+(898745033/2000000000 : ℝ)*X 1 0+(4273043711/10000000000 : ℝ)*X 1 1+(854608931/2000000000 : ℝ)*X 1 2+(898745033/2000000000 : ℝ)*X 2 0+(4273043711/10000000000 : ℝ)*X 2 1+(854608931/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2276869757/10000000000 : ℝ)*X 0 0+(657909677/1250000000 : ℝ)*X 0 1+(1315819471/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1075038591/2000000000 : ℝ)*X 1 0+(-425728177/2000000000 : ℝ)*X 1 1+(5263277769/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5375193401/10000000000 : ℝ)*X 2 0+(5263277389/10000000000 : ℝ)*X 2 1+(-266080099/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1048317069/2500000000 : ℝ)*X 0 0+(276451057/625000000 : ℝ)*X 0 1+(884643299/2000000000 : ℝ)*X 0 2+(1048317069/2500000000 : ℝ)*X 1 0+(276451057/625000000 : ℝ)*X 1 1+(884643299/2000000000 : ℝ)*X 1 2+(1048317069/2500000000 : ℝ)*X 2 0+(276451057/625000000 : ℝ)*X 2 1+(884643299/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-440795821/2000000000 : ℝ)*X 0 0+(5174549701/10000000000 : ℝ)*X 0 1+(1081333581/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((26370959/50000000 : ℝ)*X 1 0+(-258937963/1250000000 : ℝ)*X 1 1+(2703333493/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2637096031/5000000000 : ℝ)*X 2 0+(5406666629/10000000000 : ℝ)*X 2 1+(-517875959/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1131445401/2500000000 : ℝ)*X 0 0+(2128364429/5000000000 : ℝ)*X 0 1+(4256727617/10000000000 : ℝ)*X 0 2+(1131445401/2500000000 : ℝ)*X 1 0+(2128364429/5000000000 : ℝ)*X 1 1+(4256727617/10000000000 : ℝ)*X 1 2+(1131445401/2500000000 : ℝ)*X 2 0+(2128364429/5000000000 : ℝ)*X 2 1+(4256727617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1001118933/5000000000 : ℝ)*X 0 0+(2739496041/5000000000 : ℝ)*X 0 1+(210090843/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((538294237/1000000000 : ℝ)*X 1 0+(-426581841/2000000000 : ℝ)*X 1 1+(2626135577/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((134573559/250000000 : ℝ)*X 2 0+(525227113/1000000000 : ℝ)*X 2 1+(-8531637/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4167255353/10000000000 : ℝ)*X 0 0+(554498139/1250000000 : ℝ)*X 0 1+(887197061/2000000000 : ℝ)*X 0 2+(4167255353/10000000000 : ℝ)*X 1 0+(554498139/1250000000 : ℝ)*X 1 1+(887197061/2000000000 : ℝ)*X 1 2+(4167255353/10000000000 : ℝ)*X 2 0+(554498139/1250000000 : ℝ)*X 2 1+(887197061/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15709/25000 : ℝ) ≤ (-9010197043053148263314493447477/14339843750000000000000000000000 : ℝ) := by norm_num
    linear_combination (7934899/20000000000000 : ℝ)*(upper1) + (10728711/10000000000000 : ℝ)*(lower2) + (405117/20000000000000 : ℝ)*(lower3) + (15795949/50000000000000 : ℝ)*(upper5) + (355872194359767/12500000000000 : ℝ)*(major0) + (355872194359767/12500000000000 : ℝ)*(major1) + (355872194359767/12500000000000 : ℝ)*(major2) + (3520987409/50000000000000 : ℝ)*(sp2) + (772921567/20000000000000 : ℝ)*(sp3) + (192200867536349/5000000000000 : ℝ)*(sp4) + (240251226726971/6250000000000 : ℝ)*(sp5) + (1922006292828359/50000000000000 : ℝ)*(sp6) + (935438025425211/50000000000000 : ℝ)*(sp7) + (569226139/25000000000000 : ℝ)*(sp12) + (1870879915458257/100000000000000 : ℝ)*(f.failure) + (240251226726971/6250000000000 : ℝ)*(f.sum) + (9107570292629/3671000000000000000000000000 : ℝ)*base66 + (1178477739805016587/114718750000000000000000000000000 : ℝ)*base68 + (935662773254829087/114718750000000000000000000000000 : ℝ)*base70 + (1510885333565204087/114718750000000000000000000000000 : ℝ)*base72 + (22996594310587/3671000000000000000000000000 : ℝ)*base74 + (520552421599954087/114718750000000000000000000000000 : ℝ)*base76 + (1857202950893204087/114718750000000000000000000000000 : ℝ)*base78 + (1408304652143016587/114718750000000000000000000000000 : ℝ)*base80 + (5951120483699/3671000000000000000000000000 : ℝ)*base81 + (20447709/2000000000000000000000 : ℝ)*base89 + (20447709/2000000000000000000000 : ℝ)*base91 + (20447709/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58817/100000 : ℝ) ≤ (134953211255740622656861470919209/229437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6429681/50000000000000 : ℝ)*(lower0) + (296604313/100000000000000 : ℝ)*(lower1) + (93040819/100000000000000 : ℝ)*(lower2) + (11293009/10000000000000 : ℝ)*(lower5) + (1456756941679427/50000000000000 : ℝ)*(major0) + (1456756941679427/50000000000000 : ℝ)*(major1) + (1456756941679427/50000000000000 : ℝ)*(major2) + (389281738225291/10000000000000 : ℝ)*(sp0) + (389279245075311/10000000000000 : ℝ)*(sp1) + (3892805733312273/100000000000000 : ℝ)*(sp2) + (38292018264147/2000000000000 : ℝ)*(sp3) + (11648940637/100000000000000 : ℝ)*(sp6) + (3084441023/100000000000000 : ℝ)*(sp7) + (124657499/500000000000 : ℝ)*(sp9) + (1914603997648373/100000000000000 : ℝ)*(f.failure) + (389281738225291/10000000000000 : ℝ)*(f.sum) + (194898046771/45887500000000000000000000 : ℝ)*base66 + (11430872172720881097/458875000000000000000000000000000 : ℝ)*base68 + (420666728874243903/458875000000000000000000000000000 : ℝ)*base69 + (783408823223631097/458875000000000000000000000000000 : ℝ)*base72 + (68007024635939/1835500000000000000000000000 : ℝ)*base74 + (2129424481059243903/458875000000000000000000000000000 : ℝ)*base75 + (2225063041467381097/458875000000000000000000000000000 : ℝ)*base78 + (3427510880883881097/458875000000000000000000000000000 : ℝ)*base80 + (19332992397263/3671000000000000000000000000 : ℝ)*base81 + (5895601/2000000000000000000000 : ℝ)*base89 + (5895601/2000000000000000000000 : ℝ)*base91 + (5895601/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (15913/20000 : ℝ) ≤ (182557835013921530561903919540543/229437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (102006023/100000000000000 : ℝ)*(upper1) + (21252753/100000000000000 : ℝ)*(lower3) + (56437087/50000000000000 : ℝ)*(upper4) + (239342019/100000000000000 : ℝ)*(lower5) + (1613986745796743/50000000000000 : ℝ)*(major0) + (1613986745796743/50000000000000 : ℝ)*(major1) + (1613986745796743/50000000000000 : ℝ)*(major2) + (90275498029/100000000000000 : ℝ)*(sp3) + (3520434899/25000000000000 : ℝ)*(sp4) + (2154077962819449/50000000000000 : ℝ)*(sp8) + (2154087294681051/50000000000000 : ℝ)*(sp9) + (2154087294681051/50000000000000 : ℝ)*(sp10) + (2121159596214577/100000000000000 : ℝ)*(sp11) + (4581983607/100000000000000 : ℝ)*(sp12) + (1060624935856303/50000000000000 : ℝ)*(f.failure) + (2154087294681051/50000000000000 : ℝ)*(f.sum) + (29998056052283/3671000000000000000000000000 : ℝ)*base65 + (915942053675085773/458875000000000000000000000000000 : ℝ)*base68 + (5217595620486335773/458875000000000000000000000000000 : ℝ)*base70 + (2928734375300085773/458875000000000000000000000000000 : ℝ)*base72 + (2824542233043/734200000000000000000000000 : ℝ)*base73 + (4392829064586710773/458875000000000000000000000000000 : ℝ)*base76 + (4035940428775585773/458875000000000000000000000000000 : ℝ)*base78 + (6043531047106335773/458875000000000000000000000000000 : ℝ)*base80 + (559809119449/367100000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (5967011/1000000000000000000000 : ℝ)*base89 + (5967011/1000000000000000000000 : ℝ)*base91 + (5967011/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-16819/20000 : ℝ) ≤ (-192939306625851657546537023446707/229437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21622433/100000000000000 : ℝ)*(lower1) + (5655603/50000000000000 : ℝ)*(upper3) + (13293497/50000000000000 : ℝ)*(lower4) + (11724333/50000000000000 : ℝ)*(upper5) + (1631852608653007/50000000000000 : ℝ)*(major0) + (1631852608653007/50000000000000 : ℝ)*(major1) + (1631852608653007/50000000000000 : ℝ)*(major2) + (868087143/50000000000000 : ℝ)*(sp4) + (28618403901/100000000000000 : ℝ)*(sp6) + (14087904177/100000000000000 : ℝ)*(sp7) + (4410708637929853/100000000000000 : ℝ)*(sp12) + (2205355187052069/50000000000000 : ℝ)*(sp13) + (2205340877850119/50000000000000 : ℝ)*(sp14) + (536179186118357/25000000000000 : ℝ)*(sp15) + (428946166475521/20000000000000 : ℝ)*(f.failure) + (2205355187052069/50000000000000 : ℝ)*(f.sum) + (3039494955981/1835500000000000000000000000 : ℝ)*base65 + (697108752879563523/458875000000000000000000000000000 : ℝ)*base67 + (4740084909140563523/458875000000000000000000000000000 : ℝ)*base69 + (5044590668867813523/458875000000000000000000000000000 : ℝ)*base71 + (3426116320269/458875000000000000000000000 : ℝ)*base74 + (11373011778520188523/458875000000000000000000000000000 : ℝ)*base75 + (3591052748618938523/458875000000000000000000000000000 : ℝ)*base77 + (2907934313479938523/458875000000000000000000000000000 : ℝ)*base79 + (15127844471091/734200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (4979123/400000000000000000000 : ℝ)*base90 + (4979123/400000000000000000000 : ℝ)*base92 + (4979123/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1277_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14661/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1099/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15709/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58817/100000 : ℝ) else (15913/20000 : ℝ) ≤ X j i ∧ X j i ≤ (16819/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1277_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1277_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14661/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15709/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58817/100000 : ℝ) else (15913/20000 : ℝ) ≤ X j i ∧ X j i ≤ (16819/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1277_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1277_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14661/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15709/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58817/100000 : ℝ) else (15913/20000 : ℝ) ≤ X j i ∧ X j i ≤ (16819/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1277_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

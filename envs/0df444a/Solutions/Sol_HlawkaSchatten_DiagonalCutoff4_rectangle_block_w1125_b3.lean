-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1125_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:11:41.829368+00:00
-- url     : https://prove2.me/submissions/059b33cf-d7a1-4178-8015-fa2d658e3820

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
theorem support_rectangle_w1125_s9_0 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2175046361/10000000000 : ℝ)*x 0 + (269664511/500000000 : ℝ)*x 1 + (210620299/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175046361/10000000000 : ℝ)^4159 ≤ (660743204699/5000000000000 : ℝ)^3135 := by
    have hnat : (2175046361 : ℕ)^4159*5000000000000^3135 ≤ 660743204699^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175046361 10000000000 660743204699 5000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269664511/500000000 : ℝ)^4159 ≤ (44082672524081/100000000000000 : ℝ)^3135 := by
    have hnat : (269664511 : ℕ)^4159*100000000000000^3135 ≤ 44082672524081^3135*500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269664511 500000000 44082672524081 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210620299/400000000 : ℝ)^4159 ≤ (1708098534591/4000000000000 : ℝ)^3135 := by
    have hnat : (210620299 : ℕ)^4159*4000000000000^3135 ≤ 1708098534591^3135*400000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210620299 400000000 1708098534591 4000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2175046361/10000000000 : ℝ), (269664511/500000000 : ℝ), (210620299/400000000 : ℝ)] ![(660743204699/5000000000000 : ℝ), (44082672524081/100000000000000 : ℝ), (1708098534591/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2175046361/10000000000 : ℝ)|^4159 ≤ (660743204699/5000000000000 : ℝ)^3135
        have hw : |(-2175046361/10000000000 : ℝ)|=(2175046361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269664511/500000000 : ℝ)|^4159 ≤ (44082672524081/100000000000000 : ℝ)^3135
        have hw : |(269664511/500000000 : ℝ)|=(269664511/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210620299/400000000 : ℝ)|^4159 ≤ (1708098534591/4000000000000 : ℝ)^3135
        have hw : |(210620299/400000000 : ℝ)|=(210620299/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s9_1 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672402751/5000000000 : ℝ)*x 0 + (-559965789/2500000000 : ℝ)*x 1 + (5265507839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672402751/5000000000 : ℝ)^4159 ≤ (21778853378769/50000000000000 : ℝ)^3135 := by
    have hnat : (2672402751 : ℕ)^4159*50000000000000^3135 ≤ 21778853378769^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672402751 5000000000 21778853378769 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559965789/2500000000 : ℝ)^4159 ≤ (6869912975783/50000000000000 : ℝ)^3135 := by
    have hnat : (559965789 : ℕ)^4159*50000000000000^3135 ≤ 6869912975783^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559965789 2500000000 6869912975783 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265507839/10000000000 : ℝ)^4159 ≤ (2135123364049/5000000000000 : ℝ)^3135 := by
    have hnat : (5265507839 : ℕ)^4159*5000000000000^3135 ≤ 2135123364049^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265507839 10000000000 2135123364049 5000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672402751/5000000000 : ℝ), (-559965789/2500000000 : ℝ), (5265507839/10000000000 : ℝ)] ![(21778853378769/50000000000000 : ℝ), (6869912975783/50000000000000 : ℝ), (2135123364049/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672402751/5000000000 : ℝ)|^4159 ≤ (21778853378769/50000000000000 : ℝ)^3135
        have hw : |(2672402751/5000000000 : ℝ)|=(2672402751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-559965789/2500000000 : ℝ)|^4159 ≤ (6869912975783/50000000000000 : ℝ)^3135
        have hw : |(-559965789/2500000000 : ℝ)|=(559965789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265507839/10000000000 : ℝ)|^4159 ≤ (2135123364049/5000000000000 : ℝ)^3135
        have hw : |(5265507839/10000000000 : ℝ)|=(5265507839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s9_2 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344805753/10000000000 : ℝ)*x 0 + (5265507551/10000000000 : ℝ)*x 1 + (-2239863203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344805753/10000000000 : ℝ)^4159 ≤ (8711541894243/20000000000000 : ℝ)^3135 := by
    have hnat : (5344805753 : ℕ)^4159*20000000000000^3135 ≤ 8711541894243^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344805753 10000000000 8711541894243 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265507551/10000000000 : ℝ)^4159 ≤ (10675616045611/25000000000000 : ℝ)^3135 := by
    have hnat : (5265507551 : ℕ)^4159*25000000000000^3135 ≤ 10675616045611^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265507551 10000000000 10675616045611 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239863203/10000000000 : ℝ)^4159 ≤ (6869913167023/50000000000000 : ℝ)^3135 := by
    have hnat : (2239863203 : ℕ)^4159*50000000000000^3135 ≤ 6869913167023^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239863203 10000000000 6869913167023 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344805753/10000000000 : ℝ), (5265507551/10000000000 : ℝ), (-2239863203/10000000000 : ℝ)] ![(8711541894243/20000000000000 : ℝ), (10675616045611/25000000000000 : ℝ), (6869913167023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344805753/10000000000 : ℝ)|^4159 ≤ (8711541894243/20000000000000 : ℝ)^3135
        have hw : |(5344805753/10000000000 : ℝ)|=(5344805753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265507551/10000000000 : ℝ)|^4159 ≤ (10675616045611/25000000000000 : ℝ)^3135
        have hw : |(5265507551/10000000000 : ℝ)|=(5265507551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2239863203/10000000000 : ℝ)|^4159 ≤ (6869913167023/50000000000000 : ℝ)^3135
        have hw : |(-2239863203/10000000000 : ℝ)|=(2239863203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s9_3 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2183538121/5000000000 : ℝ)*x 0 + (424222573/1000000000 : ℝ)*x 1 + (4495597709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183538121/5000000000 : ℝ)^4159 ≤ (16658449441743/50000000000000 : ℝ)^3135 := by
    have hnat : (2183538121 : ℕ)^4159*50000000000000^3135 ≤ 16658449441743^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183538121 5000000000 16658449441743 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424222573/1000000000 : ℝ)^4159 ≤ (32059220026169/100000000000000 : ℝ)^3135 := by
    have hnat : (424222573 : ℕ)^4159*100000000000000^3135 ≤ 32059220026169^3135*1000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424222573 1000000000 32059220026169 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4495597709/10000000000 : ℝ)^4159 ≤ (34623881074223/100000000000000 : ℝ)^3135 := by
    have hnat : (4495597709 : ℕ)^4159*100000000000000^3135 ≤ 34623881074223^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495597709 10000000000 34623881074223 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183538121/5000000000 : ℝ), (424222573/1000000000 : ℝ), (4495597709/10000000000 : ℝ)] ![(16658449441743/50000000000000 : ℝ), (32059220026169/100000000000000 : ℝ), (34623881074223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183538121/5000000000 : ℝ)|^4159 ≤ (16658449441743/50000000000000 : ℝ)^3135
        have hw : |(2183538121/5000000000 : ℝ)|=(2183538121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(424222573/1000000000 : ℝ)|^4159 ≤ (32059220026169/100000000000000 : ℝ)^3135
        have hw : |(424222573/1000000000 : ℝ)|=(424222573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4495597709/10000000000 : ℝ)|^4159 ≤ (34623881074223/100000000000000 : ℝ)^3135
        have hw : |(4495597709/10000000000 : ℝ)|=(4495597709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s9_4 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1087525373/5000000000 : ℝ)*x 0 + (5265828917/10000000000 : ℝ)*x 1 + (269648401/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087525373/5000000000 : ℝ)^4159 ≤ (3303724859487/25000000000000 : ℝ)^3135 := by
    have hnat : (1087525373 : ℕ)^4159*25000000000000^3135 ≤ 3303724859487^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087525373 5000000000 3303724859487 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265828917/10000000000 : ℝ)^4159 ≤ (42705921731323/100000000000000 : ℝ)^3135 := by
    have hnat : (5265828917 : ℕ)^4159*100000000000000^3135 ≤ 42705921731323^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265828917 10000000000 42705921731323 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269648401/500000000 : ℝ)^4159 ≤ (11019794703629/25000000000000 : ℝ)^3135 := by
    have hnat : (269648401 : ℕ)^4159*25000000000000^3135 ≤ 11019794703629^3135*500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269648401 500000000 11019794703629 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1087525373/5000000000 : ℝ), (5265828917/10000000000 : ℝ), (269648401/500000000 : ℝ)] ![(3303724859487/25000000000000 : ℝ), (42705921731323/100000000000000 : ℝ), (11019794703629/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1087525373/5000000000 : ℝ)|^4159 ≤ (3303724859487/25000000000000 : ℝ)^3135
        have hw : |(-1087525373/5000000000 : ℝ)|=(1087525373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265828917/10000000000 : ℝ)|^4159 ≤ (42705921731323/100000000000000 : ℝ)^3135
        have hw : |(5265828917/10000000000 : ℝ)|=(5265828917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269648401/500000000 : ℝ)|^4159 ≤ (11019794703629/25000000000000 : ℝ)^3135
        have hw : |(269648401/500000000 : ℝ)|=(269648401/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s9_5 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312472351/10000000000 : ℝ)*x 0 + (-2112403123/10000000000 : ℝ)*x 1 + (5392967963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312472351/10000000000 : ℝ)^4159 ≤ (21604241960623/50000000000000 : ℝ)^3135 := by
    have hnat : (5312472351 : ℕ)^4159*50000000000000^3135 ≤ 21604241960623^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312472351 10000000000 21604241960623 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112403123/10000000000 : ℝ)^4159 ≤ (12712337879043/100000000000000 : ℝ)^3135 := by
    have hnat : (2112403123 : ℕ)^4159*100000000000000^3135 ≤ 12712337879043^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112403123 10000000000 12712337879043 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392967963/10000000000 : ℝ)^4159 ≤ (22039589098227/50000000000000 : ℝ)^3135 := by
    have hnat : (5392967963 : ℕ)^4159*50000000000000^3135 ≤ 22039589098227^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392967963 10000000000 22039589098227 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312472351/10000000000 : ℝ), (-2112403123/10000000000 : ℝ), (5392967963/10000000000 : ℝ)] ![(21604241960623/50000000000000 : ℝ), (12712337879043/100000000000000 : ℝ), (22039589098227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312472351/10000000000 : ℝ)|^4159 ≤ (21604241960623/50000000000000 : ℝ)^3135
        have hw : |(5312472351/10000000000 : ℝ)|=(5312472351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2112403123/10000000000 : ℝ)|^4159 ≤ (12712337879043/100000000000000 : ℝ)^3135
        have hw : |(-2112403123/10000000000 : ℝ)|=(2112403123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392967963/10000000000 : ℝ)|^4159 ≤ (22039589098227/50000000000000 : ℝ)^3135
        have hw : |(5392967963/10000000000 : ℝ)|=(5392967963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s9_6 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328118321/2500000000 : ℝ)*x 0 + (134824207/250000000 : ℝ)*x 1 + (-2112401431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328118321/2500000000 : ℝ)^4159 ≤ (43208493988369/100000000000000 : ℝ)^3135 := by
    have hnat : (1328118321 : ℕ)^4159*100000000000000^3135 ≤ 43208493988369^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328118321 2500000000 43208493988369 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134824207/250000000 : ℝ)^4159 ≤ (8815836326749/20000000000000 : ℝ)^3135 := by
    have hnat : (134824207 : ℕ)^4159*20000000000000^3135 ≤ 8815836326749^3135*250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134824207 250000000 8815836326749 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112401431/10000000000 : ℝ)^4159 ≤ (2542464874151/20000000000000 : ℝ)^3135 := by
    have hnat : (2112401431 : ℕ)^4159*20000000000000^3135 ≤ 2542464874151^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112401431 10000000000 2542464874151 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328118321/2500000000 : ℝ), (134824207/250000000 : ℝ), (-2112401431/10000000000 : ℝ)] ![(43208493988369/100000000000000 : ℝ), (8815836326749/20000000000000 : ℝ), (2542464874151/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328118321/2500000000 : ℝ)|^4159 ≤ (43208493988369/100000000000000 : ℝ)^3135
        have hw : |(1328118321/2500000000 : ℝ)|=(1328118321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134824207/250000000 : ℝ)|^4159 ≤ (8815836326749/20000000000000 : ℝ)^3135
        have hw : |(134824207/250000000 : ℝ)|=(134824207/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2112401431/10000000000 : ℝ)|^4159 ≤ (2542464874151/20000000000000 : ℝ)^3135
        have hw : |(-2112401431/10000000000 : ℝ)|=(2112401431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s9_7 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4367086627/10000000000 : ℝ)*x 0 + (1123740461/2500000000 : ℝ)*x 1 + (1060715811/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367086627/10000000000 : ℝ)^4159 ≤ (16658501995267/50000000000000 : ℝ)^3135 := by
    have hnat : (4367086627 : ℕ)^4159*50000000000000^3135 ≤ 16658501995267^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367086627 10000000000 16658501995267 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123740461/2500000000 : ℝ)^4159 ≤ (17308692173971/50000000000000 : ℝ)^3135 := by
    have hnat : (1123740461 : ℕ)^4159*50000000000000^3135 ≤ 17308692173971^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123740461 2500000000 17308692173971 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060715811/2500000000 : ℝ)^4159 ≤ (32065611646043/100000000000000 : ℝ)^3135 := by
    have hnat : (1060715811 : ℕ)^4159*100000000000000^3135 ≤ 32065611646043^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060715811 2500000000 32065611646043 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367086627/10000000000 : ℝ), (1123740461/2500000000 : ℝ), (1060715811/2500000000 : ℝ)] ![(16658501995267/50000000000000 : ℝ), (17308692173971/50000000000000 : ℝ), (32065611646043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367086627/10000000000 : ℝ)|^4159 ≤ (16658501995267/50000000000000 : ℝ)^3135
        have hw : |(4367086627/10000000000 : ℝ)|=(4367086627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123740461/2500000000 : ℝ)|^4159 ≤ (17308692173971/50000000000000 : ℝ)^3135
        have hw : |(1123740461/2500000000 : ℝ)|=(1123740461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060715811/2500000000 : ℝ)|^4159 ≤ (32065611646043/100000000000000 : ℝ)^3135
        have hw : |(1060715811/2500000000 : ℝ)|=(1060715811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s9_8 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-601533/80000000 : ℝ)*x 0 + (360848849/625000000 : ℝ)*x 1 + (3036235843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (601533/80000000 : ℝ)^4159 ≤ (152213291329/100000000000000 : ℝ)^3135 := by
    have hnat : (601533 : ℕ)^4159*100000000000000^3135 ≤ 152213291329^3135*80000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601533 80000000 152213291329 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (360848849/625000000 : ℝ)^4159 ≤ (48253081157201/100000000000000 : ℝ)^3135 := by
    have hnat : (360848849 : ℕ)^4159*100000000000000^3135 ≤ 48253081157201^3135*625000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360848849 625000000 48253081157201 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3036235843/5000000000 : ℝ)^4159 ≤ (51594705540729/100000000000000 : ℝ)^3135 := by
    have hnat : (3036235843 : ℕ)^4159*100000000000000^3135 ≤ 51594705540729^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3036235843 5000000000 51594705540729 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-601533/80000000 : ℝ), (360848849/625000000 : ℝ), (3036235843/5000000000 : ℝ)] ![(152213291329/100000000000000 : ℝ), (48253081157201/100000000000000 : ℝ), (51594705540729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-601533/80000000 : ℝ)|^4159 ≤ (152213291329/100000000000000 : ℝ)^3135
        have hw : |(-601533/80000000 : ℝ)|=(601533/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(360848849/625000000 : ℝ)|^4159 ≤ (48253081157201/100000000000000 : ℝ)^3135
        have hw : |(360848849/625000000 : ℝ)|=(360848849/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3036235843/5000000000 : ℝ)|^4159 ≤ (51594705540729/100000000000000 : ℝ)^3135
        have hw : |(3036235843/5000000000 : ℝ)|=(3036235843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1125_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11331/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2833/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7019/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14039/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11331/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14039/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11331/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14039/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11331/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14039/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11331/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14039/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11331/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14039/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11331/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11331/100000 : ℝ) ^ (8317/2048 : ℝ) ≤ (7216391341457647/50000000000000000000 : ℝ) := by
    have hpowers : (11331/100000 : ℝ)^8317 ≤ (7216391341457647/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11331 : ℕ)^8317*50000000000000000000^2048 ≤ 7216391341457647^2048*100000^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11331 100000 7216391341457647 50000000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11331/100000 : ℝ)) (X := (7216391341457647/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14039/100000 : ℝ) ^ (8317/2048 : ℝ) ≤ (8614741197281941/25000000000000000000 : ℝ) := by
    have hpowers : (14039/100000 : ℝ)^8317 ≤ (8614741197281941/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14039 : ℕ)^8317*25000000000000000000^2048 ≤ 8614741197281941^2048*100000^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14039 100000 8614741197281941 25000000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14039/100000 : ℝ)) (X := (8614741197281941/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007216391341457647/25000000000000000000 : ℝ) ≤ (2500177678994107/2500000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (25007216391341457647/25000000000000000000 : ℝ)^2048 ≤ (2500177678994107/2500000000000000 : ℝ)^8317 := by
      have hnat : (25007216391341457647 : ℕ)^2048*2500000000000000^8317 ≤ 2500177678994107^8317*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007216391341457647 25000000000000000000 2500177678994107 2500000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500177678994107/2500000000000000 : ℝ)) (X := (25007216391341457647/25000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024445873736021529/50000000000000000000 : ℝ) ≤ (80009629612007/80000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (50024445873736021529/50000000000000000000 : ℝ)^2048 ≤ (80009629612007/80000000000000 : ℝ)^8317 := by
      have hnat : (50024445873736021529 : ℕ)^2048*80000000000000^8317 ≤ 80009629612007^8317*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024445873736021529 50000000000000000000 80009629612007 80000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80009629612007/80000000000000 : ℝ)) (X := (50024445873736021529/50000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508614741197281941/12500000000000000000 : ℝ) ≤ (5000848343512661/5000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (12508614741197281941/12500000000000000000 : ℝ)^2048 ≤ (5000848343512661/5000000000000000 : ℝ)^8317 := by
      have hnat : (12508614741197281941 : ℕ)^2048*5000000000000000^8317 ≤ 5000848343512661^8317*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508614741197281941 12500000000000000000 5000848343512661 5000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000848343512661/5000000000000000 : ℝ)) (X := (12508614741197281941/12500000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7216391341457647/50000000000000000000 : ℝ) ≤ ((2707075258090914911/2708000000000000000 : ℝ)+2*(492985524447/270800000000000 : ℝ)*(11331/100000 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (2707075258090914911/2708000000000000000 : ℝ)+2*(492985524447/270800000000000 : ℝ)*(11331/100000 : ℝ)=(2500177678994107/2500000000000000 : ℝ) by norm_num, show 1+2*(7216391341457647/50000000000000000000 : ℝ)=(25007216391341457647/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8614741197281941/25000000000000000000 : ℝ)+(7216391341457647/50000000000000000000 : ℝ) ≤ ((2707075258090914911/2708000000000000000 : ℝ)+(492985524447/270800000000000 : ℝ)*((14039/100000 : ℝ)+(11331/100000 : ℝ)))^(8317/2048 : ℝ) := by
    rw [show (2707075258090914911/2708000000000000000 : ℝ)+(492985524447/270800000000000 : ℝ)*((14039/100000 : ℝ)+(11331/100000 : ℝ))=(80009629612007/80000000000000 : ℝ) by norm_num, show 1+(8614741197281941/25000000000000000000 : ℝ)+(7216391341457647/50000000000000000000 : ℝ)=(50024445873736021529/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8614741197281941/25000000000000000000 : ℝ) ≤ ((2707075258090914911/2708000000000000000 : ℝ)+2*(492985524447/270800000000000 : ℝ)*(14039/100000 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (2707075258090914911/2708000000000000000 : ℝ)+2*(492985524447/270800000000000 : ℝ)*(14039/100000 : ℝ)=(5000848343512661/5000000000000000 : ℝ) by norm_num, show 1+2*(8614741197281941/25000000000000000000 : ℝ)=(12508614741197281941/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2707075258090914911/2708000000000000000 : ℝ)*(X 1 0+X 2 0)+(492985524447/270800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (11331/100000 : ℝ)) (hi := (14039/100000 : ℝ)) (c := (2707075258090914911/2708000000000000000 : ℝ)) (alpha := (492985524447/270800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2707075258090914911/2708000000000000000 : ℝ)*(X 0 1+X 2 1)+(492985524447/270800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (11331/100000 : ℝ)) (hi := (14039/100000 : ℝ)) (c := (2707075258090914911/2708000000000000000 : ℝ)) (alpha := (492985524447/270800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2707075258090914911/2708000000000000000 : ℝ)*(X 0 2+X 1 2)+(492985524447/270800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (11331/100000 : ℝ)) (hi := (14039/100000 : ℝ)) (c := (2707075258090914911/2708000000000000000 : ℝ)) (alpha := (492985524447/270800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2175046361/10000000000 : ℝ)*X 0 0+(269664511/500000000 : ℝ)*X 0 1+(210620299/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672402751/5000000000 : ℝ)*X 1 0+(-559965789/2500000000 : ℝ)*X 1 1+(5265507839/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344805753/10000000000 : ℝ)*X 2 0+(5265507551/10000000000 : ℝ)*X 2 1+(-2239863203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183538121/5000000000 : ℝ)*X 0 0+(424222573/1000000000 : ℝ)*X 0 1+(4495597709/10000000000 : ℝ)*X 0 2+(2183538121/5000000000 : ℝ)*X 1 0+(424222573/1000000000 : ℝ)*X 1 1+(4495597709/10000000000 : ℝ)*X 1 2+(2183538121/5000000000 : ℝ)*X 2 0+(424222573/1000000000 : ℝ)*X 2 1+(4495597709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1087525373/5000000000 : ℝ)*X 0 0+(5265828917/10000000000 : ℝ)*X 0 1+(269648401/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312472351/10000000000 : ℝ)*X 1 0+(-2112403123/10000000000 : ℝ)*X 1 1+(5392967963/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s9_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328118321/2500000000 : ℝ)*X 2 0+(134824207/250000000 : ℝ)*X 2 1+(-2112401431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s9_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367086627/10000000000 : ℝ)*X 0 0+(1123740461/2500000000 : ℝ)*X 0 1+(1060715811/2500000000 : ℝ)*X 0 2+(4367086627/10000000000 : ℝ)*X 1 0+(1123740461/2500000000 : ℝ)*X 1 1+(1060715811/2500000000 : ℝ)*X 1 2+(4367086627/10000000000 : ℝ)*X 2 0+(1123740461/2500000000 : ℝ)*X 2 1+(1060715811/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s9_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-601533/80000000 : ℝ)*X 0 0+(360848849/625000000 : ℝ)*X 0 1+(3036235843/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s9_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (76343507404107783113498493/16925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (128990281/25000000000000 : ℝ)*(lower2) + (80842309/25000000000000 : ℝ)*(lower4) + (59236261/25000000000000 : ℝ)*(lower5) + (1471569631592279/25000000000000 : ℝ)*(major0) + (1471569631592279/25000000000000 : ℝ)*(major1) + (1471569631592279/25000000000000 : ℝ)*(major2) + (7825794664426653/100000000000000 : ℝ)*(sp0) + (1565159061267847/20000000000000 : ℝ)*(sp1) + (978224264992423/12500000000000 : ℝ)*(sp2) + (61668091409129/1562500000000 : ℝ)*(sp3) + (316018337/100000000000000 : ℝ)*(sp4) + (3745858247/100000000000000 : ℝ)*(sp5) + (2466129049/50000000000000 : ℝ)*(sp6) + (4071752493/100000000000000 : ℝ)*(sp8) + (61668091409129/1562500000000 : ℝ)*(f.failure) + (3912899526098741/50000000000000 : ℝ)*(f.sum) + (8368634377293/3385000000000000000000000000 : ℝ)*base65 + (894657722282997831/67700000000000000000000000000000 : ℝ)*base68 + (66769195309802169/67700000000000000000000000000000 : ℝ)*base69 + (72716707874402169/67700000000000000000000000000000 : ℝ)*base71 + (4784731385151/1692500000000000000000000000 : ℝ)*base74 + (133225078299702169/67700000000000000000000000000000 : ℝ)*base75 + (47476095413502169/67700000000000000000000000000000 : ℝ)*base77 + (296764354879902169/67700000000000000000000000000000 : ℝ)*base79 + (2750012941823/3385000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2327/1250000000000000000 : ℝ)*base90 + (2327/1250000000000000000 : ℝ)*base92 + (2327/1250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (160229019505586262888022911/67700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (171584689/12500000000000 : ℝ)*(lower2) + (212342021/50000000000000 : ℝ)*(lower3) + (55019917/12500000000000 : ℝ)*(lower4) + (58000859/20000000000000 : ℝ)*(lower5) + (2958049654482667/50000000000000 : ℝ)*(major0) + (2958049654482667/50000000000000 : ℝ)*(major1) + (2958049654482667/50000000000000 : ℝ)*(major2) + (61446616357/100000000000000 : ℝ)*(sp2) + (3434151969/20000000000000 : ℝ)*(sp3) + (7865440222972553/100000000000000 : ℝ)*(sp4) + (3932722906548483/50000000000000 : ℝ)*(sp5) + (7865384366480609/100000000000000 : ℝ)*(sp6) + (1983367777591081/50000000000000 : ℝ)*(sp7) + (5590124413/100000000000000 : ℝ)*(sp8) + (1983376362971003/50000000000000 : ℝ)*(f.failure) + (3932722906548483/50000000000000 : ℝ)*(f.sum) + (39744474634621/6770000000000000000000000000 : ℝ)*base66 + (2474265712889437637/135400000000000000000000000000000 : ℝ)*base67 + (1168158140066562363/135400000000000000000000000000000 : ℝ)*base70 + (491843686379162363/135400000000000000000000000000000 : ℝ)*base72 + (22065156895051/6770000000000000000000000000 : ℝ)*base74 + (1996969201181437637/135400000000000000000000000000000 : ℝ)*base75 + (781202248248562363/135400000000000000000000000000000 : ℝ)*base78 + (275081240774162363/135400000000000000000000000000000 : ℝ)*base80 + (12376419813761/6770000000000000000000000000 : ℝ)*base82 + (6411/40000000000000000000 : ℝ)*base89 + (6411/40000000000000000000 : ℝ)*base91 + (6411/40000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1125_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11331/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2833/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7019/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1125_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1125_box_0 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2047594167/10000000000 : ℝ)*x 0 + (5376548969/10000000000 : ℝ)*x 1 + (2688274331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2047594167/10000000000 : ℝ)^4159 ≤ (47646633817/390625000000 : ℝ)^3135 := by
    have hnat : (2047594167 : ℕ)^4159*390625000000^3135 ≤ 47646633817^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047594167 10000000000 47646633817 390625000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376548969/10000000000 : ℝ)^4159 ≤ (8780246505237/20000000000000 : ℝ)^3135 := by
    have hnat : (5376548969 : ℕ)^4159*20000000000000^3135 ≤ 8780246505237^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376548969 10000000000 8780246505237 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688274331/5000000000 : ℝ)^4159 ≤ (34297835313/78125000000 : ℝ)^3135 := by
    have hnat : (2688274331 : ℕ)^4159*78125000000^3135 ≤ 34297835313^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688274331 5000000000 34297835313 78125000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2047594167/10000000000 : ℝ), (5376548969/10000000000 : ℝ), (2688274331/5000000000 : ℝ)] ![(47646633817/390625000000 : ℝ), (8780246505237/20000000000000 : ℝ), (34297835313/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2047594167/10000000000 : ℝ)|^4159 ≤ (47646633817/390625000000 : ℝ)^3135
        have hw : |(-2047594167/10000000000 : ℝ)|=(2047594167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376548969/10000000000 : ℝ)|^4159 ≤ (8780246505237/20000000000000 : ℝ)^3135
        have hw : |(5376548969/10000000000 : ℝ)|=(5376548969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688274331/5000000000 : ℝ)|^4159 ≤ (34297835313/78125000000 : ℝ)^3135
        have hw : |(2688274331/5000000000 : ℝ)|=(2688274331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_box_1 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647911999/5000000000 : ℝ)*x 0 + (-2157027747/10000000000 : ℝ)*x 1 + (2688274521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647911999/5000000000 : ℝ)^4159 ≤ (2151446962759/5000000000000 : ℝ)^3135 := by
    have hnat : (2647911999 : ℕ)^4159*5000000000000^3135 ≤ 2151446962759^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647911999 5000000000 2151446962759 5000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2157027747/10000000000 : ℝ)^4159 ≤ (13069827410433/100000000000000 : ℝ)^3135 := by
    have hnat : (2157027747 : ℕ)^4159*100000000000000^3135 ≤ 13069827410433^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157027747 10000000000 13069827410433 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688274521/5000000000 : ℝ)^4159 ≤ (878024666339/2000000000000 : ℝ)^3135 := by
    have hnat : (2688274521 : ℕ)^4159*2000000000000^3135 ≤ 878024666339^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688274521 5000000000 878024666339 2000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647911999/5000000000 : ℝ), (-2157027747/10000000000 : ℝ), (2688274521/5000000000 : ℝ)] ![(2151446962759/5000000000000 : ℝ), (13069827410433/100000000000000 : ℝ), (878024666339/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647911999/5000000000 : ℝ)|^4159 ≤ (2151446962759/5000000000000 : ℝ)^3135
        have hw : |(2647911999/5000000000 : ℝ)|=(2647911999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2157027747/10000000000 : ℝ)|^4159 ≤ (13069827410433/100000000000000 : ℝ)^3135
        have hw : |(-2157027747/10000000000 : ℝ)|=(2157027747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688274521/5000000000 : ℝ)|^4159 ≤ (878024666339/2000000000000 : ℝ)^3135
        have hw : |(2688274521/5000000000 : ℝ)|=(2688274521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_box_2 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295824271/10000000000 : ℝ)*x 0 + (2688274287/5000000000 : ℝ)*x 1 + (-2157028011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295824271/10000000000 : ℝ)^4159 ≤ (43028942197847/100000000000000 : ℝ)^3135 := by
    have hnat : (5295824271 : ℕ)^4159*100000000000000^3135 ≤ 43028942197847^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295824271 10000000000 43028942197847 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688274287/5000000000 : ℝ)^4159 ≤ (43901228247389/100000000000000 : ℝ)^3135 := by
    have hnat : (2688274287 : ℕ)^4159*100000000000000^3135 ≤ 43901228247389^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688274287 5000000000 43901228247389 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2157028011/10000000000 : ℝ)^4159 ≤ (261396590651/2000000000000 : ℝ)^3135 := by
    have hnat : (2157028011 : ℕ)^4159*2000000000000^3135 ≤ 261396590651^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157028011 10000000000 261396590651 2000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295824271/10000000000 : ℝ), (2688274287/5000000000 : ℝ), (-2157028011/10000000000 : ℝ)] ![(43028942197847/100000000000000 : ℝ), (43901228247389/100000000000000 : ℝ), (261396590651/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295824271/10000000000 : ℝ)|^4159 ≤ (43028942197847/100000000000000 : ℝ)^3135
        have hw : |(5295824271/10000000000 : ℝ)|=(5295824271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688274287/5000000000 : ℝ)|^4159 ≤ (43901228247389/100000000000000 : ℝ)^3135
        have hw : |(2688274287/5000000000 : ℝ)|=(2688274287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2157028011/10000000000 : ℝ)|^4159 ≤ (261396590651/2000000000000 : ℝ)^3135
        have hw : |(-2157028011/10000000000 : ℝ)|=(2157028011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_box_3 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1118699777/2500000000 : ℝ)*x 0 + (2157666833/5000000000 : ℝ)*x 1 + (863066991/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1118699777/2500000000 : ℝ)^4159 ≤ (4301441816349/12500000000000 : ℝ)^3135 := by
    have hnat : (1118699777 : ℕ)^4159*12500000000000^3135 ≤ 4301441816349^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118699777 2500000000 4301441816349 12500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2157666833/5000000000 : ℝ)^4159 ≤ (16397113115777/50000000000000 : ℝ)^3135 := by
    have hnat : (2157666833 : ℕ)^4159*50000000000000^3135 ≤ 16397113115777^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157666833 5000000000 16397113115777 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (863066991/2000000000 : ℝ)^4159 ≤ (8198559806721/25000000000000 : ℝ)^3135 := by
    have hnat : (863066991 : ℕ)^4159*25000000000000^3135 ≤ 8198559806721^3135*2000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863066991 2000000000 8198559806721 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1118699777/2500000000 : ℝ), (2157666833/5000000000 : ℝ), (863066991/2000000000 : ℝ)] ![(4301441816349/12500000000000 : ℝ), (16397113115777/50000000000000 : ℝ), (8198559806721/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1118699777/2500000000 : ℝ)|^4159 ≤ (4301441816349/12500000000000 : ℝ)^3135
        have hw : |(1118699777/2500000000 : ℝ)|=(1118699777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2157666833/5000000000 : ℝ)|^4159 ≤ (16397113115777/50000000000000 : ℝ)^3135
        have hw : |(2157666833/5000000000 : ℝ)|=(2157666833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(863066991/2000000000 : ℝ)|^4159 ≤ (8198559806721/25000000000000 : ℝ)^3135
        have hw : |(863066991/2000000000 : ℝ)|=(863066991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_box_4 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1151941593/5000000000 : ℝ)*x 0 + (264046099/500000000 : ℝ)*x 1 + (660115269/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1151941593/5000000000 : ℝ)^4159 ≤ (14263229607313/100000000000000 : ℝ)^3135 := by
    have hnat : (1151941593 : ℕ)^4159*100000000000000^3135 ≤ 14263229607313^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1151941593 5000000000 14263229607313 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264046099/500000000 : ℝ)^4159 ≤ (42868384268717/100000000000000 : ℝ)^3135 := by
    have hnat : (264046099 : ℕ)^4159*100000000000000^3135 ≤ 42868384268717^3135*500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264046099 500000000 42868384268717 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660115269/1250000000 : ℝ)^4159 ≤ (42868386120999/100000000000000 : ℝ)^3135 := by
    have hnat : (660115269 : ℕ)^4159*100000000000000^3135 ≤ 42868386120999^3135*1250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660115269 1250000000 42868386120999 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1151941593/5000000000 : ℝ), (264046099/500000000 : ℝ), (660115269/1250000000 : ℝ)] ![(14263229607313/100000000000000 : ℝ), (42868384268717/100000000000000 : ℝ), (42868386120999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1151941593/5000000000 : ℝ)|^4159 ≤ (14263229607313/100000000000000 : ℝ)^3135
        have hw : |(-1151941593/5000000000 : ℝ)|=(1151941593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264046099/500000000 : ℝ)|^4159 ≤ (42868384268717/100000000000000 : ℝ)^3135
        have hw : |(264046099/500000000 : ℝ)|=(264046099/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(660115269/1250000000 : ℝ)|^4159 ≤ (42868386120999/100000000000000 : ℝ)^3135
        have hw : |(660115269/1250000000 : ℝ)|=(660115269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_box_5 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363410573/10000000000 : ℝ)*x 0 + (-1097296697/5000000000 : ℝ)*x 1 + (1320230469/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363410573/10000000000 : ℝ)^4159 ≤ (10939742265653/25000000000000 : ℝ)^3135 := by
    have hnat : (5363410573 : ℕ)^4159*25000000000000^3135 ≤ 10939742265653^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363410573 10000000000 10939742265653 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097296697/5000000000 : ℝ)^4159 ≤ (13372647774581/100000000000000 : ℝ)^3135 := by
    have hnat : (1097296697 : ℕ)^4159*100000000000000^3135 ≤ 13372647774581^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097296697 5000000000 13372647774581 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320230469/2500000000 : ℝ)^4159 ≤ (10717095787183/25000000000000 : ℝ)^3135 := by
    have hnat : (1320230469 : ℕ)^4159*25000000000000^3135 ≤ 10717095787183^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320230469 2500000000 10717095787183 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363410573/10000000000 : ℝ), (-1097296697/5000000000 : ℝ), (1320230469/2500000000 : ℝ)] ![(10939742265653/25000000000000 : ℝ), (13372647774581/100000000000000 : ℝ), (10717095787183/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363410573/10000000000 : ℝ)|^4159 ≤ (10939742265653/25000000000000 : ℝ)^3135
        have hw : |(5363410573/10000000000 : ℝ)|=(5363410573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1097296697/5000000000 : ℝ)|^4159 ≤ (13372647774581/100000000000000 : ℝ)^3135
        have hw : |(-1097296697/5000000000 : ℝ)|=(1097296697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320230469/2500000000 : ℝ)|^4159 ≤ (10717095787183/25000000000000 : ℝ)^3135
        have hw : |(1320230469/2500000000 : ℝ)|=(1320230469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_box_6 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363410427/10000000000 : ℝ)*x 0 + (5280921859/10000000000 : ℝ)*x 1 + (-2194593613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363410427/10000000000 : ℝ)^4159 ≤ (21879483741173/50000000000000 : ℝ)^3135 := by
    have hnat : (5363410427 : ℕ)^4159*50000000000000^3135 ≤ 21879483741173^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363410427 10000000000 21879483741173 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280921859/10000000000 : ℝ)^4159 ≤ (21434191482829/50000000000000 : ℝ)^3135 := by
    have hnat : (5280921859 : ℕ)^4159*50000000000000^3135 ≤ 21434191482829^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280921859 10000000000 21434191482829 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2194593613/10000000000 : ℝ)^4159 ≤ (1337264954493/10000000000000 : ℝ)^3135 := by
    have hnat : (2194593613 : ℕ)^4159*10000000000000^3135 ≤ 1337264954493^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194593613 10000000000 1337264954493 10000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363410427/10000000000 : ℝ), (5280921859/10000000000 : ℝ), (-2194593613/10000000000 : ℝ)] ![(21879483741173/50000000000000 : ℝ), (21434191482829/50000000000000 : ℝ), (1337264954493/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363410427/10000000000 : ℝ)|^4159 ≤ (21879483741173/50000000000000 : ℝ)^3135
        have hw : |(5363410427/10000000000 : ℝ)|=(5363410427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280921859/10000000000 : ℝ)|^4159 ≤ (21434191482829/50000000000000 : ℝ)^3135
        have hw : |(5280921859/10000000000 : ℝ)|=(5280921859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2194593613/10000000000 : ℝ)|^4159 ≤ (1337264954493/10000000000000 : ℝ)^3135
        have hw : |(-2194593613/10000000000 : ℝ)|=(2194593613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_box_7 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (425899899/1000000000 : ℝ)*x 0 + (2211606749/5000000000 : ℝ)*x 1 + (2211606649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425899899/1000000000 : ℝ)^4159 ≤ (32227490583847/100000000000000 : ℝ)^3135 := by
    have hnat : (425899899 : ℕ)^4159*100000000000000^3135 ≤ 32227490583847^3135*1000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425899899 1000000000 32227490583847 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2211606749/5000000000 : ℝ)^4159 ≤ (16943127859027/50000000000000 : ℝ)^3135 := by
    have hnat : (2211606749 : ℕ)^4159*50000000000000^3135 ≤ 16943127859027^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211606749 5000000000 16943127859027 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2211606649/5000000000 : ℝ)^4159 ≤ (33886253685383/100000000000000 : ℝ)^3135 := by
    have hnat : (2211606649 : ℕ)^4159*100000000000000^3135 ≤ 33886253685383^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211606649 5000000000 33886253685383 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(425899899/1000000000 : ℝ), (2211606749/5000000000 : ℝ), (2211606649/5000000000 : ℝ)] ![(32227490583847/100000000000000 : ℝ), (16943127859027/50000000000000 : ℝ), (33886253685383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(425899899/1000000000 : ℝ)|^4159 ≤ (32227490583847/100000000000000 : ℝ)^3135
        have hw : |(425899899/1000000000 : ℝ)|=(425899899/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2211606749/5000000000 : ℝ)|^4159 ≤ (16943127859027/50000000000000 : ℝ)^3135
        have hw : |(2211606749/5000000000 : ℝ)|=(2211606749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2211606649/5000000000 : ℝ)|^4159 ≤ (33886253685383/100000000000000 : ℝ)^3135
        have hw : |(2211606649/5000000000 : ℝ)|=(2211606649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_box_8 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1125154527/5000000000 : ℝ)*x 0 + (5215919279/10000000000 : ℝ)*x 1 + (538615563/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1125154527/5000000000 : ℝ)^4159 ≤ (13824898062931/100000000000000 : ℝ)^3135 := by
    have hnat : (1125154527 : ℕ)^4159*100000000000000^3135 ≤ 13824898062931^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125154527 5000000000 13824898062931 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215919279/10000000000 : ℝ)^4159 ≤ (42169775897867/100000000000000 : ℝ)^3135 := by
    have hnat : (5215919279 : ℕ)^4159*100000000000000^3135 ≤ 42169775897867^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215919279 10000000000 42169775897867 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538615563/1000000000 : ℝ)^4159 ≤ (1760213041043/4000000000000 : ℝ)^3135 := by
    have hnat : (538615563 : ℕ)^4159*4000000000000^3135 ≤ 1760213041043^3135*1000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538615563 1000000000 1760213041043 4000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1125154527/5000000000 : ℝ), (5215919279/10000000000 : ℝ), (538615563/1000000000 : ℝ)] ![(13824898062931/100000000000000 : ℝ), (42169775897867/100000000000000 : ℝ), (1760213041043/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1125154527/5000000000 : ℝ)|^4159 ≤ (13824898062931/100000000000000 : ℝ)^3135
        have hw : |(-1125154527/5000000000 : ℝ)|=(1125154527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215919279/10000000000 : ℝ)|^4159 ≤ (42169775897867/100000000000000 : ℝ)^3135
        have hw : |(5215919279/10000000000 : ℝ)|=(5215919279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538615563/1000000000 : ℝ)|^4159 ≤ (1760213041043/4000000000000 : ℝ)^3135
        have hw : |(538615563/1000000000 : ℝ)|=(538615563/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_box_9 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289031061/10000000000 : ℝ)*x 0 + (-2153183853/10000000000 : ℝ)*x 1 + (5386155859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289031061/10000000000 : ℝ)^4159 ≤ (42955733530511/100000000000000 : ℝ)^3135 := by
    have hnat : (5289031061 : ℕ)^4159*100000000000000^3135 ≤ 42955733530511^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289031061 10000000000 42955733530511 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2153183853/10000000000 : ℝ)^4159 ≤ (13038937942023/100000000000000 : ℝ)^3135 := by
    have hnat : (2153183853 : ℕ)^4159*100000000000000^3135 ≤ 13038937942023^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153183853 10000000000 13038937942023 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386155859/10000000000 : ℝ)^4159 ≤ (44005328508141/100000000000000 : ℝ)^3135 := by
    have hnat : (5386155859 : ℕ)^4159*100000000000000^3135 ≤ 44005328508141^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386155859 10000000000 44005328508141 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289031061/10000000000 : ℝ), (-2153183853/10000000000 : ℝ), (5386155859/10000000000 : ℝ)] ![(42955733530511/100000000000000 : ℝ), (13038937942023/100000000000000 : ℝ), (44005328508141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289031061/10000000000 : ℝ)|^4159 ≤ (42955733530511/100000000000000 : ℝ)^3135
        have hw : |(5289031061/10000000000 : ℝ)|=(5289031061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2153183853/10000000000 : ℝ)|^4159 ≤ (13038937942023/100000000000000 : ℝ)^3135
        have hw : |(-2153183853/10000000000 : ℝ)|=(2153183853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386155859/10000000000 : ℝ)|^4159 ≤ (44005328508141/100000000000000 : ℝ)^3135
        have hw : |(5386155859/10000000000 : ℝ)|=(5386155859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_box_10 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289031247/10000000000 : ℝ)*x 0 + (5386155027/10000000000 : ℝ)*x 1 + (-1076592363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289031247/10000000000 : ℝ)^4159 ≤ (8591147106913/20000000000000 : ℝ)^3135 := by
    have hnat : (5289031247 : ℕ)^4159*20000000000000^3135 ≤ 8591147106913^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289031247 10000000000 8591147106913 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386155027/10000000000 : ℝ)^4159 ≤ (11001329872583/25000000000000 : ℝ)^3135 := by
    have hnat : (5386155027 : ℕ)^4159*25000000000000^3135 ≤ 11001329872583^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386155027 10000000000 11001329872583 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076592363/5000000000 : ℝ)^4159 ≤ (13038944955393/100000000000000 : ℝ)^3135 := by
    have hnat : (1076592363 : ℕ)^4159*100000000000000^3135 ≤ 13038944955393^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076592363 5000000000 13038944955393 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289031247/10000000000 : ℝ), (5386155027/10000000000 : ℝ), (-1076592363/5000000000 : ℝ)] ![(8591147106913/20000000000000 : ℝ), (11001329872583/25000000000000 : ℝ), (13038944955393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289031247/10000000000 : ℝ)|^4159 ≤ (8591147106913/20000000000000 : ℝ)^3135
        have hw : |(5289031247/10000000000 : ℝ)|=(5289031247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386155027/10000000000 : ℝ)|^4159 ≤ (11001329872583/25000000000000 : ℝ)^3135
        have hw : |(5386155027/10000000000 : ℝ)|=(5386155027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1076592363/5000000000 : ℝ)|^4159 ≤ (13038944955393/100000000000000 : ℝ)^3135
        have hw : |(-1076592363/5000000000 : ℝ)|=(1076592363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_box_11 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4496206177/10000000000 : ℝ)*x 0 + (430448979/1000000000 : ℝ)*x 1 + (538061339/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4496206177/10000000000 : ℝ)^4159 ≤ (34630098162357/100000000000000 : ℝ)^3135 := by
    have hnat : (4496206177 : ℕ)^4159*100000000000000^3135 ≤ 34630098162357^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496206177 10000000000 34630098162357 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430448979/1000000000 : ℝ)^4159 ≤ (63837785673/195312500000 : ℝ)^3135 := by
    have hnat : (430448979 : ℕ)^4159*195312500000^3135 ≤ 63837785673^3135*1000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430448979 1000000000 63837785673 195312500000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538061339/1250000000 : ℝ)^4159 ≤ (32684955552281/100000000000000 : ℝ)^3135 := by
    have hnat : (538061339 : ℕ)^4159*100000000000000^3135 ≤ 32684955552281^3135*1250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538061339 1250000000 32684955552281 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4496206177/10000000000 : ℝ), (430448979/1000000000 : ℝ), (538061339/1250000000 : ℝ)] ![(34630098162357/100000000000000 : ℝ), (63837785673/195312500000 : ℝ), (32684955552281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4496206177/10000000000 : ℝ)|^4159 ≤ (34630098162357/100000000000000 : ℝ)^3135
        have hw : |(4496206177/10000000000 : ℝ)|=(4496206177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(430448979/1000000000 : ℝ)|^4159 ≤ (63837785673/195312500000 : ℝ)^3135
        have hw : |(430448979/1000000000 : ℝ)|=(430448979/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538061339/1250000000 : ℝ)|^4159 ≤ (32684955552281/100000000000000 : ℝ)^3135
        have hw : |(538061339/1250000000 : ℝ)|=(538061339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_box_12 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1050749079/5000000000 : ℝ)*x 0 + (5440261309/10000000000 : ℝ)*x 1 + (263644589/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050749079/5000000000 : ℝ)^4159 ≤ (12625350240059/100000000000000 : ℝ)^3135 := by
    have hnat : (1050749079 : ℕ)^4159*100000000000000^3135 ≤ 12625350240059^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050749079 5000000000 12625350240059 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440261309/10000000000 : ℝ)^4159 ≤ (445927218897/1000000000000 : ℝ)^3135 := by
    have hnat : (5440261309 : ℕ)^4159*1000000000000^3135 ≤ 445927218897^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440261309 10000000000 445927218897 1000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263644589/500000000 : ℝ)^4159 ≤ (10695481964711/25000000000000 : ℝ)^3135 := by
    have hnat : (263644589 : ℕ)^4159*25000000000000^3135 ≤ 10695481964711^3135*500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263644589 500000000 10695481964711 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1050749079/5000000000 : ℝ), (5440261309/10000000000 : ℝ), (263644589/500000000 : ℝ)] ![(12625350240059/100000000000000 : ℝ), (445927218897/1000000000000 : ℝ), (10695481964711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1050749079/5000000000 : ℝ)|^4159 ≤ (12625350240059/100000000000000 : ℝ)^3135
        have hw : |(-1050749079/5000000000 : ℝ)|=(1050749079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440261309/10000000000 : ℝ)|^4159 ≤ (445927218897/1000000000000 : ℝ)^3135
        have hw : |(5440261309/10000000000 : ℝ)|=(5440261309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263644589/500000000 : ℝ)|^4159 ≤ (10695481964711/25000000000000 : ℝ)^3135
        have hw : |(263644589/500000000 : ℝ)|=(263644589/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_box_13 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684541709/5000000000 : ℝ)*x 0 + (-2197690143/10000000000 : ℝ)*x 1 + (2636446079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684541709/5000000000 : ℝ)^4159 ≤ (43820381074623/100000000000000 : ℝ)^3135 := by
    have hnat : (2684541709 : ℕ)^4159*100000000000000^3135 ≤ 43820381074623^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684541709 5000000000 43820381074623 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197690143/10000000000 : ℝ)^4159 ≤ (13397686992571/100000000000000 : ℝ)^3135 := by
    have hnat : (2197690143 : ℕ)^4159*100000000000000^3135 ≤ 13397686992571^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197690143 10000000000 13397686992571 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636446079/5000000000 : ℝ)^4159 ≤ (8556386385507/20000000000000 : ℝ)^3135 := by
    have hnat : (2636446079 : ℕ)^4159*20000000000000^3135 ≤ 8556386385507^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636446079 5000000000 8556386385507 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684541709/5000000000 : ℝ), (-2197690143/10000000000 : ℝ), (2636446079/5000000000 : ℝ)] ![(43820381074623/100000000000000 : ℝ), (13397686992571/100000000000000 : ℝ), (8556386385507/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684541709/5000000000 : ℝ)|^4159 ≤ (43820381074623/100000000000000 : ℝ)^3135
        have hw : |(2684541709/5000000000 : ℝ)|=(2684541709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2197690143/10000000000 : ℝ)|^4159 ≤ (13397686992571/100000000000000 : ℝ)^3135
        have hw : |(-2197690143/10000000000 : ℝ)|=(2197690143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636446079/5000000000 : ℝ)|^4159 ≤ (8556386385507/20000000000000 : ℝ)^3135
        have hw : |(2636446079/5000000000 : ℝ)|=(2636446079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_box_14 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369084487/10000000000 : ℝ)*x 0 + (2636445573/5000000000 : ℝ)*x 1 + (-2197690057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369084487/10000000000 : ℝ)^4159 ≤ (43820392649199/100000000000000 : ℝ)^3135 := by
    have hnat : (5369084487 : ℕ)^4159*100000000000000^3135 ≤ 43820392649199^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369084487 10000000000 43820392649199 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636445573/5000000000 : ℝ)^4159 ≤ (21390960517319/50000000000000 : ℝ)^3135 := by
    have hnat : (2636445573 : ℕ)^4159*50000000000000^3135 ≤ 21390960517319^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636445573 5000000000 21390960517319 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2197690057/10000000000 : ℝ)^4159 ≤ (6698843148523/50000000000000 : ℝ)^3135 := by
    have hnat : (2197690057 : ℕ)^4159*50000000000000^3135 ≤ 6698843148523^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197690057 10000000000 6698843148523 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369084487/10000000000 : ℝ), (2636445573/5000000000 : ℝ), (-2197690057/10000000000 : ℝ)] ![(43820392649199/100000000000000 : ℝ), (21390960517319/50000000000000 : ℝ), (6698843148523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369084487/10000000000 : ℝ)|^4159 ≤ (43820392649199/100000000000000 : ℝ)^3135
        have hw : |(5369084487/10000000000 : ℝ)|=(5369084487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636445573/5000000000 : ℝ)|^4159 ≤ (21390960517319/50000000000000 : ℝ)^3135
        have hw : |(2636445573/5000000000 : ℝ)|=(2636445573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2197690057/10000000000 : ℝ)|^4159 ≤ (6698843148523/50000000000000 : ℝ)^3135
        have hw : |(-2197690057/10000000000 : ℝ)|=(2197690057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_box_15 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4240645837/10000000000 : ℝ)*x 0 + (554033459/1250000000 : ℝ)*x 1 + (886453611/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4240645837/10000000000 : ℝ)^4159 ≤ (6408676321561/20000000000000 : ℝ)^3135 := by
    have hnat : (4240645837 : ℕ)^4159*20000000000000^3135 ≤ 6408676321561^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240645837 10000000000 6408676321561 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554033459/1250000000 : ℝ)^4159 ≤ (33978307243371/100000000000000 : ℝ)^3135 := by
    have hnat : (554033459 : ℕ)^4159*100000000000000^3135 ≤ 33978307243371^3135*1250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554033459 1250000000 33978307243371 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (886453611/2000000000 : ℝ)^4159 ≤ (33978311138537/100000000000000 : ℝ)^3135 := by
    have hnat : (886453611 : ℕ)^4159*100000000000000^3135 ≤ 33978311138537^3135*2000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886453611 2000000000 33978311138537 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4240645837/10000000000 : ℝ), (554033459/1250000000 : ℝ), (886453611/2000000000 : ℝ)] ![(6408676321561/20000000000000 : ℝ), (33978307243371/100000000000000 : ℝ), (33978311138537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4240645837/10000000000 : ℝ)|^4159 ≤ (6408676321561/20000000000000 : ℝ)^3135
        have hw : |(4240645837/10000000000 : ℝ)|=(4240645837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(554033459/1250000000 : ℝ)|^4159 ≤ (33978307243371/100000000000000 : ℝ)^3135
        have hw : |(554033459/1250000000 : ℝ)|=(554033459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(886453611/2000000000 : ℝ)|^4159 ≤ (33978311138537/100000000000000 : ℝ)^3135
        have hw : |(886453611/2000000000 : ℝ)|=(886453611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1125_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7019/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2833/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62229/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11857/20000 : ℝ) ∧ (19939/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41543/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7019/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2833/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7019/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2833/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7019/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2833/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7019/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2833/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7019/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2833/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7019/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2833/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2833/25000 : ℝ) ^ (8317/2048 : ℝ) ≤ (14437956097026111/100000000000000000000 : ℝ) := by
    have hpowers : (2833/25000 : ℝ)^8317 ≤ (14437956097026111/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2833 : ℕ)^8317*100000000000000000000^2048 ≤ 14437956097026111^2048*25000^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2833 25000 14437956097026111 100000000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2833/25000 : ℝ)) (X := (14437956097026111/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7019/50000 : ℝ) ^ (8317/2048 : ℝ) ≤ (688979959915061/2000000000000000000 : ℝ) := by
    have hpowers : (7019/50000 : ℝ)^8317 ≤ (688979959915061/2000000000000000000 : ℝ)^2048 := by
      have hnat : (7019 : ℕ)^8317*2000000000000000000^2048 ≤ 688979959915061^2048*50000^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7019 50000 688979959915061 2000000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7019/50000 : ℝ)) (X := (688979959915061/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014437956097026111/50000000000000000000 : ℝ) ≤ (10000710970704023/10000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (50014437956097026111/50000000000000000000 : ℝ)^2048 ≤ (10000710970704023/10000000000000000 : ℝ)^8317 := by
      have hnat : (50014437956097026111 : ℕ)^2048*10000000000000000^8317 ≤ 10000710970704023^8317*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014437956097026111 50000000000000000000 10000710970704023 10000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000710970704023/10000000000000000 : ℝ)) (X := (50014437956097026111/50000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048886954092779161/100000000000000000000 : ℝ) ≤ (10001203583510919/10000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (100048886954092779161/100000000000000000000 : ℝ)^2048 ≤ (10001203583510919/10000000000000000 : ℝ)^8317 := by
      have hnat : (100048886954092779161 : ℕ)^2048*10000000000000000^8317 ≤ 10001203583510919^8317*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048886954092779161 100000000000000000000 10001203583510919 10000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001203583510919/10000000000000000 : ℝ)) (X := (100048886954092779161/100000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000688979959915061/1000000000000000000 : ℝ) ≤ (2000339239263563/2000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (1000688979959915061/1000000000000000000 : ℝ)^2048 ≤ (2000339239263563/2000000000000000 : ℝ)^8317 := by
      have hnat : (1000688979959915061 : ℕ)^2048*2000000000000000^8317 ≤ 2000339239263563^8317*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000688979959915061 1000000000000000000 2000339239263563 2000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000339239263563/2000000000000000 : ℝ)) (X := (1000688979959915061/1000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14437956097026111/100000000000000000000 : ℝ) ≤ ((13525379655034797647/13530000000000000000 : ℝ)+2*(30788300431/16912500000000 : ℝ)*(2833/25000 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (13525379655034797647/13530000000000000000 : ℝ)+2*(30788300431/16912500000000 : ℝ)*(2833/25000 : ℝ)=(10000710970704023/10000000000000000 : ℝ) by norm_num, show 1+2*(14437956097026111/100000000000000000000 : ℝ)=(50014437956097026111/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(688979959915061/2000000000000000000 : ℝ)+(14437956097026111/100000000000000000000 : ℝ) ≤ ((13525379655034797647/13530000000000000000 : ℝ)+(30788300431/16912500000000 : ℝ)*((7019/50000 : ℝ)+(2833/25000 : ℝ)))^(8317/2048 : ℝ) := by
    rw [show (13525379655034797647/13530000000000000000 : ℝ)+(30788300431/16912500000000 : ℝ)*((7019/50000 : ℝ)+(2833/25000 : ℝ))=(10001203583510919/10000000000000000 : ℝ) by norm_num, show 1+(688979959915061/2000000000000000000 : ℝ)+(14437956097026111/100000000000000000000 : ℝ)=(100048886954092779161/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(688979959915061/2000000000000000000 : ℝ) ≤ ((13525379655034797647/13530000000000000000 : ℝ)+2*(30788300431/16912500000000 : ℝ)*(7019/50000 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (13525379655034797647/13530000000000000000 : ℝ)+2*(30788300431/16912500000000 : ℝ)*(7019/50000 : ℝ)=(2000339239263563/2000000000000000 : ℝ) by norm_num, show 1+2*(688979959915061/2000000000000000000 : ℝ)=(1000688979959915061/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13525379655034797647/13530000000000000000 : ℝ)*(X 1 0+X 2 0)+(30788300431/16912500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (2833/25000 : ℝ)) (hi := (7019/50000 : ℝ)) (c := (13525379655034797647/13530000000000000000 : ℝ)) (alpha := (30788300431/16912500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13525379655034797647/13530000000000000000 : ℝ)*(X 0 1+X 2 1)+(30788300431/16912500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (2833/25000 : ℝ)) (hi := (7019/50000 : ℝ)) (c := (13525379655034797647/13530000000000000000 : ℝ)) (alpha := (30788300431/16912500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13525379655034797647/13530000000000000000 : ℝ)*(X 0 2+X 1 2)+(30788300431/16912500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (2833/25000 : ℝ)) (hi := (7019/50000 : ℝ)) (c := (13525379655034797647/13530000000000000000 : ℝ)) (alpha := (30788300431/16912500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2047594167/10000000000 : ℝ)*X 0 0+(5376548969/10000000000 : ℝ)*X 0 1+(2688274331/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647911999/5000000000 : ℝ)*X 1 0+(-2157027747/10000000000 : ℝ)*X 1 1+(2688274521/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295824271/10000000000 : ℝ)*X 2 0+(2688274287/5000000000 : ℝ)*X 2 1+(-2157028011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1118699777/2500000000 : ℝ)*X 0 0+(2157666833/5000000000 : ℝ)*X 0 1+(863066991/2000000000 : ℝ)*X 0 2+(1118699777/2500000000 : ℝ)*X 1 0+(2157666833/5000000000 : ℝ)*X 1 1+(863066991/2000000000 : ℝ)*X 1 2+(1118699777/2500000000 : ℝ)*X 2 0+(2157666833/5000000000 : ℝ)*X 2 1+(863066991/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1151941593/5000000000 : ℝ)*X 0 0+(264046099/500000000 : ℝ)*X 0 1+(660115269/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363410573/10000000000 : ℝ)*X 1 0+(-1097296697/5000000000 : ℝ)*X 1 1+(1320230469/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363410427/10000000000 : ℝ)*X 2 0+(5280921859/10000000000 : ℝ)*X 2 1+(-2194593613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((425899899/1000000000 : ℝ)*X 0 0+(2211606749/5000000000 : ℝ)*X 0 1+(2211606649/5000000000 : ℝ)*X 0 2+(425899899/1000000000 : ℝ)*X 1 0+(2211606749/5000000000 : ℝ)*X 1 1+(2211606649/5000000000 : ℝ)*X 1 2+(425899899/1000000000 : ℝ)*X 2 0+(2211606749/5000000000 : ℝ)*X 2 1+(2211606649/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1125154527/5000000000 : ℝ)*X 0 0+(5215919279/10000000000 : ℝ)*X 0 1+(538615563/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289031061/10000000000 : ℝ)*X 1 0+(-2153183853/10000000000 : ℝ)*X 1 1+(5386155859/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289031247/10000000000 : ℝ)*X 2 0+(5386155027/10000000000 : ℝ)*X 2 1+(-1076592363/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4496206177/10000000000 : ℝ)*X 0 0+(430448979/1000000000 : ℝ)*X 0 1+(538061339/1250000000 : ℝ)*X 0 2+(4496206177/10000000000 : ℝ)*X 1 0+(430448979/1000000000 : ℝ)*X 1 1+(538061339/1250000000 : ℝ)*X 1 2+(4496206177/10000000000 : ℝ)*X 2 0+(430448979/1000000000 : ℝ)*X 2 1+(538061339/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1050749079/5000000000 : ℝ)*X 0 0+(5440261309/10000000000 : ℝ)*X 0 1+(263644589/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684541709/5000000000 : ℝ)*X 1 0+(-2197690143/10000000000 : ℝ)*X 1 1+(2636446079/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369084487/10000000000 : ℝ)*X 2 0+(2636445573/5000000000 : ℝ)*X 2 1+(-2197690057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4240645837/10000000000 : ℝ)*X 0 0+(554033459/1250000000 : ℝ)*X 0 1+(886453611/2000000000 : ℝ)*X 0 2+(4240645837/10000000000 : ℝ)*X 1 0+(554033459/1250000000 : ℝ)*X 1 1+(886453611/2000000000 : ℝ)*X 1 2+(4240645837/10000000000 : ℝ)*X 2 0+(554033459/1250000000 : ℝ)*X 2 1+(886453611/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62229/100000 : ℝ) ≤ (-637823136584789338249410577481/1025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41284993/50000000000000 : ℝ)*(lower0) + (44602893/100000000000000 : ℝ)*(upper1) + (73514083/50000000000000 : ℝ)*(lower4) + (390645125183947/10000000000000 : ℝ)*(major0) + (390645125183947/10000000000000 : ℝ)*(major1) + (390645125183947/10000000000000 : ℝ)*(major2) + (632171333/6250000000000 : ℝ)*(sp1) + (20604889403/100000000000000 : ℝ)*(sp2) + (639956231/20000000000000 : ℝ)*(sp3) + (1303590139129723/25000000000000 : ℝ)*(sp4) + (1042870733193211/20000000000000 : ℝ)*(sp5) + (260717158790899/5000000000000 : ℝ)*(sp6) + (1309638869507143/50000000000000 : ℝ)*(sp7) + (3224188491/100000000000000 : ℝ)*(sp12) + (1309640469397721/50000000000000 : ℝ)*(f.failure) + (5214363780707383/100000000000000 : ℝ)*(f.sum) + (3625535363921/676500000000000000000000000 : ℝ)*base65 + (504383057032727291/135300000000000000000000000000000 : ℝ)*base68 + (639900927916727291/135300000000000000000000000000000 : ℝ)*base70 + (263431643963327291/135300000000000000000000000000000 : ℝ)*base72 + (9989348686901/338250000000000000000000000 : ℝ)*base74 + (1658077724054327291/135300000000000000000000000000000 : ℝ)*base76 + (511475620497527291/135300000000000000000000000000000 : ℝ)*base78 + (2424030488883372709/135300000000000000000000000000000 : ℝ)*base79 + (104135952091/169125000000000000000000000 : ℝ)*base82 + (640777/40000000000000000000 : ℝ)*base89 + (640777/40000000000000000000 : ℝ)*base91 + (640777/40000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (11857/20000 : ℝ) ≤ (607701299627300166575474829541/1025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (244408161/100000000000000 : ℝ)*(upper0) + (8857629/12500000000000 : ℝ)*(lower1) + (27806183/50000000000000 : ℝ)*(upper2) + (397032727205833/10000000000000 : ℝ)*(major0) + (397032727205833/10000000000000 : ℝ)*(major1) + (397032727205833/10000000000000 : ℝ)*(major2) + (5258770679239809/100000000000000 : ℝ)*(sp0) + (5258756241445587/100000000000000 : ℝ)*(sp1) + (2629372547958207/50000000000000 : ℝ)*(sp2) + (2662108841929049/100000000000000 : ℝ)*(sp3) + (6440137221/25000000000000 : ℝ)*(sp5) + (1056302809/100000000000000 : ℝ)*(sp7) + (18453039029/50000000000000 : ℝ)*(sp10) + (5661377331/50000000000000 : ℝ)*(sp12) + (1331054949115929/50000000000000 : ℝ)*(f.failure) + (5258782001994471/100000000000000 : ℝ)*(f.sum) + (2787365688191/1353000000000000000000000000 : ℝ)*base66 + (528332980067974951/135300000000000000000000000000000 : ℝ)*base67 + (1107263637972025049/135300000000000000000000000000000 : ℝ)*base70 + (974571243076525049/135300000000000000000000000000000 : ℝ)*base72 + (1710137743067/54120000000000000000000000 : ℝ)*base74 + (1146554774208025049/135300000000000000000000000000000 : ℝ)*base76 + (2145838334495125049/135300000000000000000000000000000 : ℝ)*base78 + (4086115696053925049/135300000000000000000000000000000 : ℝ)*base80 + (1335221642473/1353000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (179273/40000000000000000000 : ℝ)*base89 + (179273/40000000000000000000 : ℝ)*base91 + (179273/40000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (19939/25000 : ℝ) ≤ (899277582912084086985410739/1127500000000000000000000000 : ℝ) := by norm_num
    linear_combination (563864671/100000000000000 : ℝ)*(upper0) + (48071153/50000000000000 : ℝ)*(upper2) + (14226629/50000000000000 : ℝ)*(lower3) + (714519497/100000000000000 : ℝ)*(lower5) + (1109576661703073/25000000000000 : ℝ)*(major0) + (1109576661703073/25000000000000 : ℝ)*(major1) + (1109576661703073/25000000000000 : ℝ)*(major2) + (15118736013/5000000000000 : ℝ)*(sp1) + (20577168897/20000000000000 : ℝ)*(sp3) + (12117330021/100000000000000 : ℝ)*(sp4) + (73426553526727/1250000000000 : ℝ)*(sp8) + (5873834024747921/100000000000000 : ℝ)*(sp9) + (5874136399468181/100000000000000 : ℝ)*(sp10) + (1487893913499457/50000000000000 : ℝ)*(sp11) + (1487945356421699/50000000000000 : ℝ)*(f.failure) + (5874136399468181/100000000000000 : ℝ)*(f.sum) + (9799035388091/1691250000000000000000000000 : ℝ)*base66 + (2565858787569030769/338250000000000000000000000000000 : ℝ)*base68 + (1402670360990280769/338250000000000000000000000000000 : ℝ)*base70 + (1274355521496719231/338250000000000000000000000000000 : ℝ)*base71 + (237122876210489/6765000000000000000000000000 : ℝ)*base74 + (390783883346969231/338250000000000000000000000000000 : ℝ)*base75 + (478550027562780769/338250000000000000000000000000000 : ℝ)*base78 + (31445364068219231/338250000000000000000000000000000 : ℝ)*base79 + (51558319389989/6765000000000000000000000000 : ℝ)*base82 + (120237/40000000000000000000 : ℝ)*base90 + (120237/40000000000000000000 : ℝ)*base92 + (120237/40000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-41543/50000 : ℝ) ≤ (-374707585353902664573486701/451000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17088729/100000000000000 : ℝ)*(lower0) + (325356697/100000000000000 : ℝ)*(lower1) + (37843461/10000000000000 : ℝ)*(lower2) + (111830039653219/2500000000000 : ℝ)*(major0) + (111830039653219/2500000000000 : ℝ)*(major1) + (111830039653219/2500000000000 : ℝ)*(major2) + (301583433/12500000000000 : ℝ)*(sp0) + (3101424977/2000000000000 : ℝ)*(sp5) + (306872051699/50000000000000 : ℝ)*(sp6) + (152218923109/100000000000000 : ℝ)*(sp7) + (5974807515863007/100000000000000 : ℝ)*(sp12) + (298732742864081/5000000000000 : ℝ)*(sp13) + (5974196184427073/100000000000000 : ℝ)*(sp14) + (749783899684979/25000000000000 : ℝ)*(sp15) + (187455488603939/6250000000000 : ℝ)*(f.failure) + (597480992853047/10000000000000 : ℝ)*(f.sum) + (798849689491/169125000000000000000000000 : ℝ)*base66 + (77373940431349307/33825000000000000000000000000000 : ℝ)*base68 + (19253825595874307/33825000000000000000000000000000 : ℝ)*base70 + (269941288137475693/33825000000000000000000000000000 : ℝ)*base71 + (17147999016913/676500000000000000000000000 : ℝ)*base74 + (343896010729225693/33825000000000000000000000000000 : ℝ)*base75 + (79274076245299307/33825000000000000000000000000000 : ℝ)*base78 + (385242745252825693/33825000000000000000000000000000 : ℝ)*base79 + (207296296253/270600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (33357/5000000000000000000 : ℝ)*base90 + (33357/5000000000000000000 : ℝ)*base92 + (33357/5000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1125_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7019/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2833/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11857/20000 : ℝ) else (19939/25000 : ℝ) ≤ X j i ∧ X j i ≤ (41543/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1125_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1125_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11331/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11857/20000 : ℝ) else (19939/25000 : ℝ) ≤ X j i ∧ X j i ≤ (41543/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1125_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1125_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11331/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11857/20000 : ℝ) else (19939/25000 : ℝ) ≤ X j i ∧ X j i ≤ (41543/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1125_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

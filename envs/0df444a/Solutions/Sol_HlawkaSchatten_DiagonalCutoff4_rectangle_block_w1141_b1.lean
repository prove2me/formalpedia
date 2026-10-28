-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1141_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:31:42.055738+00:00
-- url     : https://prove2.me/submissions/cda65c50-0503-4de8-9f5b-200932cb8246

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
theorem support_rectangle_w1141_s3_0 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-432709593/2000000000 : ℝ)*x 0 + (5429287443/10000000000 : ℝ)*x 1 + (1046397313/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432709593/2000000000 : ℝ)^4167 ≤ (13138976634879/100000000000000 : ℝ)^3143 := by
    have hnat : (432709593 : ℕ)^4167*100000000000000^3143 ≤ 13138976634879^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432709593 2000000000 13138976634879 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429287443/10000000000 : ℝ)^4167 ≤ (44496018923973/100000000000000 : ℝ)^3143 := by
    have hnat : (5429287443 : ℕ)^4167*100000000000000^3143 ≤ 44496018923973^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429287443 10000000000 44496018923973 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046397313/2000000000 : ℝ)^4167 ≤ (42365004427027/100000000000000 : ℝ)^3143 := by
    have hnat : (1046397313 : ℕ)^4167*100000000000000^3143 ≤ 42365004427027^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046397313 2000000000 42365004427027 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-432709593/2000000000 : ℝ), (5429287443/10000000000 : ℝ), (1046397313/2000000000 : ℝ)] ![(13138976634879/100000000000000 : ℝ), (44496018923973/100000000000000 : ℝ), (42365004427027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-432709593/2000000000 : ℝ)|^4167 ≤ (13138976634879/100000000000000 : ℝ)^3143
        have hw : |(-432709593/2000000000 : ℝ)|=(432709593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429287443/10000000000 : ℝ)|^4167 ≤ (44496018923973/100000000000000 : ℝ)^3143
        have hw : |(5429287443/10000000000 : ℝ)|=(5429287443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1046397313/2000000000 : ℝ)|^4167 ≤ (42365004427027/100000000000000 : ℝ)^3143
        have hw : |(1046397313/2000000000 : ℝ)|=(1046397313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s3_1 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26769103/50000000 : ℝ)*x 0 + (-113220189/500000000 : ℝ)*x 1 + (2615993203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26769103/50000000 : ℝ)^4167 ≤ (10919470484297/25000000000000 : ℝ)^3143 := by
    have hnat : (26769103 : ℕ)^4167*25000000000000^3143 ≤ 10919470484297^3143*50000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26769103 50000000 10919470484297 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113220189/500000000 : ℝ)^4167 ≤ (6978557661667/50000000000000 : ℝ)^3143 := by
    have hnat : (113220189 : ℕ)^4167*50000000000000^3143 ≤ 6978557661667^3143*500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113220189 500000000 6978557661667 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615993203/5000000000 : ℝ)^4167 ≤ (10591250680023/25000000000000 : ℝ)^3143 := by
    have hnat : (2615993203 : ℕ)^4167*25000000000000^3143 ≤ 10591250680023^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615993203 5000000000 10591250680023 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26769103/50000000 : ℝ), (-113220189/500000000 : ℝ), (2615993203/5000000000 : ℝ)] ![(10919470484297/25000000000000 : ℝ), (6978557661667/50000000000000 : ℝ), (10591250680023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26769103/50000000 : ℝ)|^4167 ≤ (10919470484297/25000000000000 : ℝ)^3143
        have hw : |(26769103/50000000 : ℝ)|=(26769103/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-113220189/500000000 : ℝ)|^4167 ≤ (6978557661667/50000000000000 : ℝ)^3143
        have hw : |(-113220189/500000000 : ℝ)|=(113220189/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615993203/5000000000 : ℝ)|^4167 ≤ (10591250680023/25000000000000 : ℝ)^3143
        have hw : |(2615993203/5000000000 : ℝ)|=(2615993203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s3_2 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353820683/10000000000 : ℝ)*x 0 + (2615993243/5000000000 : ℝ)*x 1 + (-1132201783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353820683/10000000000 : ℝ)^4167 ≤ (43677882834937/100000000000000 : ℝ)^3143 := by
    have hnat : (5353820683 : ℕ)^4167*100000000000000^3143 ≤ 43677882834937^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353820683 10000000000 43677882834937 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2615993243/5000000000 : ℝ)^4167 ≤ (42365003578927/100000000000000 : ℝ)^3143 := by
    have hnat : (2615993243 : ℕ)^4167*100000000000000^3143 ≤ 42365003578927^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615993243 5000000000 42365003578927 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132201783/5000000000 : ℝ)^4167 ≤ (3489278393639/25000000000000 : ℝ)^3143 := by
    have hnat : (1132201783 : ℕ)^4167*25000000000000^3143 ≤ 3489278393639^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132201783 5000000000 3489278393639 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353820683/10000000000 : ℝ), (2615993243/5000000000 : ℝ), (-1132201783/5000000000 : ℝ)] ![(43677882834937/100000000000000 : ℝ), (42365003578927/100000000000000 : ℝ), (3489278393639/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353820683/10000000000 : ℝ)|^4167 ≤ (43677882834937/100000000000000 : ℝ)^3143
        have hw : |(5353820683/10000000000 : ℝ)|=(5353820683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2615993243/5000000000 : ℝ)|^4167 ≤ (42365003578927/100000000000000 : ℝ)^3143
        have hw : |(2615993243/5000000000 : ℝ)|=(2615993243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1132201783/5000000000 : ℝ)|^4167 ≤ (3489278393639/25000000000000 : ℝ)^3143
        have hw : |(-1132201783/5000000000 : ℝ)|=(1132201783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s3_3 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4362549679/10000000000 : ℝ)*x 0 + (4170712101/10000000000 : ℝ)*x 1 + (4563159849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362549679/10000000000 : ℝ)^4167 ≤ (33294046993153/100000000000000 : ℝ)^3143 := by
    have hnat : (4362549679 : ℕ)^4167*100000000000000^3143 ≤ 33294046993153^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362549679 10000000000 33294046993153 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170712101/10000000000 : ℝ)^4167 ≤ (3136703137311/10000000000000 : ℝ)^3143 := by
    have hnat : (4170712101 : ℕ)^4167*10000000000000^3143 ≤ 3136703137311^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170712101 10000000000 3136703137311 10000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4563159849/10000000000 : ℝ)^4167 ≤ (17669460810489/50000000000000 : ℝ)^3143 := by
    have hnat : (4563159849 : ℕ)^4167*50000000000000^3143 ≤ 17669460810489^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4563159849 10000000000 17669460810489 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362549679/10000000000 : ℝ), (4170712101/10000000000 : ℝ), (4563159849/10000000000 : ℝ)] ![(33294046993153/100000000000000 : ℝ), (3136703137311/10000000000000 : ℝ), (17669460810489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362549679/10000000000 : ℝ)|^4167 ≤ (33294046993153/100000000000000 : ℝ)^3143
        have hw : |(4362549679/10000000000 : ℝ)|=(4362549679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170712101/10000000000 : ℝ)|^4167 ≤ (3136703137311/10000000000000 : ℝ)^3143
        have hw : |(4170712101/10000000000 : ℝ)|=(4170712101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4563159849/10000000000 : ℝ)|^4167 ≤ (17669460810489/50000000000000 : ℝ)^3143
        have hw : |(4563159849/10000000000 : ℝ)|=(4563159849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s3_4 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1081783047/5000000000 : ℝ)*x 0 + (81761763/156250000 : ℝ)*x 1 + (5428516893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081783047/5000000000 : ℝ)^4167 ≤ (6569561299913/50000000000000 : ℝ)^3143 := by
    have hnat : (1081783047 : ℕ)^4167*50000000000000^3143 ≤ 6569561299913^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081783047 5000000000 6569561299913 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81761763/156250000 : ℝ)^4167 ≤ (21186615417457/50000000000000 : ℝ)^3143 := by
    have hnat : (81761763 : ℕ)^4167*50000000000000^3143 ≤ 21186615417457^3143*156250000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81761763 156250000 21186615417457 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428516893/10000000000 : ℝ)^4167 ≤ (44487646557613/100000000000000 : ℝ)^3143 := by
    have hnat : (5428516893 : ℕ)^4167*100000000000000^3143 ≤ 44487646557613^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428516893 10000000000 44487646557613 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1081783047/5000000000 : ℝ), (81761763/156250000 : ℝ), (5428516893/10000000000 : ℝ)] ![(6569561299913/50000000000000 : ℝ), (21186615417457/50000000000000 : ℝ), (44487646557613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1081783047/5000000000 : ℝ)|^4167 ≤ (6569561299913/50000000000000 : ℝ)^3143
        have hw : |(-1081783047/5000000000 : ℝ)|=(1081783047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81761763/156250000 : ℝ)|^4167 ≤ (21186615417457/50000000000000 : ℝ)^3143
        have hw : |(81761763/156250000 : ℝ)|=(81761763/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428516893/10000000000 : ℝ)|^4167 ≤ (44487646557613/100000000000000 : ℝ)^3143
        have hw : |(5428516893/10000000000 : ℝ)|=(5428516893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s3_5 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303838853/10000000000 : ℝ)*x 0 + (-2067873203/10000000000 : ℝ)*x 1 + (542851703/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303838853/10000000000 : ℝ)^4167 ≤ (21569045285283/50000000000000 : ℝ)^3143 := by
    have hnat : (5303838853 : ℕ)^4167*50000000000000^3143 ≤ 21569045285283^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303838853 10000000000 21569045285283 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2067873203/10000000000 : ℝ)^4167 ≤ (2474852275623/20000000000000 : ℝ)^3143 := by
    have hnat : (2067873203 : ℕ)^4167*20000000000000^3143 ≤ 2474852275623^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067873203 10000000000 2474852275623 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542851703/1000000000 : ℝ)^4167 ≤ (695119500721/1562500000000 : ℝ)^3143 := by
    have hnat : (542851703 : ℕ)^4167*1562500000000^3143 ≤ 695119500721^3143*1000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542851703 1000000000 695119500721 1562500000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303838853/10000000000 : ℝ), (-2067873203/10000000000 : ℝ), (542851703/1000000000 : ℝ)] ![(21569045285283/50000000000000 : ℝ), (2474852275623/20000000000000 : ℝ), (695119500721/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303838853/10000000000 : ℝ)|^4167 ≤ (21569045285283/50000000000000 : ℝ)^3143
        have hw : |(5303838853/10000000000 : ℝ)|=(5303838853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2067873203/10000000000 : ℝ)|^4167 ≤ (2474852275623/20000000000000 : ℝ)^3143
        have hw : |(-2067873203/10000000000 : ℝ)|=(2067873203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542851703/1000000000 : ℝ)|^4167 ≤ (695119500721/1562500000000 : ℝ)^3143
        have hw : |(542851703/1000000000 : ℝ)|=(542851703/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s3_6 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303838741/10000000000 : ℝ)*x 0 + (5428517209/10000000000 : ℝ)*x 1 + (-516968277/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303838741/10000000000 : ℝ)^4167 ≤ (21569044681421/50000000000000 : ℝ)^3143 := by
    have hnat : (5303838741 : ℕ)^4167*50000000000000^3143 ≤ 21569044681421^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303838741 10000000000 21569044681421 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428517209/10000000000 : ℝ)^4167 ≤ (44487649991013/100000000000000 : ℝ)^3143 := by
    have hnat : (5428517209 : ℕ)^4167*100000000000000^3143 ≤ 44487649991013^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428517209 10000000000 44487649991013 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516968277/2500000000 : ℝ)^4167 ≤ (386695644513/3125000000000 : ℝ)^3143 := by
    have hnat : (516968277 : ℕ)^4167*3125000000000^3143 ≤ 386695644513^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516968277 2500000000 386695644513 3125000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303838741/10000000000 : ℝ), (5428517209/10000000000 : ℝ), (-516968277/2500000000 : ℝ)] ![(21569044681421/50000000000000 : ℝ), (44487649991013/100000000000000 : ℝ), (386695644513/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303838741/10000000000 : ℝ)|^4167 ≤ (21569044681421/50000000000000 : ℝ)^3143
        have hw : |(5303838741/10000000000 : ℝ)|=(5303838741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428517209/10000000000 : ℝ)|^4167 ≤ (44487649991013/100000000000000 : ℝ)^3143
        have hw : |(5428517209/10000000000 : ℝ)|=(5428517209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-516968277/2500000000 : ℝ)|^4167 ≤ (386695644513/3125000000000 : ℝ)^3143
        have hw : |(-516968277/2500000000 : ℝ)|=(516968277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s3_7 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (218129287/500000000 : ℝ)*x 0 + (4561635981/10000000000 : ℝ)*x 1 + (4172244507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218129287/500000000 : ℝ)^4167 ≤ (33294411867787/100000000000000 : ℝ)^3143 := by
    have hnat : (218129287 : ℕ)^4167*100000000000000^3143 ≤ 33294411867787^3143*500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218129287 500000000 33294411867787 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4561635981/10000000000 : ℝ)^4167 ≤ (1412931043393/4000000000000 : ℝ)^3143 := by
    have hnat : (4561635981 : ℕ)^4167*4000000000000^3143 ≤ 1412931043393^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4561635981 10000000000 1412931043393 4000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172244507/10000000000 : ℝ)^4167 ≤ (7845578008699/25000000000000 : ℝ)^3143 := by
    have hnat : (4172244507 : ℕ)^4167*25000000000000^3143 ≤ 7845578008699^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172244507 10000000000 7845578008699 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218129287/500000000 : ℝ), (4561635981/10000000000 : ℝ), (4172244507/10000000000 : ℝ)] ![(33294411867787/100000000000000 : ℝ), (1412931043393/4000000000000 : ℝ), (7845578008699/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218129287/500000000 : ℝ)|^4167 ≤ (33294411867787/100000000000000 : ℝ)^3143
        have hw : |(218129287/500000000 : ℝ)|=(218129287/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4561635981/10000000000 : ℝ)|^4167 ≤ (1412931043393/4000000000000 : ℝ)^3143
        have hw : |(4561635981/10000000000 : ℝ)|=(4561635981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172244507/10000000000 : ℝ)|^4167 ≤ (7845578008699/25000000000000 : ℝ)^3143
        have hw : |(4172244507/10000000000 : ℝ)|=(4172244507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1141_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8253/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4533/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1329/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14807/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8253/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4533/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8253/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4533/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8253/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4533/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8253/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4533/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8253/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4533/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8253/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4533/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4533/50000 : ℝ) ^ (8333/2048 : ℝ) ≤ (2863211163942731/50000000000000000000 : ℝ) := by
    have hpowers : (4533/50000 : ℝ)^8333 ≤ (2863211163942731/50000000000000000000 : ℝ)^2048 := by
      have hnat : (4533 : ℕ)^8333*50000000000000000000^2048 ≤ 2863211163942731^2048*50000^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4533 50000 2863211163942731 50000000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4533/50000 : ℝ)) (X := (2863211163942731/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8253/50000 : ℝ) ^ (8333/2048 : ℝ) ≤ (65569796752771329/100000000000000000000 : ℝ) := by
    have hpowers : (8253/50000 : ℝ)^8333 ≤ (65569796752771329/100000000000000000000 : ℝ)^2048 := by
      have hnat : (8253 : ℕ)^8333*100000000000000000000^2048 ≤ 65569796752771329^2048*50000^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8253 50000 65569796752771329 100000000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8253/50000 : ℝ)) (X := (65569796752771329/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002863211163942731/25000000000000000000 : ℝ) ≤ (10000281464213051/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (25002863211163942731/25000000000000000000 : ℝ)^2048 ≤ (10000281464213051/10000000000000000 : ℝ)^8333 := by
      have hnat : (25002863211163942731 : ℕ)^2048*10000000000000000^8333 ≤ 10000281464213051^8333*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002863211163942731 25000000000000000000 10000281464213051 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000281464213051/10000000000000000 : ℝ)) (X := (25002863211163942731/25000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100071296219080656791/100000000000000000000 : ℝ) ≤ (2000350355008403/2000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (100071296219080656791/100000000000000000000 : ℝ)^2048 ≤ (2000350355008403/2000000000000000 : ℝ)^8333 := by
      have hnat : (100071296219080656791 : ℕ)^2048*2000000000000000^8333 ≤ 2000350355008403^8333*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100071296219080656791 100000000000000000000 2000350355008403 2000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000350355008403/2000000000000000 : ℝ)) (X := (100071296219080656791/100000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50065569796752771329/50000000000000000000 : ℝ) ≤ (10003222085870979/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (50065569796752771329/50000000000000000000 : ℝ)^2048 ≤ (10003222085870979/10000000000000000 : ℝ)^8333 := by
      have hnat : (50065569796752771329 : ℕ)^2048*10000000000000000^8333 ≤ 10003222085870979^8333*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50065569796752771329 50000000000000000000 10003222085870979 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003222085870979/10000000000000000 : ℝ)) (X := (50065569796752771329/50000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2863211163942731/50000000000000000000 : ℝ) ≤ ((774744108518690877/775000000000000000 : ℝ)+2*(367577707241/186000000000000 : ℝ)*(4533/50000 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (774744108518690877/775000000000000000 : ℝ)+2*(367577707241/186000000000000 : ℝ)*(4533/50000 : ℝ)=(10000281464213051/10000000000000000 : ℝ) by norm_num, show 1+2*(2863211163942731/50000000000000000000 : ℝ)=(25002863211163942731/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(65569796752771329/100000000000000000000 : ℝ)+(2863211163942731/50000000000000000000 : ℝ) ≤ ((774744108518690877/775000000000000000 : ℝ)+(367577707241/186000000000000 : ℝ)*((8253/50000 : ℝ)+(4533/50000 : ℝ)))^(8333/2048 : ℝ) := by
    rw [show (774744108518690877/775000000000000000 : ℝ)+(367577707241/186000000000000 : ℝ)*((8253/50000 : ℝ)+(4533/50000 : ℝ))=(2000350355008403/2000000000000000 : ℝ) by norm_num, show 1+(65569796752771329/100000000000000000000 : ℝ)+(2863211163942731/50000000000000000000 : ℝ)=(100071296219080656791/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(65569796752771329/100000000000000000000 : ℝ) ≤ ((774744108518690877/775000000000000000 : ℝ)+2*(367577707241/186000000000000 : ℝ)*(8253/50000 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (774744108518690877/775000000000000000 : ℝ)+2*(367577707241/186000000000000 : ℝ)*(8253/50000 : ℝ)=(10003222085870979/10000000000000000 : ℝ) by norm_num, show 1+2*(65569796752771329/100000000000000000000 : ℝ)=(50065569796752771329/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (774744108518690877/775000000000000000 : ℝ)*(X 1 0+X 2 0)+(367577707241/186000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (4533/50000 : ℝ)) (hi := (8253/50000 : ℝ)) (c := (774744108518690877/775000000000000000 : ℝ)) (alpha := (367577707241/186000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (774744108518690877/775000000000000000 : ℝ)*(X 0 1+X 2 1)+(367577707241/186000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (4533/50000 : ℝ)) (hi := (8253/50000 : ℝ)) (c := (774744108518690877/775000000000000000 : ℝ)) (alpha := (367577707241/186000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (774744108518690877/775000000000000000 : ℝ)*(X 0 2+X 1 2)+(367577707241/186000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (4533/50000 : ℝ)) (hi := (8253/50000 : ℝ)) (c := (774744108518690877/775000000000000000 : ℝ)) (alpha := (367577707241/186000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-432709593/2000000000 : ℝ)*X 0 0+(5429287443/10000000000 : ℝ)*X 0 1+(1046397313/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((26769103/50000000 : ℝ)*X 1 0+(-113220189/500000000 : ℝ)*X 1 1+(2615993203/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353820683/10000000000 : ℝ)*X 2 0+(2615993243/5000000000 : ℝ)*X 2 1+(-1132201783/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362549679/10000000000 : ℝ)*X 0 0+(4170712101/10000000000 : ℝ)*X 0 1+(4563159849/10000000000 : ℝ)*X 0 2+(4362549679/10000000000 : ℝ)*X 1 0+(4170712101/10000000000 : ℝ)*X 1 1+(4563159849/10000000000 : ℝ)*X 1 2+(4362549679/10000000000 : ℝ)*X 2 0+(4170712101/10000000000 : ℝ)*X 2 1+(4563159849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1081783047/5000000000 : ℝ)*X 0 0+(81761763/156250000 : ℝ)*X 0 1+(5428516893/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303838853/10000000000 : ℝ)*X 1 0+(-2067873203/10000000000 : ℝ)*X 1 1+(542851703/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303838741/10000000000 : ℝ)*X 2 0+(5428517209/10000000000 : ℝ)*X 2 1+(-516968277/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((218129287/500000000 : ℝ)*X 0 0+(4561635981/10000000000 : ℝ)*X 0 1+(4172244507/10000000000 : ℝ)*X 0 2+(218129287/500000000 : ℝ)*X 1 0+(4561635981/10000000000 : ℝ)*X 1 1+(4172244507/10000000000 : ℝ)*X 1 2+(218129287/500000000 : ℝ)*X 2 0+(4561635981/10000000000 : ℝ)*X 2 1+(4172244507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9062019095082427542121821/1937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1299701143/100000000000000 : ℝ)*(base19) + (1235692051/100000000000000 : ℝ)*(base23) + (76337403/100000000000000 : ℝ)*(lower2) + (45470733/100000000000000 : ℝ)*(upper3) + (178317559/100000000000000 : ℝ)*(upper5) + (1904143869067411/50000000000000 : ℝ)*(major0) + (1904143869067411/50000000000000 : ℝ)*(major1) + (476035967266853/12500000000000 : ℝ)*(major2) + (2534209931307881/50000000000000 : ℝ)*(sp0) + (5068443680679881/100000000000000 : ℝ)*(sp1) + (5068443744688973/100000000000000 : ℝ)*(sp2) + (637030146907171/25000000000000 : ℝ)*(sp3) + (12558882631/50000000000000 : ℝ)*(sp4) + (9752354223/100000000000000 : ℝ)*(sp7) + (1274065169991453/50000000000000 : ℝ)*(f.failure) + (158388905636907/3125000000000 : ℝ)*(f.sum) + (9239090473981/3100000000000000000000000000 : ℝ)*base65 + (998418633521471659/116250000000000000000000000000000 : ℝ)*base68 + (34500175169886059/14531250000000000000000000000000 : ℝ)*base69 + (571492793880221659/116250000000000000000000000000000 : ℝ)*base72 + (17927856149919/3100000000000000000000000000 : ℝ)*base74 + (172359754127698559/14531250000000000000000000000000 : ℝ)*base75 + (128069310454484159/116250000000000000000000000000000 : ℝ)*base78 + (2282579467991984159/116250000000000000000000000000000 : ℝ)*base80 + (23895816551299/4650000000000000000000000000 : ℝ)*base82 + (4978241/5000000000000000000000 : ℝ)*base89 + (4978241/5000000000000000000000 : ℝ)*base91 + (95021759/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (136868731355531488010051409/19375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1337575237/100000000000000 : ℝ)*(base19) + (1474045103/100000000000000 : ℝ)*(base23) + (96511349/50000000000000 : ℝ)*(upper3) + (94127557/100000000000000 : ℝ)*(lower4) + (62460139/50000000000000 : ℝ)*(upper5) + (1919073927543387/50000000000000 : ℝ)*(major0) + (1919073927543387/50000000000000 : ℝ)*(major1) + (1919073927543387/50000000000000 : ℝ)*(major2) + (24852599419/100000000000000 : ℝ)*(sp1) + (15974084963/50000000000000 : ℝ)*(sp2) + (1021637138229597/20000000000000 : ℝ)*(sp4) + (5108159500973329/100000000000000 : ℝ)*(sp5) + (5108152268932957/100000000000000 : ℝ)*(sp6) + (160506861472029/6250000000000 : ℝ)*(sp7) + (160506861472029/6250000000000 : ℝ)*(f.failure) + (1021637138229597/20000000000000 : ℝ)*(f.sum) + (4493052438411/1550000000000000000000000000 : ℝ)*base66 + (767451443267192899/38750000000000000000000000000000 : ℝ)*base67 + (612045531243442899/38750000000000000000000000000000 : ℝ)*base69 + (366745610163442899/38750000000000000000000000000000 : ℝ)*base71 + (2619032960739/1550000000000000000000000000 : ℝ)*base73 + (422620791557192899/38750000000000000000000000000000 : ℝ)*base75 + (164141872290942899/38750000000000000000000000000000 : ℝ)*base77 + (280537019018442899/38750000000000000000000000000000 : ℝ)*base79 + (4929558752289/1550000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (5344287/625000000000000000000 : ℝ)*base90 + (5344287/625000000000000000000 : ℝ)*base92 + (5344287/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1141_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8253/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4533/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1329/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14807/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1141_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1141_s4_0 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-67705009/312500000 : ℝ)*x 0 + (216077679/400000000 : ℝ)*x 1 + (5257361343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67705009/312500000 : ℝ)^4167 ≤ (13163235703879/100000000000000 : ℝ)^3143 := by
    have hnat : (67705009 : ℕ)^4167*100000000000000^3143 ≤ 13163235703879^3143*312500000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67705009 312500000 13163235703879 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216077679/400000000 : ℝ)^4167 ≤ (44199135520467/100000000000000 : ℝ)^3143 := by
    have hnat : (216077679 : ℕ)^4167*100000000000000^3143 ≤ 44199135520467^3143*400000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216077679 400000000 44199135520467 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5257361343/10000000000 : ℝ)^4167 ≤ (21318814380631/50000000000000 : ℝ)^3143 := by
    have hnat : (5257361343 : ℕ)^4167*50000000000000^3143 ≤ 21318814380631^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257361343 10000000000 21318814380631 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67705009/312500000 : ℝ), (216077679/400000000 : ℝ), (5257361343/10000000000 : ℝ)] ![(13163235703879/100000000000000 : ℝ), (44199135520467/100000000000000 : ℝ), (21318814380631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67705009/312500000 : ℝ)|^4167 ≤ (13163235703879/100000000000000 : ℝ)^3143
        have hw : |(-67705009/312500000 : ℝ)|=(67705009/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216077679/400000000 : ℝ)|^4167 ≤ (44199135520467/100000000000000 : ℝ)^3143
        have hw : |(216077679/400000000 : ℝ)|=(216077679/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5257361343/10000000000 : ℝ)|^4167 ≤ (21318814380631/50000000000000 : ℝ)^3143
        have hw : |(5257361343/10000000000 : ℝ)|=(5257361343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s4_1 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668373901/1250000000 : ℝ)*x 0 + (-2240036107/10000000000 : ℝ)*x 1 + (1314340483/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668373901/1250000000 : ℝ)^4167 ≤ (43604028853237/100000000000000 : ℝ)^3143 := by
    have hnat : (668373901 : ℕ)^4167*100000000000000^3143 ≤ 43604028853237^3143*1250000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668373901 1250000000 43604028853237 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2240036107/10000000000 : ℝ)^4167 ≤ (13758336036827/100000000000000 : ℝ)^3143 := by
    have hnat : (2240036107 : ℕ)^4167*100000000000000^3143 ≤ 13758336036827^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240036107 10000000000 13758336036827 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314340483/2500000000 : ℝ)^4167 ≤ (4263763509441/10000000000000 : ℝ)^3143 := by
    have hnat : (1314340483 : ℕ)^4167*10000000000000^3143 ≤ 4263763509441^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314340483 2500000000 4263763509441 10000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668373901/1250000000 : ℝ), (-2240036107/10000000000 : ℝ), (1314340483/2500000000 : ℝ)] ![(43604028853237/100000000000000 : ℝ), (13758336036827/100000000000000 : ℝ), (4263763509441/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668373901/1250000000 : ℝ)|^4167 ≤ (43604028853237/100000000000000 : ℝ)^3143
        have hw : |(668373901/1250000000 : ℝ)|=(668373901/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2240036107/10000000000 : ℝ)|^4167 ≤ (13758336036827/100000000000000 : ℝ)^3143
        have hw : |(-2240036107/10000000000 : ℝ)|=(2240036107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1314340483/2500000000 : ℝ)|^4167 ≤ (4263763509441/10000000000000 : ℝ)^3143
        have hw : |(1314340483/2500000000 : ℝ)|=(1314340483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s4_2 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346991661/10000000000 : ℝ)*x 0 + (5257360997/10000000000 : ℝ)*x 1 + (-2240036741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346991661/10000000000 : ℝ)^4167 ≤ (43604033750963/100000000000000 : ℝ)^3143 := by
    have hnat : (5346991661 : ℕ)^4167*100000000000000^3143 ≤ 43604033750963^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346991661 10000000000 43604033750963 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5257360997/10000000000 : ℝ)^4167 ≤ (42637625040941/100000000000000 : ℝ)^3143 := by
    have hnat : (5257360997 : ℕ)^4167*100000000000000^3143 ≤ 42637625040941^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257360997 10000000000 42637625040941 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2240036741/10000000000 : ℝ)^4167 ≤ (3439585299889/25000000000000 : ℝ)^3143 := by
    have hnat : (2240036741 : ℕ)^4167*25000000000000^3143 ≤ 3439585299889^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240036741 10000000000 3439585299889 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346991661/10000000000 : ℝ), (5257360997/10000000000 : ℝ), (-2240036741/10000000000 : ℝ)] ![(43604033750963/100000000000000 : ℝ), (42637625040941/100000000000000 : ℝ), (3439585299889/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346991661/10000000000 : ℝ)|^4167 ≤ (43604033750963/100000000000000 : ℝ)^3143
        have hw : |(5346991661/10000000000 : ℝ)|=(5346991661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5257360997/10000000000 : ℝ)|^4167 ≤ (42637625040941/100000000000000 : ℝ)^3143
        have hw : |(5257360997/10000000000 : ℝ)|=(5257360997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2240036741/10000000000 : ℝ)|^4167 ≤ (3439585299889/25000000000000 : ℝ)^3143
        have hw : |(-2240036741/10000000000 : ℝ)|=(2240036741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s4_3 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2182173353/5000000000 : ℝ)*x 0 + (211145509/500000000 : ℝ)*x 1 + (451049559/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182173353/5000000000 : ℝ)^4167 ≤ (16656115489047/50000000000000 : ℝ)^3143 := by
    have hnat : (2182173353 : ℕ)^4167*50000000000000^3143 ≤ 16656115489047^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182173353 5000000000 16656115489047 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211145509/500000000 : ℝ)^4167 ≤ (31888560900881/100000000000000 : ℝ)^3143 := by
    have hnat : (211145509 : ℕ)^4167*100000000000000^3143 ≤ 31888560900881^3143*500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211145509 500000000 31888560900881 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451049559/1000000000 : ℝ)^4167 ≤ (4349901012301/12500000000000 : ℝ)^3143 := by
    have hnat : (451049559 : ℕ)^4167*12500000000000^3143 ≤ 4349901012301^3143*1000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451049559 1000000000 4349901012301 12500000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182173353/5000000000 : ℝ), (211145509/500000000 : ℝ), (451049559/1000000000 : ℝ)] ![(16656115489047/50000000000000 : ℝ), (31888560900881/100000000000000 : ℝ), (4349901012301/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182173353/5000000000 : ℝ)|^4167 ≤ (16656115489047/50000000000000 : ℝ)^3143
        have hw : |(2182173353/5000000000 : ℝ)|=(2182173353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211145509/500000000 : ℝ)|^4167 ≤ (31888560900881/100000000000000 : ℝ)^3143
        have hw : |(211145509/500000000 : ℝ)|=(211145509/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(451049559/1000000000 : ℝ)|^4167 ≤ (4349901012301/12500000000000 : ℝ)^3143
        have hw : |(451049559/1000000000 : ℝ)|=(451049559/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s4_4 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1083284041/5000000000 : ℝ)*x 0 + (2628886399/5000000000 : ℝ)*x 1 + (5401528343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083284041/5000000000 : ℝ)^4167 ≤ (105306387883/800000000000 : ℝ)^3143 := by
    have hnat : (1083284041 : ℕ)^4167*800000000000^3143 ≤ 105306387883^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083284041 5000000000 105306387883 800000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628886399/5000000000 : ℝ)^4167 ≤ (21321026467721/50000000000000 : ℝ)^3143 := by
    have hnat : (2628886399 : ℕ)^4167*50000000000000^3143 ≤ 21321026467721^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628886399 5000000000 21321026467721 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401528343/10000000000 : ℝ)^4167 ≤ (44194648565691/100000000000000 : ℝ)^3143 := by
    have hnat : (5401528343 : ℕ)^4167*100000000000000^3143 ≤ 44194648565691^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401528343 10000000000 44194648565691 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1083284041/5000000000 : ℝ), (2628886399/5000000000 : ℝ), (5401528343/10000000000 : ℝ)] ![(105306387883/800000000000 : ℝ), (21321026467721/50000000000000 : ℝ), (44194648565691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1083284041/5000000000 : ℝ)|^4167 ≤ (105306387883/800000000000 : ℝ)^3143
        have hw : |(-1083284041/5000000000 : ℝ)|=(1083284041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628886399/5000000000 : ℝ)|^4167 ≤ (21321026467721/50000000000000 : ℝ)^3143
        have hw : |(2628886399/5000000000 : ℝ)|=(2628886399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401528343/10000000000 : ℝ)|^4167 ≤ (44194648565691/100000000000000 : ℝ)^3143
        have hw : |(5401528343/10000000000 : ℝ)|=(5401528343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s4_5 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655183281/5000000000 : ℝ)*x 0 + (-523967171/2500000000 : ℝ)*x 1 + (2700764171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655183281/5000000000 : ℝ)^4167 ≤ (43208494604281/100000000000000 : ℝ)^3143 := by
    have hnat : (2655183281 : ℕ)^4167*100000000000000^3143 ≤ 43208494604281^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655183281 5000000000 43208494604281 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523967171/2500000000 : ℝ)^4167 ≤ (6298428414629/50000000000000 : ℝ)^3143 := by
    have hnat : (523967171 : ℕ)^4167*50000000000000^3143 ≤ 6298428414629^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523967171 2500000000 6298428414629 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700764171/5000000000 : ℝ)^4167 ≤ (44194648554843/100000000000000 : ℝ)^3143 := by
    have hnat : (2700764171 : ℕ)^4167*100000000000000^3143 ≤ 44194648554843^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700764171 5000000000 44194648554843 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655183281/5000000000 : ℝ), (-523967171/2500000000 : ℝ), (2700764171/5000000000 : ℝ)] ![(43208494604281/100000000000000 : ℝ), (6298428414629/50000000000000 : ℝ), (44194648554843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655183281/5000000000 : ℝ)|^4167 ≤ (43208494604281/100000000000000 : ℝ)^3143
        have hw : |(2655183281/5000000000 : ℝ)|=(2655183281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-523967171/2500000000 : ℝ)|^4167 ≤ (6298428414629/50000000000000 : ℝ)^3143
        have hw : |(-523967171/2500000000 : ℝ)|=(523967171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700764171/5000000000 : ℝ)|^4167 ≤ (44194648554843/100000000000000 : ℝ)^3143
        have hw : |(2700764171/5000000000 : ℝ)|=(2700764171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s4_6 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663795829/1250000000 : ℝ)*x 0 + (1350382053/2500000000 : ℝ)*x 1 + (-1047934383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663795829/1250000000 : ℝ)^4167 ≤ (43208495359411/100000000000000 : ℝ)^3143 := by
    have hnat : (663795829 : ℕ)^4167*100000000000000^3143 ≤ 43208495359411^3143*1250000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663795829 1250000000 43208495359411 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350382053/2500000000 : ℝ)^4167 ≤ (2209732357233/5000000000000 : ℝ)^3143 := by
    have hnat : (1350382053 : ℕ)^4167*5000000000000^3143 ≤ 2209732357233^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350382053 2500000000 2209732357233 5000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047934383/5000000000 : ℝ)^4167 ≤ (3149214370669/25000000000000 : ℝ)^3143 := by
    have hnat : (1047934383 : ℕ)^4167*25000000000000^3143 ≤ 3149214370669^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047934383 5000000000 3149214370669 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663795829/1250000000 : ℝ), (1350382053/2500000000 : ℝ), (-1047934383/5000000000 : ℝ)] ![(43208495359411/100000000000000 : ℝ), (2209732357233/5000000000000 : ℝ), (3149214370669/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663795829/1250000000 : ℝ)|^4167 ≤ (43208495359411/100000000000000 : ℝ)^3143
        have hw : |(663795829/1250000000 : ℝ)|=(663795829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350382053/2500000000 : ℝ)|^4167 ≤ (2209732357233/5000000000000 : ℝ)^3143
        have hw : |(1350382053/2500000000 : ℝ)|=(1350382053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1047934383/5000000000 : ℝ)|^4167 ≤ (3149214370669/25000000000000 : ℝ)^3143
        have hw : |(-1047934383/5000000000 : ℝ)|=(1047934383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s4_7 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4364360533/10000000000 : ℝ)*x 0 + (4509675297/10000000000 : ℝ)*x 1 + (1055933561/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364360533/10000000000 : ℝ)^4167 ≤ (6662474180391/20000000000000 : ℝ)^3143 := by
    have hnat : (4364360533 : ℕ)^4167*20000000000000^3143 ≤ 6662474180391^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364360533 10000000000 6662474180391 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4509675297/10000000000 : ℝ)^4167 ≤ (34790817743021/100000000000000 : ℝ)^3143 := by
    have hnat : (4509675297 : ℕ)^4167*100000000000000^3143 ≤ 34790817743021^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509675297 10000000000 34790817743021 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055933561/2500000000 : ℝ)^4167 ≤ (15948405668847/50000000000000 : ℝ)^3143 := by
    have hnat : (1055933561 : ℕ)^4167*50000000000000^3143 ≤ 15948405668847^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055933561 2500000000 15948405668847 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364360533/10000000000 : ℝ), (4509675297/10000000000 : ℝ), (1055933561/2500000000 : ℝ)] ![(6662474180391/20000000000000 : ℝ), (34790817743021/100000000000000 : ℝ), (15948405668847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364360533/10000000000 : ℝ)|^4167 ≤ (6662474180391/20000000000000 : ℝ)^3143
        have hw : |(4364360533/10000000000 : ℝ)|=(4364360533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4509675297/10000000000 : ℝ)|^4167 ≤ (34790817743021/100000000000000 : ℝ)^3143
        have hw : |(4509675297/10000000000 : ℝ)|=(4509675297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055933561/2500000000 : ℝ)|^4167 ≤ (15948405668847/50000000000000 : ℝ)^3143
        have hw : |(1055933561/2500000000 : ℝ)|=(1055933561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1141_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14807/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1329/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11173/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14807/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1329/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14807/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1329/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14807/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1329/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14807/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1329/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14807/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1329/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14807/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1329/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1329/12500 : ℝ) ^ (8333/2048 : ℝ) ≤ (10950768389271563/100000000000000000000 : ℝ) := by
    have hpowers : (1329/12500 : ℝ)^8333 ≤ (10950768389271563/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1329 : ℕ)^8333*100000000000000000000^2048 ≤ 10950768389271563^2048*12500^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1329 12500 10950768389271563 100000000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1329/12500 : ℝ)) (X := (10950768389271563/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14807/100000 : ℝ) ^ (8333/2048 : ℝ) ≤ (42146052904113033/100000000000000000000 : ℝ) := by
    have hpowers : (14807/100000 : ℝ)^8333 ≤ (42146052904113033/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14807 : ℕ)^8333*100000000000000000000^2048 ≤ 42146052904113033^2048*100000^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14807 100000 42146052904113033 100000000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14807/100000 : ℝ)) (X := (42146052904113033/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010950768389271563/50000000000000000000 : ℝ) ≤ (10000538229246333/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (50010950768389271563/50000000000000000000 : ℝ)^2048 ≤ (10000538229246333/10000000000000000 : ℝ)^8333 := by
      have hnat : (50010950768389271563 : ℕ)^2048*10000000000000000^8333 ≤ 10000538229246333^8333*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010950768389271563 50000000000000000000 10000538229246333 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538229246333/10000000000000000 : ℝ)) (X := (50010950768389271563/50000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25013274205323346149/25000000000000000000 : ℝ) ≤ (10001304698459527/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (25013274205323346149/25000000000000000000 : ℝ)^2048 ≤ (10001304698459527/10000000000000000 : ℝ)^8333 := by
      have hnat : (25013274205323346149 : ℕ)^2048*10000000000000000^8333 ≤ 10001304698459527^8333*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013274205323346149 25000000000000000000 10001304698459527 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001304698459527/10000000000000000 : ℝ)) (X := (25013274205323346149/25000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50042146052904113033/50000000000000000000 : ℝ) ≤ (10002071167672721/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (50042146052904113033/50000000000000000000 : ℝ)^2048 ≤ (10002071167672721/10000000000000000 : ℝ)^8333 := by
      have hnat : (50042146052904113033 : ℕ)^2048*10000000000000000^8333 ≤ 10002071167672721^8333*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50042146052904113033 50000000000000000000 10002071167672721 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002071167672721/10000000000000000 : ℝ)) (X := (50042146052904113033/50000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10950768389271563/100000000000000000000 : ℝ) ≤ ((41735948905754083059/41750000000000000000 : ℝ)+2*(383234606597/208750000000000 : ℝ)*(1329/12500 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (41735948905754083059/41750000000000000000 : ℝ)+2*(383234606597/208750000000000 : ℝ)*(1329/12500 : ℝ)=(10000538229246333/10000000000000000 : ℝ) by norm_num, show 1+2*(10950768389271563/100000000000000000000 : ℝ)=(50010950768389271563/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(42146052904113033/100000000000000000000 : ℝ)+(10950768389271563/100000000000000000000 : ℝ) ≤ ((41735948905754083059/41750000000000000000 : ℝ)+(383234606597/208750000000000 : ℝ)*((14807/100000 : ℝ)+(1329/12500 : ℝ)))^(8333/2048 : ℝ) := by
    rw [show (41735948905754083059/41750000000000000000 : ℝ)+(383234606597/208750000000000 : ℝ)*((14807/100000 : ℝ)+(1329/12500 : ℝ))=(10001304698459527/10000000000000000 : ℝ) by norm_num, show 1+(42146052904113033/100000000000000000000 : ℝ)+(10950768389271563/100000000000000000000 : ℝ)=(25013274205323346149/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(42146052904113033/100000000000000000000 : ℝ) ≤ ((41735948905754083059/41750000000000000000 : ℝ)+2*(383234606597/208750000000000 : ℝ)*(14807/100000 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (41735948905754083059/41750000000000000000 : ℝ)+2*(383234606597/208750000000000 : ℝ)*(14807/100000 : ℝ)=(10002071167672721/10000000000000000 : ℝ) by norm_num, show 1+2*(42146052904113033/100000000000000000000 : ℝ)=(50042146052904113033/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41735948905754083059/41750000000000000000 : ℝ)*(X 1 0+X 2 0)+(383234606597/208750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (1329/12500 : ℝ)) (hi := (14807/100000 : ℝ)) (c := (41735948905754083059/41750000000000000000 : ℝ)) (alpha := (383234606597/208750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41735948905754083059/41750000000000000000 : ℝ)*(X 0 1+X 2 1)+(383234606597/208750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (1329/12500 : ℝ)) (hi := (14807/100000 : ℝ)) (c := (41735948905754083059/41750000000000000000 : ℝ)) (alpha := (383234606597/208750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41735948905754083059/41750000000000000000 : ℝ)*(X 0 2+X 1 2)+(383234606597/208750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (1329/12500 : ℝ)) (hi := (14807/100000 : ℝ)) (c := (41735948905754083059/41750000000000000000 : ℝ)) (alpha := (383234606597/208750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-67705009/312500000 : ℝ)*X 0 0+(216077679/400000000 : ℝ)*X 0 1+(5257361343/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668373901/1250000000 : ℝ)*X 1 0+(-2240036107/10000000000 : ℝ)*X 1 1+(1314340483/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346991661/10000000000 : ℝ)*X 2 0+(5257360997/10000000000 : ℝ)*X 2 1+(-2240036741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2182173353/5000000000 : ℝ)*X 0 0+(211145509/500000000 : ℝ)*X 0 1+(451049559/1000000000 : ℝ)*X 0 2+(2182173353/5000000000 : ℝ)*X 1 0+(211145509/500000000 : ℝ)*X 1 1+(451049559/1000000000 : ℝ)*X 1 2+(2182173353/5000000000 : ℝ)*X 2 0+(211145509/500000000 : ℝ)*X 2 1+(451049559/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1083284041/5000000000 : ℝ)*X 0 0+(2628886399/5000000000 : ℝ)*X 0 1+(5401528343/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655183281/5000000000 : ℝ)*X 1 0+(-523967171/2500000000 : ℝ)*X 1 1+(2700764171/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663795829/1250000000 : ℝ)*X 2 0+(1350382053/2500000000 : ℝ)*X 2 1+(-1047934383/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4364360533/10000000000 : ℝ)*X 0 0+(4509675297/10000000000 : ℝ)*X 0 1+(1055933561/2500000000 : ℝ)*X 0 2+(4364360533/10000000000 : ℝ)*X 1 0+(4509675297/10000000000 : ℝ)*X 1 1+(1055933561/2500000000 : ℝ)*X 1 2+(4364360533/10000000000 : ℝ)*X 2 0+(4509675297/10000000000 : ℝ)*X 2 1+(1055933561/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6615049690662162280131280203/417500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1216787177/100000000000000 : ℝ)*(base23) + (46607579/50000000000000 : ℝ)*(lower2) + (407385957/100000000000000 : ℝ)*(upper3) + (439546767/100000000000000 : ℝ)*(lower4) + (171166049/100000000000000 : ℝ)*(upper5) + (5196917193799847/100000000000000 : ℝ)*(major0) + (5196917193799847/100000000000000 : ℝ)*(major1) + (649614649224981/12500000000000 : ℝ)*(major2) + (6916569722266313/100000000000000 : ℝ)*(sp0) + (6916569722266313/100000000000000 : ℝ)*(sp1) + (6916566038006869/100000000000000 : ℝ)*(sp2) + (1738622050708831/50000000000000 : ℝ)*(sp3) + (2467472267/100000000000000 : ℝ)*(sp6) + (10017884013/50000000000000 : ℝ)*(sp7) + (434658017148211/12500000000000 : ℝ)*(f.failure) + (6916569722266313/100000000000000 : ℝ)*(f.sum) + (93015503403533/4175000000000000000000000000 : ℝ)*base65 + (71946108414064308027/4175000000000000000000000000000000 : ℝ)*base68 + (8664281015397453121/521875000000000000000000000000000 : ℝ)*base70 + (81701931479460691973/4175000000000000000000000000000000 : ℝ)*base71 + (11886922615079/2087500000000000000000000000 : ℝ)*base73 + (6793285220456828121/521875000000000000000000000000000 : ℝ)*base76 + (94644626796433708027/4175000000000000000000000000000000 : ℝ)*base78 + (17345272067233708027/4175000000000000000000000000000000 : ℝ)*base80 + (122249040042557/20875000000000000000000000000 : ℝ)*base82 + (17491567/1250000000000000000000 : ℝ)*base89 + (17491567/1250000000000000000000 : ℝ)*base91 + (4991567/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1666812691560568230598694337/521875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (659285593/50000000000000 : ℝ)*(base19) + (818072949/50000000000000 : ℝ)*(base23) + (142331669/100000000000000 : ℝ)*(upper2) + (3534939/6250000000000 : ℝ)*(upper3) + (315097243/100000000000000 : ℝ)*(upper5) + (2613370044943081/50000000000000 : ℝ)*(major0) + (2613370044943081/50000000000000 : ℝ)*(major1) + (2613370044943081/50000000000000 : ℝ)*(major2) + (9521749453/25000000000000 : ℝ)*(sp1) + (31975566421/100000000000000 : ℝ)*(sp2) + (6956261397084187/100000000000000 : ℝ)*(sp4) + (6956221991515189/100000000000000 : ℝ)*(sp5) + (1739056946342967/25000000000000 : ℝ)*(sp6) + (43715233452813/1250000000000 : ℝ)*(sp7) + (43715233452813/1250000000000 : ℝ)*(f.failure) + (6956261397084187/100000000000000 : ℝ)*(f.sum) + (26646027544339/10437500000000000000000000000 : ℝ)*base65 + (10293514524202235221/2087500000000000000000000000000000 : ℝ)*base68 + (43955495346264735221/2087500000000000000000000000000000 : ℝ)*base70 + (46536713171402235221/2087500000000000000000000000000000 : ℝ)*base72 + (28592185254107/5218750000000000000000000000 : ℝ)*base73 + (11067908295352235221/2087500000000000000000000000000000 : ℝ)*base76 + (1230762877585264779/2087500000000000000000000000000000 : ℝ)*base77 + (51494244274314735221/2087500000000000000000000000000000 : ℝ)*base80 + (162866355595697/20875000000000000000000000000 : ℝ)*base82 + (1806161/125000000000000000000 : ℝ)*base89 + (1806161/125000000000000000000 : ℝ)*base91 + (1806161/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1141_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14807/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1329/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1141_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1141_s5_0 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-54180063/250000000 : ℝ)*x 0 + (2697470557/5000000000 : ℝ)*x 1 + (657992547/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54180063/250000000 : ℝ)^4167 ≤ (13168409197401/100000000000000 : ℝ)^3143 := by
    have hnat : (54180063 : ℕ)^4167*100000000000000^3143 ≤ 13168409197401^3143*250000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54180063 250000000 13168409197401 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697470557/5000000000 : ℝ)^4167 ≤ (22061603694663/50000000000000 : ℝ)^3143 := by
    have hnat : (2697470557 : ℕ)^4167*50000000000000^3143 ≤ 22061603694663^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697470557 5000000000 22061603694663 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657992547/1250000000 : ℝ)^4167 ≤ (2135419169851/5000000000000 : ℝ)^3143 := by
    have hnat : (657992547 : ℕ)^4167*5000000000000^3143 ≤ 2135419169851^3143*1250000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657992547 1250000000 2135419169851 5000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-54180063/250000000 : ℝ), (2697470557/5000000000 : ℝ), (657992547/1250000000 : ℝ)] ![(13168409197401/100000000000000 : ℝ), (22061603694663/50000000000000 : ℝ), (2135419169851/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-54180063/250000000 : ℝ)|^4167 ≤ (13168409197401/100000000000000 : ℝ)^3143
        have hw : |(-54180063/250000000 : ℝ)|=(54180063/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697470557/5000000000 : ℝ)|^4167 ≤ (22061603694663/50000000000000 : ℝ)^3143
        have hw : |(2697470557/5000000000 : ℝ)|=(2697470557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657992547/1250000000 : ℝ)|^4167 ≤ (2135419169851/5000000000000 : ℝ)^3143
        have hw : |(657992547/1250000000 : ℝ)|=(657992547/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s5_1 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345235689/10000000000 : ℝ)*x 0 + (-1116837847/5000000000 : ℝ)*x 1 + (5263940419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345235689/10000000000 : ℝ)^4167 ≤ (21792524811987/50000000000000 : ℝ)^3143 := by
    have hnat : (5345235689 : ℕ)^4167*50000000000000^3143 ≤ 21792524811987^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345235689 10000000000 21792524811987 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1116837847/5000000000 : ℝ)^4167 ≤ (13706566500731/100000000000000 : ℝ)^3143 := by
    have hnat : (1116837847 : ℕ)^4167*100000000000000^3143 ≤ 13706566500731^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116837847 5000000000 13706566500731 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263940419/10000000000 : ℝ)^4167 ≤ (42708383859561/100000000000000 : ℝ)^3143 := by
    have hnat : (5263940419 : ℕ)^4167*100000000000000^3143 ≤ 42708383859561^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263940419 10000000000 42708383859561 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345235689/10000000000 : ℝ), (-1116837847/5000000000 : ℝ), (5263940419/10000000000 : ℝ)] ![(21792524811987/50000000000000 : ℝ), (13706566500731/100000000000000 : ℝ), (42708383859561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345235689/10000000000 : ℝ)|^4167 ≤ (21792524811987/50000000000000 : ℝ)^3143
        have hw : |(5345235689/10000000000 : ℝ)|=(5345235689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1116837847/5000000000 : ℝ)|^4167 ≤ (13706566500731/100000000000000 : ℝ)^3143
        have hw : |(-1116837847/5000000000 : ℝ)|=(1116837847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263940419/10000000000 : ℝ)|^4167 ≤ (42708383859561/100000000000000 : ℝ)^3143
        have hw : |(5263940419/10000000000 : ℝ)|=(5263940419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s5_2 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345235551/10000000000 : ℝ)*x 0 + (5263940559/10000000000 : ℝ)*x 1 + (-558418923/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345235551/10000000000 : ℝ)^4167 ≤ (43585048132111/100000000000000 : ℝ)^3143 := by
    have hnat : (5345235551 : ℕ)^4167*100000000000000^3143 ≤ 43585048132111^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345235551 10000000000 43585048132111 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263940559/10000000000 : ℝ)^4167 ≤ (42708385365507/100000000000000 : ℝ)^3143 := by
    have hnat : (5263940559 : ℕ)^4167*100000000000000^3143 ≤ 42708385365507^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263940559 10000000000 42708385365507 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (558418923/2500000000 : ℝ)^4167 ≤ (685328324223/5000000000000 : ℝ)^3143 := by
    have hnat : (558418923 : ℕ)^4167*5000000000000^3143 ≤ 685328324223^3143*2500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558418923 2500000000 685328324223 5000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345235551/10000000000 : ℝ), (5263940559/10000000000 : ℝ), (-558418923/2500000000 : ℝ)] ![(43585048132111/100000000000000 : ℝ), (42708385365507/100000000000000 : ℝ), (685328324223/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345235551/10000000000 : ℝ)|^4167 ≤ (43585048132111/100000000000000 : ℝ)^3143
        have hw : |(5345235551/10000000000 : ℝ)|=(5345235551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263940559/10000000000 : ℝ)|^4167 ≤ (42708385365507/100000000000000 : ℝ)^3143
        have hw : |(5263940559/10000000000 : ℝ)|=(5263940559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-558418923/2500000000 : ℝ)|^4167 ≤ (685328324223/5000000000000 : ℝ)^3143
        have hw : |(-558418923/2500000000 : ℝ)|=(558418923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s5_3 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4364719413/10000000000 : ℝ)*x 0 + (211818457/500000000 : ℝ)*x 1 + (4496940237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364719413/10000000000 : ℝ)^4167 ≤ (8329000669619/25000000000000 : ℝ)^3143 := by
    have hnat : (4364719413 : ℕ)^4167*25000000000000^3143 ≤ 8329000669619^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364719413 10000000000 8329000669619 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211818457/500000000 : ℝ)^4167 ≤ (16011688065773/50000000000000 : ℝ)^3143 := by
    have hnat : (211818457 : ℕ)^4167*50000000000000^3143 ≤ 16011688065773^3143*500000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211818457 500000000 16011688065773 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4496940237/10000000000 : ℝ)^4167 ≤ (34660621180141/100000000000000 : ℝ)^3143 := by
    have hnat : (4496940237 : ℕ)^4167*100000000000000^3143 ≤ 34660621180141^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496940237 10000000000 34660621180141 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364719413/10000000000 : ℝ), (211818457/500000000 : ℝ), (4496940237/10000000000 : ℝ)] ![(8329000669619/25000000000000 : ℝ), (16011688065773/50000000000000 : ℝ), (34660621180141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364719413/10000000000 : ℝ)|^4167 ≤ (8329000669619/25000000000000 : ℝ)^3143
        have hw : |(4364719413/10000000000 : ℝ)|=(4364719413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211818457/500000000 : ℝ)|^4167 ≤ (16011688065773/50000000000000 : ℝ)^3143
        have hw : |(211818457/500000000 : ℝ)|=(211818457/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4496940237/10000000000 : ℝ)|^4167 ≤ (34660621180141/100000000000000 : ℝ)^3143
        have hw : |(4496940237/10000000000 : ℝ)|=(4496940237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s5_4 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1083603833/5000000000 : ℝ)*x 0 + (5264279319/10000000000 : ℝ)*x 1 + (1078920209/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083603833/5000000000 : ℝ)^4167 ≤ (13168450652971/100000000000000 : ℝ)^3143 := by
    have hnat : (1083603833 : ℕ)^4167*100000000000000^3143 ≤ 13168450652971^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083603833 5000000000 13168450652971 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264279319/10000000000 : ℝ)^4167 ≤ (10678007340547/25000000000000 : ℝ)^3143 := by
    have hnat : (5264279319 : ℕ)^4167*25000000000000^3143 ≤ 10678007340547^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264279319 10000000000 10678007340547 25000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078920209/2000000000 : ℝ)^4167 ≤ (8823903994777/20000000000000 : ℝ)^3143 := by
    have hnat : (1078920209 : ℕ)^4167*20000000000000^3143 ≤ 8823903994777^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078920209 2000000000 8823903994777 20000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1083603833/5000000000 : ℝ), (5264279319/10000000000 : ℝ), (1078920209/2000000000 : ℝ)] ![(13168450652971/100000000000000 : ℝ), (10678007340547/25000000000000 : ℝ), (8823903994777/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1083603833/5000000000 : ℝ)|^4167 ≤ (13168450652971/100000000000000 : ℝ)^3143
        have hw : |(-1083603833/5000000000 : ℝ)|=(1083603833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264279319/10000000000 : ℝ)|^4167 ≤ (10678007340547/25000000000000 : ℝ)^3143
        have hw : |(5264279319/10000000000 : ℝ)|=(5264279319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078920209/2000000000 : ℝ)|^4167 ≤ (8823903994777/20000000000000 : ℝ)^3143
        have hw : |(1078920209/2000000000 : ℝ)|=(1078920209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s5_5 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312049401/10000000000 : ℝ)*x 0 + (-420602897/2000000000 : ℝ)*x 1 + (2697300563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312049401/10000000000 : ℝ)^4167 ≤ (43226649290219/100000000000000 : ℝ)^3143 := by
    have hnat : (5312049401 : ℕ)^4167*100000000000000^3143 ≤ 43226649290219^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312049401 10000000000 43226649290219 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (420602897/2000000000 : ℝ)^4167 ≤ (12653829833547/100000000000000 : ℝ)^3143 := by
    have hnat : (420602897 : ℕ)^4167*100000000000000^3143 ≤ 12653829833547^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420602897 2000000000 12653829833547 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697300563/5000000000 : ℝ)^4167 ≤ (4411952085217/10000000000000 : ℝ)^3143 := by
    have hnat : (2697300563 : ℕ)^4167*10000000000000^3143 ≤ 4411952085217^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697300563 5000000000 4411952085217 10000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312049401/10000000000 : ℝ), (-420602897/2000000000 : ℝ), (2697300563/5000000000 : ℝ)] ![(43226649290219/100000000000000 : ℝ), (12653829833547/100000000000000 : ℝ), (4411952085217/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312049401/10000000000 : ℝ)|^4167 ≤ (43226649290219/100000000000000 : ℝ)^3143
        have hw : |(5312049401/10000000000 : ℝ)|=(5312049401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-420602897/2000000000 : ℝ)|^4167 ≤ (12653829833547/100000000000000 : ℝ)^3143
        have hw : |(-420602897/2000000000 : ℝ)|=(420602897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697300563/5000000000 : ℝ)|^4167 ≤ (4411952085217/10000000000000 : ℝ)^3143
        have hw : |(2697300563/5000000000 : ℝ)|=(2697300563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s5_6 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664006121/1250000000 : ℝ)*x 0 + (2697300699/5000000000 : ℝ)*x 1 + (-2103014703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664006121/1250000000 : ℝ)^4167 ≤ (21613322309359/50000000000000 : ℝ)^3143 := by
    have hnat : (664006121 : ℕ)^4167*50000000000000^3143 ≤ 21613322309359^3143*1250000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664006121 1250000000 21613322309359 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697300699/5000000000 : ℝ)^4167 ≤ (22059761900737/50000000000000 : ℝ)^3143 := by
    have hnat : (2697300699 : ℕ)^4167*50000000000000^3143 ≤ 22059761900737^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697300699 5000000000 22059761900737 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2103014703/10000000000 : ℝ)^4167 ≤ (1265383157261/10000000000000 : ℝ)^3143 := by
    have hnat : (2103014703 : ℕ)^4167*10000000000000^3143 ≤ 1265383157261^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103014703 10000000000 1265383157261 10000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664006121/1250000000 : ℝ), (2697300699/5000000000 : ℝ), (-2103014703/10000000000 : ℝ)] ![(21613322309359/50000000000000 : ℝ), (22059761900737/50000000000000 : ℝ), (1265383157261/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664006121/1250000000 : ℝ)|^4167 ≤ (21613322309359/50000000000000 : ℝ)^3143
        have hw : |(664006121/1250000000 : ℝ)|=(664006121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697300699/5000000000 : ℝ)|^4167 ≤ (22059761900737/50000000000000 : ℝ)^3143
        have hw : |(2697300699/5000000000 : ℝ)|=(2697300699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2103014703/10000000000 : ℝ)|^4167 ≤ (1265383157261/10000000000000 : ℝ)^3143
        have hw : |(-2103014703/10000000000 : ℝ)|=(2103014703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1141_s5_7 (p : ℝ) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2182365113/5000000000 : ℝ)*x 0 + (4496266539/10000000000 : ℝ)*x 1 + (847409023/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182365113/5000000000 : ℝ)^4167 ≤ (16658056052431/50000000000000 : ℝ)^3143 := by
    have hnat : (2182365113 : ℕ)^4167*50000000000000^3143 ≤ 16658056052431^3143*5000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182365113 5000000000 16658056052431 50000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496266539/10000000000 : ℝ)^4167 ≤ (3465373698767/10000000000000 : ℝ)^3143 := by
    have hnat : (4496266539 : ℕ)^4167*10000000000000^3143 ≤ 3465373698767^3143*10000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496266539 10000000000 3465373698767 10000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847409023/2000000000 : ℝ)^4167 ≤ (32030150898537/100000000000000 : ℝ)^3143 := by
    have hnat : (847409023 : ℕ)^4167*100000000000000^3143 ≤ 32030150898537^3143*2000000000^4167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847409023 2000000000 32030150898537 100000000000000 4167 3143 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4167/1024 : ℝ)) 4167 3143 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182365113/5000000000 : ℝ), (4496266539/10000000000 : ℝ), (847409023/2000000000 : ℝ)] ![(16658056052431/50000000000000 : ℝ), (3465373698767/10000000000000 : ℝ), (32030150898537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182365113/5000000000 : ℝ)|^4167 ≤ (16658056052431/50000000000000 : ℝ)^3143
        have hw : |(2182365113/5000000000 : ℝ)|=(2182365113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496266539/10000000000 : ℝ)|^4167 ≤ (3465373698767/10000000000000 : ℝ)^3143
        have hw : |(4496266539/10000000000 : ℝ)|=(4496266539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(847409023/2000000000 : ℝ)|^4167 ≤ (32030150898537/100000000000000 : ℝ)^3143
        have hw : |(847409023/2000000000 : ℝ)|=(847409023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1141_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5657/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1761/12500 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11173/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11173/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11173/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11173/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11173/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11173/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11173/100000 : ℝ) ^ (8333/2048 : ℝ) ≤ (6700665231240661/50000000000000000000 : ℝ) := by
    have hpowers : (11173/100000 : ℝ)^8333 ≤ (6700665231240661/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11173 : ℕ)^8333*50000000000000000000^2048 ≤ 6700665231240661^2048*100000^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11173 100000 6700665231240661 50000000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11173/100000 : ℝ)) (X := (6700665231240661/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8333/2048 : ℝ) ≤ (17951904800197613/50000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8333 ≤ (17951904800197613/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8333*50000000000000000000^2048 ≤ 17951904800197613^2048*20000^8333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 17951904800197613 50000000000000000000 8333 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (17951904800197613/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006700665231240661/25000000000000000000 : ℝ) ≤ (10000658661972243/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (25006700665231240661/25000000000000000000 : ℝ)^2048 ≤ (10000658661972243/10000000000000000 : ℝ)^8333 := by
      have hnat : (25006700665231240661 : ℕ)^2048*10000000000000000^8333 ≤ 10000658661972243^8333*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006700665231240661 25000000000000000000 10000658661972243 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000658661972243/10000000000000000 : ℝ)) (X := (25006700665231240661/25000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012326285015719137/25000000000000000000 : ℝ) ≤ (5000605773172333/5000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (25012326285015719137/25000000000000000000 : ℝ)^2048 ≤ (5000605773172333/5000000000000000 : ℝ)^8333 := by
      have hnat : (25012326285015719137 : ℕ)^2048*5000000000000000^8333 ≤ 5000605773172333^8333*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012326285015719137 25000000000000000000 5000605773172333 5000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000605773172333/5000000000000000 : ℝ)) (X := (25012326285015719137/25000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017951904800197613/25000000000000000000 : ℝ) ≤ (10001764430717089/10000000000000000 : ℝ) ^ (8333/2048 : ℝ) := by
    have hpowers : (25017951904800197613/25000000000000000000 : ℝ)^2048 ≤ (10001764430717089/10000000000000000 : ℝ)^8333 := by
      have hnat : (25017951904800197613 : ℕ)^2048*10000000000000000^8333 ≤ 10001764430717089^8333*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017951904800197613 25000000000000000000 10001764430717089 10000000000000000 2048 8333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001764430717089/10000000000000000 : ℝ)) (X := (25017951904800197613/25000000000000000000 : ℝ)) (by norm_num) 8333 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6700665231240661/50000000000000000000 : ℝ) ≤ ((7652415517193210927/7655000000000000000 : ℝ)+2*(552884372423/306200000000000 : ℝ)*(11173/100000 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (7652415517193210927/7655000000000000000 : ℝ)+2*(552884372423/306200000000000 : ℝ)*(11173/100000 : ℝ)=(10000658661972243/10000000000000000 : ℝ) by norm_num, show 1+2*(6700665231240661/50000000000000000000 : ℝ)=(25006700665231240661/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17951904800197613/50000000000000000000 : ℝ)+(6700665231240661/50000000000000000000 : ℝ) ≤ ((7652415517193210927/7655000000000000000 : ℝ)+(552884372423/306200000000000 : ℝ)*((2847/20000 : ℝ)+(11173/100000 : ℝ)))^(8333/2048 : ℝ) := by
    rw [show (7652415517193210927/7655000000000000000 : ℝ)+(552884372423/306200000000000 : ℝ)*((2847/20000 : ℝ)+(11173/100000 : ℝ))=(5000605773172333/5000000000000000 : ℝ) by norm_num, show 1+(17951904800197613/50000000000000000000 : ℝ)+(6700665231240661/50000000000000000000 : ℝ)=(25012326285015719137/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17951904800197613/50000000000000000000 : ℝ) ≤ ((7652415517193210927/7655000000000000000 : ℝ)+2*(552884372423/306200000000000 : ℝ)*(2847/20000 : ℝ))^(8333/2048 : ℝ) := by
    rw [show (7652415517193210927/7655000000000000000 : ℝ)+2*(552884372423/306200000000000 : ℝ)*(2847/20000 : ℝ)=(10001764430717089/10000000000000000 : ℝ) by norm_num, show 1+2*(17951904800197613/50000000000000000000 : ℝ)=(25017951904800197613/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7652415517193210927/7655000000000000000 : ℝ)*(X 1 0+X 2 0)+(552884372423/306200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (11173/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (7652415517193210927/7655000000000000000 : ℝ)) (alpha := (552884372423/306200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7652415517193210927/7655000000000000000 : ℝ)*(X 0 1+X 2 1)+(552884372423/306200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (11173/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (7652415517193210927/7655000000000000000 : ℝ)) (alpha := (552884372423/306200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7652415517193210927/7655000000000000000 : ℝ)*(X 0 2+X 1 2)+(552884372423/306200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8333/2048 : ℝ)) (lo := (11173/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (7652415517193210927/7655000000000000000 : ℝ)) (alpha := (552884372423/306200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-54180063/250000000 : ℝ)*X 0 0+(2697470557/5000000000 : ℝ)*X 0 1+(657992547/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345235689/10000000000 : ℝ)*X 1 0+(-1116837847/5000000000 : ℝ)*X 1 1+(5263940419/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345235551/10000000000 : ℝ)*X 2 0+(5263940559/10000000000 : ℝ)*X 2 1+(-558418923/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364719413/10000000000 : ℝ)*X 0 0+(211818457/500000000 : ℝ)*X 0 1+(4496940237/10000000000 : ℝ)*X 0 2+(4364719413/10000000000 : ℝ)*X 1 0+(211818457/500000000 : ℝ)*X 1 1+(4496940237/10000000000 : ℝ)*X 1 2+(4364719413/10000000000 : ℝ)*X 2 0+(211818457/500000000 : ℝ)*X 2 1+(4496940237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1083603833/5000000000 : ℝ)*X 0 0+(5264279319/10000000000 : ℝ)*X 0 1+(1078920209/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312049401/10000000000 : ℝ)*X 1 0+(-420602897/2000000000 : ℝ)*X 1 1+(2697300563/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664006121/1250000000 : ℝ)*X 2 0+(2697300699/5000000000 : ℝ)*X 2 1+(-2103014703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182365113/5000000000 : ℝ)*X 0 0+(4496266539/10000000000 : ℝ)*X 0 1+(847409023/2000000000 : ℝ)*X 0 2+(2182365113/5000000000 : ℝ)*X 1 0+(4496266539/10000000000 : ℝ)*X 1 1+(847409023/2000000000 : ℝ)*X 1 2+(2182365113/5000000000 : ℝ)*X 2 0+(4496266539/10000000000 : ℝ)*X 2 1+(847409023/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1141_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (632705433928760667181686867/191375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (874221413/100000000000000 : ℝ)*(base19) + (15243009/2500000000000 : ℝ)*(base23) + (17531979/12500000000000 : ℝ)*(upper3) + (4504803/12500000000000 : ℝ)*(upper4) + (2883887/5000000000000 : ℝ)*(upper5) + (5735670714129593/100000000000000 : ℝ)*(major0) + (5735670714129593/100000000000000 : ℝ)*(major1) + (2867835357064797/50000000000000 : ℝ)*(major2) + (238549157040117/3125000000000 : ℝ)*(sp0) + (7633595616815799/100000000000000 : ℝ)*(sp1) + (7633595881316853/100000000000000 : ℝ)*(sp2) + (3837733996118513/100000000000000 : ℝ)*(sp3) + (5866438367/25000000000000 : ℝ)*(sp4) + (1353862503/12500000000000 : ℝ)*(sp7) + (3837744827018537/100000000000000 : ℝ)*(f.failure) + (7633596491037213/100000000000000 : ℝ)*(f.sum) + (148140555139399/30620000000000000000000000000 : ℝ)*base66 + (12244844852926212711/765500000000000000000000000000000 : ℝ)*base67 + (3594750291398325681/382750000000000000000000000000000 : ℝ)*base70 + (2833172436856212711/765500000000000000000000000000000 : ℝ)*base71 + (45662656025101/30620000000000000000000000000 : ℝ)*base73 + (3543285367904924319/382750000000000000000000000000000 : ℝ)*base75 + (1290501005919637711/765500000000000000000000000000000 : ℝ)*base77 + (1153807747721137711/765500000000000000000000000000000 : ℝ)*base79 + (33433123011311/15310000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (51449789/10000000000000000000000 : ℝ)*base89 + (51449789/10000000000000000000000 : ℝ)*base91 + (48550211/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (157990062915897817763535303/382750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (242155073/20000000000000 : ℝ)*(base19) + (851533861/100000000000000 : ℝ)*(base23) + (34056327/100000000000000 : ℝ)*(upper3) + (33080463/20000000000000 : ℝ)*(lower4) + (2882753052397027/50000000000000 : ℝ)*(major0) + (2882753052397027/50000000000000 : ℝ)*(major1) + (1153101220958811/20000000000000 : ℝ)*(major2) + (22413310137/50000000000000 : ℝ)*(sp1) + (1880033589/5000000000000 : ℝ)*(sp2) + (3143000283/100000000000000 : ℝ)*(sp3) + (1534660893926463/20000000000000 : ℝ)*(sp4) + (1918314608059169/25000000000000 : ℝ)*(sp5) + (3836633008713337/50000000000000 : ℝ)*(sp6) + (482213072899537/12500000000000 : ℝ)*(sp7) + (1928853863098289/50000000000000 : ℝ)*(f.failure) + (1534660893926463/20000000000000 : ℝ)*(f.sum) + (267709091422593/30620000000000000000000000000 : ℝ)*base66 + (2959347768180223471/382750000000000000000000000000000 : ℝ)*base68 + (2289669688220262203/153100000000000000000000000000000 : ℝ)*base70 + (8164260522837223471/382750000000000000000000000000000 : ℝ)*base72 + (104217403293653/30620000000000000000000000000 : ℝ)*base74 + (1869683135971962203/153100000000000000000000000000000 : ℝ)*base76 + (2010440342205010971/382750000000000000000000000000000 : ℝ)*base78 + (5616045411809760971/382750000000000000000000000000000 : ℝ)*base80 + (7698952590963/3827500000000000000000000000 : ℝ)*base81 + (14568933/5000000000000000000000 : ℝ)*base89 + (14568933/5000000000000000000000 : ℝ)*base91 + (35431067/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1141_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1141_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1141_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8253/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4533/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1141_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1141_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1141_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8333/2048 : ℝ) ≤ p) (hpb : p ≤ (4167/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149454197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8253/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4533/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1141_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

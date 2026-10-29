-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1718_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:55:24.208714+00:00
-- url     : https://prove2.me/submissions/5defedb3-d89a-46e5-8b82-61c89661d759

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
theorem support_rectangle_w1718_s0_0 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1313367153/10000000000 : ℝ)*x 0 + (5682133711/10000000000 : ℝ)*x 1 + (621060167/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313367153/10000000000 : ℝ)^5367 ≤ (8138000696621/100000000000000 : ℝ)^4343 := by
    have hnat : (1313367153 : ℕ)^5367*100000000000000^4343 ≤ 8138000696621^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313367153 10000000000 8138000696621 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5682133711/10000000000 : ℝ)^5367 ≤ (9946258283061/20000000000000 : ℝ)^4343 := by
    have hnat : (5682133711 : ℕ)^5367*20000000000000^4343 ≤ 9946258283061^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5682133711 10000000000 9946258283061 20000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (621060167/1250000000 : ℝ)^5367 ≤ (21065353937121/50000000000000 : ℝ)^4343 := by
    have hnat : (621060167 : ℕ)^5367*50000000000000^4343 ≤ 21065353937121^4343*1250000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621060167 1250000000 21065353937121 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1313367153/10000000000 : ℝ), (5682133711/10000000000 : ℝ), (621060167/1250000000 : ℝ)] ![(8138000696621/100000000000000 : ℝ), (9946258283061/20000000000000 : ℝ), (21065353937121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1313367153/10000000000 : ℝ)|^5367 ≤ (8138000696621/100000000000000 : ℝ)^4343
        have hw : |(-1313367153/10000000000 : ℝ)|=(1313367153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5682133711/10000000000 : ℝ)|^5367 ≤ (9946258283061/20000000000000 : ℝ)^4343
        have hw : |(5682133711/10000000000 : ℝ)|=(5682133711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(621060167/1250000000 : ℝ)|^5367 ≤ (21065353937121/50000000000000 : ℝ)^4343
        have hw : |(621060167/1250000000 : ℝ)|=(621060167/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s0_1 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539874287/1000000000 : ℝ)*x 0 + (-849411091/5000000000 : ℝ)*x 1 + (4968479891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539874287/1000000000 : ℝ)^5367 ≤ (11671109718053/25000000000000 : ℝ)^4343 := by
    have hnat : (539874287 : ℕ)^5367*25000000000000^4343 ≤ 11671109718053^4343*1000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539874287 1000000000 11671109718053 25000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849411091/5000000000 : ℝ)^5367 ≤ (11184868384071/100000000000000 : ℝ)^4343 := by
    have hnat : (849411091 : ℕ)^5367*100000000000000^4343 ≤ 11184868384071^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849411091 5000000000 11184868384071 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4968479891/10000000000 : ℝ)^5367 ≤ (42130692732191/100000000000000 : ℝ)^4343 := by
    have hnat : (4968479891 : ℕ)^5367*100000000000000^4343 ≤ 42130692732191^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4968479891 10000000000 42130692732191 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539874287/1000000000 : ℝ), (-849411091/5000000000 : ℝ), (4968479891/10000000000 : ℝ)] ![(11671109718053/25000000000000 : ℝ), (11184868384071/100000000000000 : ℝ), (42130692732191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539874287/1000000000 : ℝ)|^5367 ≤ (11671109718053/25000000000000 : ℝ)^4343
        have hw : |(539874287/1000000000 : ℝ)|=(539874287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-849411091/5000000000 : ℝ)|^5367 ≤ (11184868384071/100000000000000 : ℝ)^4343
        have hw : |(-849411091/5000000000 : ℝ)|=(849411091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4968479891/10000000000 : ℝ)|^5367 ≤ (42130692732191/100000000000000 : ℝ)^4343
        have hw : |(4968479891/10000000000 : ℝ)|=(4968479891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s0_2 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5398741987/10000000000 : ℝ)*x 0 + (77632521/156250000 : ℝ)*x 1 + (-169882147/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5398741987/10000000000 : ℝ)^5367 ≤ (23342214718171/50000000000000 : ℝ)^4343 := by
    have hnat : (5398741987 : ℕ)^5367*50000000000000^4343 ≤ 23342214718171^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398741987 10000000000 23342214718171 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77632521/156250000 : ℝ)^5367 ≤ (42130707958073/100000000000000 : ℝ)^4343 := by
    have hnat : (77632521 : ℕ)^5367*100000000000000^4343 ≤ 42130707958073^4343*156250000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77632521 156250000 42130707958073 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169882147/1000000000 : ℝ)^5367 ≤ (699053911941/6250000000000 : ℝ)^4343 := by
    have hnat : (169882147 : ℕ)^5367*6250000000000^4343 ≤ 699053911941^4343*1000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169882147 1000000000 699053911941 6250000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5398741987/10000000000 : ℝ), (77632521/156250000 : ℝ), (-169882147/1000000000 : ℝ)] ![(23342214718171/50000000000000 : ℝ), (42130707958073/100000000000000 : ℝ), (699053911941/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5398741987/10000000000 : ℝ)|^5367 ≤ (23342214718171/50000000000000 : ℝ)^4343
        have hw : |(5398741987/10000000000 : ℝ)|=(5398741987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(77632521/156250000 : ℝ)|^5367 ≤ (42130707958073/100000000000000 : ℝ)^4343
        have hw : |(77632521/156250000 : ℝ)|=(77632521/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-169882147/1000000000 : ℝ)|^5367 ≤ (699053911941/6250000000000 : ℝ)^4343
        have hw : |(-169882147/1000000000 : ℝ)|=(169882147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s0_3 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (252056717/625000000 : ℝ)*x 0 + (3063998039/10000000000 : ℝ)*x 1 + (1292710823/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (252056717/625000000 : ℝ)^5367 ≤ (16277970525503/50000000000000 : ℝ)^4343 := by
    have hnat : (252056717 : ℕ)^5367*50000000000000^4343 ≤ 16277970525503^4343*625000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252056717 625000000 16277970525503 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3063998039/10000000000 : ℝ)^5367 ≤ (23182736508889/100000000000000 : ℝ)^4343 := by
    have hnat : (3063998039 : ℕ)^5367*100000000000000^4343 ≤ 23182736508889^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3063998039 10000000000 23182736508889 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1292710823/2500000000 : ℝ)^5367 ≤ (44261322423121/100000000000000 : ℝ)^4343 := by
    have hnat : (1292710823 : ℕ)^5367*100000000000000^4343 ≤ 44261322423121^4343*2500000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292710823 2500000000 44261322423121 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(252056717/625000000 : ℝ), (3063998039/10000000000 : ℝ), (1292710823/2500000000 : ℝ)] ![(16277970525503/50000000000000 : ℝ), (23182736508889/100000000000000 : ℝ), (44261322423121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(252056717/625000000 : ℝ)|^5367 ≤ (16277970525503/50000000000000 : ℝ)^4343
        have hw : |(252056717/625000000 : ℝ)|=(252056717/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3063998039/10000000000 : ℝ)|^5367 ≤ (23182736508889/100000000000000 : ℝ)^4343
        have hw : |(3063998039/10000000000 : ℝ)|=(3063998039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1292710823/2500000000 : ℝ)|^5367 ≤ (44261322423121/100000000000000 : ℝ)^4343
        have hw : |(1292710823/2500000000 : ℝ)|=(1292710823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s0_4 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1314915969/10000000000 : ℝ)*x 0 + (4985864661/10000000000 : ℝ)*x 1 + (5664181571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314915969/10000000000 : ℝ)^5367 ≤ (8149862030209/100000000000000 : ℝ)^4343 := by
    have hnat : (1314915969 : ℕ)^5367*100000000000000^4343 ≤ 8149862030209^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314915969 10000000000 8149862030209 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4985864661/10000000000 : ℝ)^5367 ≤ (5289117694267/12500000000000 : ℝ)^4343 := by
    have hnat : (4985864661 : ℕ)^5367*12500000000000^4343 ≤ 5289117694267^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4985864661 10000000000 5289117694267 12500000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5664181571/10000000000 : ℝ)^5367 ≤ (49537196409717/100000000000000 : ℝ)^4343 := by
    have hnat : (5664181571 : ℕ)^5367*100000000000000^4343 ≤ 49537196409717^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5664181571 10000000000 49537196409717 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1314915969/10000000000 : ℝ), (4985864661/10000000000 : ℝ), (5664181571/10000000000 : ℝ)] ![(8149862030209/100000000000000 : ℝ), (5289117694267/12500000000000 : ℝ), (49537196409717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1314915969/10000000000 : ℝ)|^5367 ≤ (8149862030209/100000000000000 : ℝ)^4343
        have hw : |(-1314915969/10000000000 : ℝ)|=(1314915969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4985864661/10000000000 : ℝ)|^5367 ≤ (5289117694267/12500000000000 : ℝ)^4343
        have hw : |(4985864661/10000000000 : ℝ)|=(4985864661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5664181571/10000000000 : ℝ)|^5367 ≤ (49537196409717/100000000000000 : ℝ)^4343
        have hw : |(5664181571/10000000000 : ℝ)|=(5664181571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s0_5 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (650706377/1250000000 : ℝ)*x 0 + (-1003121763/10000000000 : ℝ)*x 1 + (5664181949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (650706377/1250000000 : ℝ)^5367 ≤ (44629811252337/100000000000000 : ℝ)^4343 := by
    have hnat : (650706377 : ℕ)^5367*100000000000000^4343 ≤ 44629811252337^4343*1250000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650706377 1250000000 44629811252337 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003121763/10000000000 : ℝ)^5367 ≤ (1458247062183/25000000000000 : ℝ)^4343 := by
    have hnat : (1003121763 : ℕ)^5367*25000000000000^4343 ≤ 1458247062183^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003121763 10000000000 1458247062183 25000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5664181949/10000000000 : ℝ)^5367 ≤ (24768600247527/50000000000000 : ℝ)^4343 := by
    have hnat : (5664181949 : ℕ)^5367*50000000000000^4343 ≤ 24768600247527^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5664181949 10000000000 24768600247527 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(650706377/1250000000 : ℝ), (-1003121763/10000000000 : ℝ), (5664181949/10000000000 : ℝ)] ![(44629811252337/100000000000000 : ℝ), (1458247062183/25000000000000 : ℝ), (24768600247527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(650706377/1250000000 : ℝ)|^5367 ≤ (44629811252337/100000000000000 : ℝ)^4343
        have hw : |(650706377/1250000000 : ℝ)|=(650706377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1003121763/10000000000 : ℝ)|^5367 ≤ (1458247062183/25000000000000 : ℝ)^4343
        have hw : |(-1003121763/10000000000 : ℝ)|=(1003121763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5664181949/10000000000 : ℝ)|^5367 ≤ (24768600247527/50000000000000 : ℝ)^4343
        have hw : |(5664181949/10000000000 : ℝ)|=(5664181949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s0_6 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (260282603/500000000 : ℝ)*x 0 + (5664181067/10000000000 : ℝ)*x 1 + (-250780387/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260282603/500000000 : ℝ)^5367 ≤ (44629822313283/100000000000000 : ℝ)^4343 := by
    have hnat : (260282603 : ℕ)^5367*100000000000000^4343 ≤ 44629822313283^4343*500000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260282603 500000000 44629822313283 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5664181067/10000000000 : ℝ)^5367 ≤ (24768595481301/50000000000000 : ℝ)^4343 := by
    have hnat : (5664181067 : ℕ)^5367*50000000000000^4343 ≤ 24768595481301^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5664181067 10000000000 24768595481301 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250780387/2500000000 : ℝ)^5367 ≤ (583298670377/10000000000000 : ℝ)^4343 := by
    have hnat : (250780387 : ℕ)^5367*10000000000000^4343 ≤ 583298670377^4343*2500000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250780387 2500000000 583298670377 10000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(260282603/500000000 : ℝ), (5664181067/10000000000 : ℝ), (-250780387/2500000000 : ℝ)] ![(44629822313283/100000000000000 : ℝ), (24768595481301/50000000000000 : ℝ), (583298670377/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(260282603/500000000 : ℝ)|^5367 ≤ (44629822313283/100000000000000 : ℝ)^4343
        have hw : |(260282603/500000000 : ℝ)|=(260282603/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5664181067/10000000000 : ℝ)|^5367 ≤ (24768595481301/50000000000000 : ℝ)^4343
        have hw : |(5664181067/10000000000 : ℝ)|=(5664181067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-250780387/2500000000 : ℝ)|^5367 ≤ (583298670377/10000000000000 : ℝ)^4343
        have hw : |(-250780387/2500000000 : ℝ)|=(250780387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s0_7 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4037483009/10000000000 : ℝ)*x 0 + (1279880793/2500000000 : ℝ)*x 1 + (779249887/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4037483009/10000000000 : ℝ)^5367 ≤ (8150398107493/25000000000000 : ℝ)^4343 := by
    have hnat : (4037483009 : ℕ)^5367*25000000000000^4343 ≤ 8150398107493^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4037483009 10000000000 8150398107493 25000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1279880793/2500000000 : ℝ)^5367 ≤ (43719093474103/100000000000000 : ℝ)^4343 := by
    have hnat : (1279880793 : ℕ)^5367*100000000000000^4343 ≤ 43719093474103^4343*2500000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279880793 2500000000 43719093474103 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (779249887/2500000000 : ℝ)^5367 ≤ (23679314084289/100000000000000 : ℝ)^4343 := by
    have hnat : (779249887 : ℕ)^5367*100000000000000^4343 ≤ 23679314084289^4343*2500000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779249887 2500000000 23679314084289 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4037483009/10000000000 : ℝ), (1279880793/2500000000 : ℝ), (779249887/2500000000 : ℝ)] ![(8150398107493/25000000000000 : ℝ), (43719093474103/100000000000000 : ℝ), (23679314084289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4037483009/10000000000 : ℝ)|^5367 ≤ (8150398107493/25000000000000 : ℝ)^4343
        have hw : |(4037483009/10000000000 : ℝ)|=(4037483009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1279880793/2500000000 : ℝ)|^5367 ≤ (43719093474103/100000000000000 : ℝ)^4343
        have hw : |(1279880793/2500000000 : ℝ)|=(1279880793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(779249887/2500000000 : ℝ)|^5367 ≤ (23679314084289/100000000000000 : ℝ)^4343
        have hw : |(779249887/2500000000 : ℝ)|=(779249887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1718_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (197609909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3139/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (21633/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (5359/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5359 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5359*1^1024 ≤ 0^1024*1^5359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5359/1024 : ℝ) ≤ (826839813591637379/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5359 ≤ (826839813591637379/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5359*100000000000000000000^1024 ≤ 826839813591637379^1024*5^5359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 826839813591637379 100000000000000000000 5359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (826839813591637379/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5359/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5359 := by
      have hnat : (1 : ℕ)^1024*1^5359 ≤ 1^5359*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100826839813591637379/100000000000000000000 : ℝ) ≤ (5007873357853323/5000000000000000 : ℝ) ^ (5359/1024 : ℝ) := by
    have hpowers : (100826839813591637379/100000000000000000000 : ℝ)^1024 ≤ (5007873357853323/5000000000000000 : ℝ)^5359 := by
      have hnat : (100826839813591637379 : ℕ)^1024*5000000000000000^5359 ≤ 5007873357853323^5359*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100826839813591637379 100000000000000000000 5007873357853323 5000000000000000 1024 5359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007873357853323/5000000000000000 : ℝ)) (X := (100826839813591637379/100000000000000000000 : ℝ)) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50826839813591637379/50000000000000000000 : ℝ) ≤ (2507873357853323/2500000000000000 : ℝ) ^ (5359/1024 : ℝ) := by
    have hpowers : (50826839813591637379/50000000000000000000 : ℝ)^1024 ≤ (2507873357853323/2500000000000000 : ℝ)^5359 := by
      have hnat : (50826839813591637379 : ℕ)^1024*2500000000000000^5359 ≤ 2507873357853323^5359*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50826839813591637379 50000000000000000000 2507873357853323 2500000000000000 1024 5359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2507873357853323/2500000000000000 : ℝ)) (X := (50826839813591637379/50000000000000000000 : ℝ)) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7873357853323/2000000000000000 : ℝ)*(0 : ℝ))^(5359/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7873357853323/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(826839813591637379/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7873357853323/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5359/1024 : ℝ) := by
    rw [show (1 : ℝ)+(7873357853323/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5007873357853323/5000000000000000 : ℝ) by norm_num, show 1+(826839813591637379/100000000000000000000 : ℝ)+(0 : ℝ)=(100826839813591637379/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(826839813591637379/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7873357853323/2000000000000000 : ℝ)*(2/5 : ℝ))^(5359/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7873357853323/2000000000000000 : ℝ)*(2/5 : ℝ)=(2507873357853323/2500000000000000 : ℝ) by norm_num, show 1+2*(826839813591637379/100000000000000000000 : ℝ)=(50826839813591637379/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7873357853323/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5359/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7873357853323/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7873357853323/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5359/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7873357853323/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7873357853323/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5359/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7873357853323/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1313367153/10000000000 : ℝ)*X 0 0+(5682133711/10000000000 : ℝ)*X 0 1+(621060167/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((539874287/1000000000 : ℝ)*X 1 0+(-849411091/5000000000 : ℝ)*X 1 1+(4968479891/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5398741987/10000000000 : ℝ)*X 2 0+(77632521/156250000 : ℝ)*X 2 1+(-169882147/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((252056717/625000000 : ℝ)*X 0 0+(3063998039/10000000000 : ℝ)*X 0 1+(1292710823/2500000000 : ℝ)*X 0 2+(252056717/625000000 : ℝ)*X 1 0+(3063998039/10000000000 : ℝ)*X 1 1+(1292710823/2500000000 : ℝ)*X 1 2+(252056717/625000000 : ℝ)*X 2 0+(3063998039/10000000000 : ℝ)*X 2 1+(1292710823/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1314915969/10000000000 : ℝ)*X 0 0+(4985864661/10000000000 : ℝ)*X 0 1+(5664181571/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((650706377/1250000000 : ℝ)*X 1 0+(-1003121763/10000000000 : ℝ)*X 1 1+(5664181949/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((260282603/500000000 : ℝ)*X 2 0+(5664181067/10000000000 : ℝ)*X 2 1+(-250780387/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4037483009/10000000000 : ℝ)*X 0 0+(1279880793/2500000000 : ℝ)*X 0 1+(779249887/2500000000 : ℝ)*X 0 2+(4037483009/10000000000 : ℝ)*X 1 0+(1279880793/2500000000 : ℝ)*X 1 1+(779249887/2500000000 : ℝ)*X 1 2+(4037483009/10000000000 : ℝ)*X 2 0+(1279880793/2500000000 : ℝ)*X 2 1+(779249887/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5986225720977888321/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (226063051/100000000000000 : ℝ)*(base1) + (49497739/5000000000000 : ℝ)*(base19) + (37625321/5000000000000 : ℝ)*(base23) + (8265561/100000000000000 : ℝ)*(base24) + (55246029/25000000000000 : ℝ)*(upper5) + (117243150460013/12500000000000 : ℝ)*(major0) + (117243150460013/12500000000000 : ℝ)*(major1) + (117243150460013/12500000000000 : ℝ)*(major2) + (700621487850469/50000000000000 : ℝ)*(sp0) + (700622197210483/50000000000000 : ℝ)*(sp1) + (280248924720753/20000000000000 : ℝ)*(sp2) + (237322173038147/50000000000000 : ℝ)*(sp3) + (1317368929/50000000000000 : ℝ)*(sp4) + (62826063/25000000000000 : ℝ)*(sp7) + (237322411721799/50000000000000 : ℝ)*(f.failure) + (700622692187873/50000000000000 : ℝ)*(f.sum) + (11053608326801/12500000000000000000000000000 : ℝ)*base66 + (314411834023199/25000000000000000000000000000 : ℝ)*base67 + (200580979923199/25000000000000000000000000000 : ℝ)*base69 + (36825244273199/25000000000000000000000000000 : ℝ)*base71 + (55830543198199/12500000000000000000000000000 : ℝ)*base73 + (61656185576801/25000000000000000000000000000 : ℝ)*base76 + (52181028398199/25000000000000000000000000000 : ℝ)*base77 + (125225743576801/25000000000000000000000000000 : ℝ)*base80 + (32668411751801/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (33706291/5000000000000000000000 : ℝ)*base89 + (33706291/5000000000000000000000 : ℝ)*base91 + (33706291/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (636772420772650069973571/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (79574749/100000000000000 : ℝ)*(base1) + (995152657/100000000000000 : ℝ)*(base19) + (1365878731/100000000000000 : ℝ)*(base23) + (666711249/100000000000000 : ℝ)*(base32) + (303322891/100000000000000 : ℝ)*(upper3) + (493400781283341/50000000000000 : ℝ)*(major0) + (493400781283341/50000000000000 : ℝ)*(major1) + (493400781283341/50000000000000 : ℝ)*(major2) + (1995260241/100000000000000 : ℝ)*(sp1) + (4019059717/100000000000000 : ℝ)*(sp2) + (1474234318580903/100000000000000 : ℝ)*(sp4) + (184278906074157/12500000000000 : ℝ)*(sp5) + (294845770813541/20000000000000 : ℝ)*(sp6) + (499367715326259/100000000000000 : ℝ)*(sp7) + (249684230806129/50000000000000 : ℝ)*(f.failure) + (737117119503077/50000000000000 : ℝ)*(f.sum) + (55188115192143/50000000000000000000000000000 : ℝ)*base65 + (53958538292143/100000000000000000000000000000 : ℝ)*base67 + (334665826892143/100000000000000000000000000000 : ℝ)*base69 + (219708528307857/100000000000000000000000000000 : ℝ)*base72 + (2691086507857/50000000000000000000000000000 : ℝ)*base74 + (685279307857/100000000000000000000000000000 : ℝ)*base76 + (97766549607857/100000000000000000000000000000 : ℝ)*base78 + (554319338292143/100000000000000000000000000000 : ℝ)*base79 + (237362801292143/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (48332261/5000000000000000000000 : ℝ)*base89 + (48332261/5000000000000000000000 : ℝ)*base91 + (48332261/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1718_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (197609909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3139/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (21633/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1718_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1718_s1_0 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1380644179/10000000000 : ℝ)*x 0 + (2738751289/5000000000 : ℝ)*x 1 + (2564363859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1380644179/10000000000 : ℝ)^5367 ≤ (8656229613649/100000000000000 : ℝ)^4343 := by
    have hnat : (1380644179 : ℕ)^5367*100000000000000^4343 ≤ 8656229613649^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380644179 10000000000 8656229613649 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738751289/5000000000 : ℝ)^5367 ≤ (4752751907461/10000000000000 : ℝ)^4343 := by
    have hnat : (2738751289 : ℕ)^5367*10000000000000^4343 ≤ 4752751907461^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738751289 5000000000 4752751907461 10000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2564363859/5000000000 : ℝ)^5367 ≤ (2738515706061/6250000000000 : ℝ)^4343 := by
    have hnat : (2564363859 : ℕ)^5367*6250000000000^4343 ≤ 2738515706061^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564363859 5000000000 2738515706061 6250000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1380644179/10000000000 : ℝ), (2738751289/5000000000 : ℝ), (2564363859/5000000000 : ℝ)] ![(8656229613649/100000000000000 : ℝ), (4752751907461/10000000000000 : ℝ), (2738515706061/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1380644179/10000000000 : ℝ)|^5367 ≤ (8656229613649/100000000000000 : ℝ)^4343
        have hw : |(-1380644179/10000000000 : ℝ)|=(1380644179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738751289/5000000000 : ℝ)|^5367 ≤ (4752751907461/10000000000000 : ℝ)^4343
        have hw : |(2738751289/5000000000 : ℝ)|=(2738751289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2564363859/5000000000 : ℝ)|^5367 ≤ (2738515706061/6250000000000 : ℝ)^4343
        have hw : |(2564363859/5000000000 : ℝ)|=(2564363859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s1_1 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668030047/1250000000 : ℝ)*x 0 + (-780912541/5000000000 : ℝ)*x 1 + (512872671/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668030047/1250000000 : ℝ)^5367 ≤ (23051356004983/50000000000000 : ℝ)^4343 := by
    have hnat : (668030047 : ℕ)^5367*50000000000000^4343 ≤ 23051356004983^4343*1250000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668030047 1250000000 23051356004983 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (780912541/5000000000 : ℝ)^5367 ≤ (10081047326779/100000000000000 : ℝ)^4343 := by
    have hnat : (780912541 : ℕ)^5367*100000000000000^4343 ≤ 10081047326779^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780912541 5000000000 10081047326779 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512872671/1000000000 : ℝ)^5367 ≤ (43816240654863/100000000000000 : ℝ)^4343 := by
    have hnat : (512872671 : ℕ)^5367*100000000000000^4343 ≤ 43816240654863^4343*1000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512872671 1000000000 43816240654863 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668030047/1250000000 : ℝ), (-780912541/5000000000 : ℝ), (512872671/1000000000 : ℝ)] ![(23051356004983/50000000000000 : ℝ), (10081047326779/100000000000000 : ℝ), (43816240654863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668030047/1250000000 : ℝ)|^5367 ≤ (23051356004983/50000000000000 : ℝ)^4343
        have hw : |(668030047/1250000000 : ℝ)|=(668030047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-780912541/5000000000 : ℝ)|^5367 ≤ (10081047326779/100000000000000 : ℝ)^4343
        have hw : |(-780912541/5000000000 : ℝ)|=(780912541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(512872671/1000000000 : ℝ)|^5367 ≤ (43816240654863/100000000000000 : ℝ)^4343
        have hw : |(512872671/1000000000 : ℝ)|=(512872671/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s1_2 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672119569/5000000000 : ℝ)*x 0 + (5128727663/10000000000 : ℝ)*x 1 + (-780912737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672119569/5000000000 : ℝ)^5367 ≤ (368821590497/800000000000 : ℝ)^4343 := by
    have hnat : (2672119569 : ℕ)^5367*800000000000^4343 ≤ 368821590497^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672119569 5000000000 368821590497 800000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5128727663/10000000000 : ℝ)^5367 ≤ (8763250143261/20000000000000 : ℝ)^4343 := by
    have hnat : (5128727663 : ℕ)^5367*20000000000000^4343 ≤ 8763250143261^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128727663 10000000000 8763250143261 20000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (780912737/5000000000 : ℝ)^5367 ≤ (5040525226793/50000000000000 : ℝ)^4343 := by
    have hnat : (780912737 : ℕ)^5367*50000000000000^4343 ≤ 5040525226793^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780912737 5000000000 5040525226793 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672119569/5000000000 : ℝ), (5128727663/10000000000 : ℝ), (-780912737/5000000000 : ℝ)] ![(368821590497/800000000000 : ℝ), (8763250143261/20000000000000 : ℝ), (5040525226793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672119569/5000000000 : ℝ)|^5367 ≤ (368821590497/800000000000 : ℝ)^4343
        have hw : |(2672119569/5000000000 : ℝ)|=(2672119569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5128727663/10000000000 : ℝ)|^5367 ≤ (8763250143261/20000000000000 : ℝ)^4343
        have hw : |(5128727663/10000000000 : ℝ)|=(5128727663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-780912737/5000000000 : ℝ)|^5367 ≤ (5040525226793/50000000000000 : ℝ)^4343
        have hw : |(-780912737/5000000000 : ℝ)|=(780912737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s1_3 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4092211459/10000000000 : ℝ)*x 0 + (1798719949/5000000000 : ℝ)*x 1 + (1156772207/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4092211459/10000000000 : ℝ)^5367 ≤ (16574287885657/50000000000000 : ℝ)^4343 := by
    have hnat : (4092211459 : ℕ)^5367*50000000000000^4343 ≤ 16574287885657^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4092211459 10000000000 16574287885657 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1798719949/5000000000 : ℝ)^5367 ≤ (28268641799309/100000000000000 : ℝ)^4343 := by
    have hnat : (1798719949 : ℕ)^5367*100000000000000^4343 ≤ 28268641799309^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1798719949 5000000000 28268641799309 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1156772207/2500000000 : ℝ)^5367 ≤ (38582782414659/100000000000000 : ℝ)^4343 := by
    have hnat : (1156772207 : ℕ)^5367*100000000000000^4343 ≤ 38582782414659^4343*2500000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1156772207 2500000000 38582782414659 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4092211459/10000000000 : ℝ), (1798719949/5000000000 : ℝ), (1156772207/2500000000 : ℝ)] ![(16574287885657/50000000000000 : ℝ), (28268641799309/100000000000000 : ℝ), (38582782414659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4092211459/10000000000 : ℝ)|^5367 ≤ (16574287885657/50000000000000 : ℝ)^4343
        have hw : |(4092211459/10000000000 : ℝ)|=(4092211459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1798719949/5000000000 : ℝ)|^5367 ≤ (28268641799309/100000000000000 : ℝ)^4343
        have hw : |(1798719949/5000000000 : ℝ)|=(1798719949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1156772207/2500000000 : ℝ)|^5367 ≤ (38582782414659/100000000000000 : ℝ)^4343
        have hw : |(1156772207/2500000000 : ℝ)|=(1156772207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s1_4 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1380825327/10000000000 : ℝ)*x 0 + (1026577819/2000000000 : ℝ)*x 1 + (342079599/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1380825327/10000000000 : ℝ)^5367 ≤ (8657633167333/100000000000000 : ℝ)^4343 := by
    have hnat : (1380825327 : ℕ)^5367*100000000000000^4343 ≤ 8657633167333^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380825327 10000000000 8657633167333 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026577819/2000000000 : ℝ)^5367 ≤ (43860189868727/100000000000000 : ℝ)^4343 := by
    have hnat : (1026577819 : ℕ)^5367*100000000000000^4343 ≤ 43860189868727^4343*2000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026577819 2000000000 43860189868727 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (342079599/625000000 : ℝ)^5367 ≤ (47482176951661/100000000000000 : ℝ)^4343 := by
    have hnat : (342079599 : ℕ)^5367*100000000000000^4343 ≤ 47482176951661^4343*625000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342079599 625000000 47482176951661 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1380825327/10000000000 : ℝ), (1026577819/2000000000 : ℝ), (342079599/625000000 : ℝ)] ![(8657633167333/100000000000000 : ℝ), (43860189868727/100000000000000 : ℝ), (47482176951661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1380825327/10000000000 : ℝ)|^5367 ≤ (8657633167333/100000000000000 : ℝ)^4343
        have hw : |(-1380825327/10000000000 : ℝ)|=(1380825327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1026577819/2000000000 : ℝ)|^5367 ≤ (43860189868727/100000000000000 : ℝ)^4343
        have hw : |(1026577819/2000000000 : ℝ)|=(1026577819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(342079599/625000000 : ℝ)|^5367 ≤ (47482176951661/100000000000000 : ℝ)^4343
        have hw : |(342079599/625000000 : ℝ)|=(342079599/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s1_5 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250846117/10000000000 : ℝ)*x 0 + (-1217278809/10000000000 : ℝ)*x 1 + (1368318281/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250846117/10000000000 : ℝ)^5367 ≤ (45109132223937/100000000000000 : ℝ)^4343 := by
    have hnat : (5250846117 : ℕ)^5367*100000000000000^4343 ≤ 45109132223937^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250846117 10000000000 45109132223937 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1217278809/10000000000 : ℝ)^5367 ≤ (7408695736817/100000000000000 : ℝ)^4343 := by
    have hnat : (1217278809 : ℕ)^5367*100000000000000^4343 ≤ 7408695736817^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217278809 10000000000 7408695736817 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1368318281/2500000000 : ℝ)^5367 ≤ (9496434404023/20000000000000 : ℝ)^4343 := by
    have hnat : (1368318281 : ℕ)^5367*20000000000000^4343 ≤ 9496434404023^4343*2500000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368318281 2500000000 9496434404023 20000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250846117/10000000000 : ℝ), (-1217278809/10000000000 : ℝ), (1368318281/2500000000 : ℝ)] ![(45109132223937/100000000000000 : ℝ), (7408695736817/100000000000000 : ℝ), (9496434404023/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250846117/10000000000 : ℝ)|^5367 ≤ (45109132223937/100000000000000 : ℝ)^4343
        have hw : |(5250846117/10000000000 : ℝ)|=(5250846117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1217278809/10000000000 : ℝ)|^5367 ≤ (7408695736817/100000000000000 : ℝ)^4343
        have hw : |(-1217278809/10000000000 : ℝ)|=(1217278809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1368318281/2500000000 : ℝ)|^5367 ≤ (9496434404023/20000000000000 : ℝ)^4343
        have hw : |(1368318281/2500000000 : ℝ)|=(1368318281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s1_6 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250846383/10000000000 : ℝ)*x 0 + (5473272813/10000000000 : ℝ)*x 1 + (-1217278877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250846383/10000000000 : ℝ)^5367 ≤ (22554567523949/50000000000000 : ℝ)^4343 := by
    have hnat : (5250846383 : ℕ)^5367*50000000000000^4343 ≤ 22554567523949^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250846383 10000000000 22554567523949 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5473272813/10000000000 : ℝ)^5367 ≤ (23741084342981/50000000000000 : ℝ)^4343 := by
    have hnat : (5473272813 : ℕ)^5367*50000000000000^4343 ≤ 23741084342981^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473272813 10000000000 23741084342981 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1217278877/10000000000 : ℝ)^5367 ≤ (3704348124133/50000000000000 : ℝ)^4343 := by
    have hnat : (1217278877 : ℕ)^5367*50000000000000^4343 ≤ 3704348124133^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217278877 10000000000 3704348124133 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250846383/10000000000 : ℝ), (5473272813/10000000000 : ℝ), (-1217278877/10000000000 : ℝ)] ![(22554567523949/50000000000000 : ℝ), (23741084342981/50000000000000 : ℝ), (3704348124133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250846383/10000000000 : ℝ)|^5367 ≤ (22554567523949/50000000000000 : ℝ)^4343
        have hw : |(5250846383/10000000000 : ℝ)|=(5250846383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5473272813/10000000000 : ℝ)|^5367 ≤ (23741084342981/50000000000000 : ℝ)^4343
        have hw : |(5473272813/10000000000 : ℝ)|=(5473272813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1217278877/10000000000 : ℝ)|^5367 ≤ (3704348124133/50000000000000 : ℝ)^4343
        have hw : |(-1217278877/10000000000 : ℝ)|=(1217278877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s1_7 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (511592693/1250000000 : ℝ)*x 0 + (461480293/1000000000 : ℝ)*x 1 + (1804960687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (511592693/1250000000 : ℝ)^5367 ≤ (6630776436059/20000000000000 : ℝ)^4343 := by
    have hnat : (511592693 : ℕ)^5367*20000000000000^4343 ≤ 6630776436059^4343*1250000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511592693 1250000000 6630776436059 20000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (461480293/1000000000 : ℝ)^5367 ≤ (9614055468623/25000000000000 : ℝ)^4343 := by
    have hnat : (461480293 : ℕ)^5367*25000000000000^4343 ≤ 9614055468623^4343*1000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461480293 1000000000 9614055468623 25000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1804960687/5000000000 : ℝ)^5367 ≤ (28389895932999/100000000000000 : ℝ)^4343 := by
    have hnat : (1804960687 : ℕ)^5367*100000000000000^4343 ≤ 28389895932999^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1804960687 5000000000 28389895932999 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(511592693/1250000000 : ℝ), (461480293/1000000000 : ℝ), (1804960687/5000000000 : ℝ)] ![(6630776436059/20000000000000 : ℝ), (9614055468623/25000000000000 : ℝ), (28389895932999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(511592693/1250000000 : ℝ)|^5367 ≤ (6630776436059/20000000000000 : ℝ)^4343
        have hw : |(511592693/1250000000 : ℝ)|=(511592693/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(461480293/1000000000 : ℝ)|^5367 ≤ (9614055468623/25000000000000 : ℝ)^4343
        have hw : |(461480293/1000000000 : ℝ)|=(461480293/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1804960687/5000000000 : ℝ)|^5367 ≤ (28389895932999/100000000000000 : ℝ)^4343
        have hw : |(1804960687/5000000000 : ℝ)|=(1804960687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1718_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (197609909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21633/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3139/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9843/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17299/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (21633/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3139/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (21633/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3139/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (21633/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3139/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (21633/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3139/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (21633/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3139/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (21633/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3139/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3139/50000 : ℝ) ^ (5359/1024 : ℝ) ≤ (51111653307547/100000000000000000000 : ℝ) := by
    have hpowers : (3139/50000 : ℝ)^5359 ≤ (51111653307547/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3139 : ℕ)^5359*100000000000000000000^1024 ≤ 51111653307547^1024*50000^5359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3139 50000 51111653307547 100000000000000000000 5359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3139/50000 : ℝ)) (X := (51111653307547/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (21633/100000 : ℝ) ^ (5359/1024 : ℝ) ≤ (662874077085989/2000000000000000000 : ℝ) := by
    have hpowers : (21633/100000 : ℝ)^5359 ≤ (662874077085989/2000000000000000000 : ℝ)^1024 := by
      have hnat : (21633 : ℕ)^5359*2000000000000000000^1024 ≤ 662874077085989^1024*100000^5359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21633 100000 662874077085989 2000000000000000000 5359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21633/100000 : ℝ)) (X := (662874077085989/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000051111653307547/50000000000000000000 : ℝ) ≤ (2000000390657297/2000000000000000 : ℝ) ^ (5359/1024 : ℝ) := by
    have hpowers : (50000051111653307547/50000000000000000000 : ℝ)^1024 ≤ (2000000390657297/2000000000000000 : ℝ)^5359 := by
      have hnat : (50000051111653307547 : ℕ)^1024*2000000000000000^5359 ≤ 2000000390657297^5359*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000051111653307547 50000000000000000000 2000000390657297 2000000000000000 1024 5359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000390657297/2000000000000000 : ℝ)) (X := (50000051111653307547/50000000000000000000 : ℝ)) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100033194815507606997/100000000000000000000 : ℝ) ≤ (5000317101402373/5000000000000000 : ℝ) ^ (5359/1024 : ℝ) := by
    have hpowers : (100033194815507606997/100000000000000000000 : ℝ)^1024 ≤ (5000317101402373/5000000000000000 : ℝ)^5359 := by
      have hnat : (100033194815507606997 : ℕ)^1024*5000000000000000^5359 ≤ 5000317101402373^5359*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100033194815507606997 100000000000000000000 5000317101402373 5000000000000000 1024 5359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000317101402373/5000000000000000 : ℝ)) (X := (100033194815507606997/100000000000000000000 : ℝ)) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000662874077085989/1000000000000000000 : ℝ) ≤ (10001266452323007/10000000000000000 : ℝ) ^ (5359/1024 : ℝ) := by
    have hpowers : (1000662874077085989/1000000000000000000 : ℝ)^1024 ≤ (10001266452323007/10000000000000000 : ℝ)^5359 := by
      have hnat : (1000662874077085989 : ℕ)^1024*10000000000000000^5359 ≤ 10001266452323007^5359*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000662874077085989 1000000000000000000 10001266452323007 10000000000000000 1024 5359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001266452323007/10000000000000000 : ℝ)) (X := (1000662874077085989/1000000000000000000 : ℝ)) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(51111653307547/100000000000000000000 : ℝ) ≤ ((153542091467762692059/153550000000000000000 : ℝ)+2*(632249518261/1535500000000000 : ℝ)*(3139/50000 : ℝ))^(5359/1024 : ℝ) := by
    rw [show (153542091467762692059/153550000000000000000 : ℝ)+2*(632249518261/1535500000000000 : ℝ)*(3139/50000 : ℝ)=(2000000390657297/2000000000000000 : ℝ) by norm_num, show 1+2*(51111653307547/100000000000000000000 : ℝ)=(50000051111653307547/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(662874077085989/2000000000000000000 : ℝ)+(51111653307547/100000000000000000000 : ℝ) ≤ ((153542091467762692059/153550000000000000000 : ℝ)+(632249518261/1535500000000000 : ℝ)*((21633/100000 : ℝ)+(3139/50000 : ℝ)))^(5359/1024 : ℝ) := by
    rw [show (153542091467762692059/153550000000000000000 : ℝ)+(632249518261/1535500000000000 : ℝ)*((21633/100000 : ℝ)+(3139/50000 : ℝ))=(5000317101402373/5000000000000000 : ℝ) by norm_num, show 1+(662874077085989/2000000000000000000 : ℝ)+(51111653307547/100000000000000000000 : ℝ)=(100033194815507606997/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(662874077085989/2000000000000000000 : ℝ) ≤ ((153542091467762692059/153550000000000000000 : ℝ)+2*(632249518261/1535500000000000 : ℝ)*(21633/100000 : ℝ))^(5359/1024 : ℝ) := by
    rw [show (153542091467762692059/153550000000000000000 : ℝ)+2*(632249518261/1535500000000000 : ℝ)*(21633/100000 : ℝ)=(10001266452323007/10000000000000000 : ℝ) by norm_num, show 1+2*(662874077085989/2000000000000000000 : ℝ)=(1000662874077085989/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (153542091467762692059/153550000000000000000 : ℝ)*(X 1 0+X 2 0)+(632249518261/1535500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5359/1024 : ℝ)) (lo := (3139/50000 : ℝ)) (hi := (21633/100000 : ℝ)) (c := (153542091467762692059/153550000000000000000 : ℝ)) (alpha := (632249518261/1535500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (153542091467762692059/153550000000000000000 : ℝ)*(X 0 1+X 2 1)+(632249518261/1535500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5359/1024 : ℝ)) (lo := (3139/50000 : ℝ)) (hi := (21633/100000 : ℝ)) (c := (153542091467762692059/153550000000000000000 : ℝ)) (alpha := (632249518261/1535500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (153542091467762692059/153550000000000000000 : ℝ)*(X 0 2+X 1 2)+(632249518261/1535500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5359/1024 : ℝ)) (lo := (3139/50000 : ℝ)) (hi := (21633/100000 : ℝ)) (c := (153542091467762692059/153550000000000000000 : ℝ)) (alpha := (632249518261/1535500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1380644179/10000000000 : ℝ)*X 0 0+(2738751289/5000000000 : ℝ)*X 0 1+(2564363859/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668030047/1250000000 : ℝ)*X 1 0+(-780912541/5000000000 : ℝ)*X 1 1+(512872671/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672119569/5000000000 : ℝ)*X 2 0+(5128727663/10000000000 : ℝ)*X 2 1+(-780912737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4092211459/10000000000 : ℝ)*X 0 0+(1798719949/5000000000 : ℝ)*X 0 1+(1156772207/2500000000 : ℝ)*X 0 2+(4092211459/10000000000 : ℝ)*X 1 0+(1798719949/5000000000 : ℝ)*X 1 1+(1156772207/2500000000 : ℝ)*X 1 2+(4092211459/10000000000 : ℝ)*X 2 0+(1798719949/5000000000 : ℝ)*X 2 1+(1156772207/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1380825327/10000000000 : ℝ)*X 0 0+(1026577819/2000000000 : ℝ)*X 0 1+(342079599/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5250846117/10000000000 : ℝ)*X 1 0+(-1217278809/10000000000 : ℝ)*X 1 1+(1368318281/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5250846383/10000000000 : ℝ)*X 2 0+(5473272813/10000000000 : ℝ)*X 2 1+(-1217278877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((511592693/1250000000 : ℝ)*X 0 0+(461480293/1000000000 : ℝ)*X 0 1+(1804960687/5000000000 : ℝ)*X 0 2+(511592693/1250000000 : ℝ)*X 1 0+(461480293/1000000000 : ℝ)*X 1 1+(1804960687/5000000000 : ℝ)*X 1 2+(511592693/1250000000 : ℝ)*X 2 0+(461480293/1000000000 : ℝ)*X 2 1+(1804960687/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5329504517052521752986388713/479843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1020166053/100000000000000 : ℝ)*(base19) + (309304239/50000000000000 : ℝ)*(base23) + (93160057/100000000000000 : ℝ)*(lower2) + (28826661/25000000000000 : ℝ)*(upper3) + (235693057/100000000000000 : ℝ)*(lower4) + (239899743433681/12500000000000 : ℝ)*(major0) + (239899743433681/12500000000000 : ℝ)*(major1) + (239899743433681/12500000000000 : ℝ)*(major2) + (89599609906587/3125000000000 : ℝ)*(sp0) + (1433594592675143/50000000000000 : ℝ)*(sp1) + (286718935381167/10000000000000 : ℝ)*(sp2) + (194241063839511/20000000000000 : ℝ)*(sp3) + (1344252777/50000000000000 : ℝ)*(sp4) + (227633/97656250000 : ℝ)*(sp6) + (194241063839511/20000000000000 : ℝ)*(f.failure) + (1433595102758169/50000000000000 : ℝ)*(f.sum) + (156505649069403/76775000000000000000000000000 : ℝ)*base65 + (17241044982633439179/1919375000000000000000000000000000 : ℝ)*base67 + (23587596968298439179/1919375000000000000000000000000000 : ℝ)*base69 + (8234673169671564179/1919375000000000000000000000000000 : ℝ)*base71 + (2714451474989/38387500000000000000000000000 : ℝ)*base73 + (6383965117390939179/1919375000000000000000000000000000 : ℝ)*base75 + (4826801266990935821/1919375000000000000000000000000000 : ℝ)*base78 + (501560401880939179/1919375000000000000000000000000000 : ℝ)*base79 + (7249912293283/4798437500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/50000000000000 : ℝ)*base87 + (685501/2000000000000000000000 : ℝ)*base90 + (685501/2000000000000000000000 : ℝ)*base92 + (685501/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1893953362554850654825725837/959687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (928074363/100000000000000 : ℝ)*(base19) + (1422019369/100000000000000 : ℝ)*(base23) + (86989681/50000000000000 : ℝ)*(upper2) + (4452191/5000000000000 : ℝ)*(upper3) + (24104631/12500000000000 : ℝ)*(upper5) + (245812216984473/12500000000000 : ℝ)*(major0) + (245812216984473/12500000000000 : ℝ)*(major1) + (245812216984473/12500000000000 : ℝ)*(major2) + (227462887/4000000000000 : ℝ)*(sp1) + (3230764349/50000000000000 : ℝ)*(sp2) + (2937854147198417/100000000000000 : ℝ)*(sp4) + (1468923766275939/50000000000000 : ℝ)*(sp5) + (58756925273007/2000000000000 : ℝ)*(sp6) + (49757062938473/5000000000000 : ℝ)*(sp7) + (49757062938473/5000000000000 : ℝ)*(f.failure) + (2937854147198417/100000000000000 : ℝ)*(f.sum) + (513565736897151/76775000000000000000000000000 : ℝ)*base66 + (12175316983088074907/1919375000000000000000000000000000 : ℝ)*base67 + (23644975780673699907/1919375000000000000000000000000000 : ℝ)*base69 + (12888438977512449907/1919375000000000000000000000000000 : ℝ)*base71 + (69449966674019/19193750000000000000000000000 : ℝ)*base74 + (27703101525564949907/1919375000000000000000000000000000 : ℝ)*base75 + (2398150868632449907/1919375000000000000000000000000000 : ℝ)*base77 + (12034540982251199907/1919375000000000000000000000000000 : ℝ)*base79 + (121994680109587/38387500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2128957/500000000000000000000 : ℝ)*base89 + (2128957/500000000000000000000 : ℝ)*base91 + (2128957/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1718_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (197609909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21633/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3139/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9843/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17299/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1718_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1718_s2_0 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-691793631/5000000000 : ℝ)*x 0 + (273268183/500000000 : ℝ)*x 1 + (5138890419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (691793631/5000000000 : ℝ)^5367 ≤ (1735807660757/20000000000000 : ℝ)^4343 := by
    have hnat : (691793631 : ℕ)^5367*20000000000000^4343 ≤ 1735807660757^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691793631 5000000000 1735807660757 20000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273268183/500000000 : ℝ)^5367 ≤ (47397391074931/100000000000000 : ℝ)^4343 := by
    have hnat : (273268183 : ℕ)^5367*100000000000000^4343 ≤ 47397391074931^4343*500000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273268183 500000000 47397391074931 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138890419/10000000000 : ℝ)^5367 ≤ (43923570608891/100000000000000 : ℝ)^4343 := by
    have hnat : (5138890419 : ℕ)^5367*100000000000000^4343 ≤ 43923570608891^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138890419 10000000000 43923570608891 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-691793631/5000000000 : ℝ), (273268183/500000000 : ℝ), (5138890419/10000000000 : ℝ)] ![(1735807660757/20000000000000 : ℝ), (47397391074931/100000000000000 : ℝ), (43923570608891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-691793631/5000000000 : ℝ)|^5367 ≤ (1735807660757/20000000000000 : ℝ)^4343
        have hw : |(-691793631/5000000000 : ℝ)|=(691793631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273268183/500000000 : ℝ)|^5367 ≤ (47397391074931/100000000000000 : ℝ)^4343
        have hw : |(273268183/500000000 : ℝ)|=(273268183/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138890419/10000000000 : ℝ)|^5367 ≤ (43923570608891/100000000000000 : ℝ)^4343
        have hw : |(5138890419/10000000000 : ℝ)|=(5138890419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s2_1 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2670469501/5000000000 : ℝ)*x 0 + (-194096907/1250000000 : ℝ)*x 1 + (2569445169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2670469501/5000000000 : ℝ)^5367 ≤ (46067519896581/100000000000000 : ℝ)^4343 := by
    have hnat : (2670469501 : ℕ)^5367*100000000000000^4343 ≤ 46067519896581^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2670469501 5000000000 46067519896581 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (194096907/1250000000 : ℝ)^5367 ≤ (400356413279/4000000000000 : ℝ)^4343 := by
    have hnat : (194096907 : ℕ)^5367*4000000000000^4343 ≤ 400356413279^4343*1250000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194096907 1250000000 400356413279 4000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569445169/5000000000 : ℝ)^5367 ≤ (21961784876661/50000000000000 : ℝ)^4343 := by
    have hnat : (2569445169 : ℕ)^5367*50000000000000^4343 ≤ 21961784876661^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569445169 5000000000 21961784876661 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2670469501/5000000000 : ℝ), (-194096907/1250000000 : ℝ), (2569445169/5000000000 : ℝ)] ![(46067519896581/100000000000000 : ℝ), (400356413279/4000000000000 : ℝ), (21961784876661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2670469501/5000000000 : ℝ)|^5367 ≤ (46067519896581/100000000000000 : ℝ)^4343
        have hw : |(2670469501/5000000000 : ℝ)|=(2670469501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-194096907/1250000000 : ℝ)|^5367 ≤ (400356413279/4000000000000 : ℝ)^4343
        have hw : |(-194096907/1250000000 : ℝ)|=(194096907/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2569445169/5000000000 : ℝ)|^5367 ≤ (21961784876661/50000000000000 : ℝ)^4343
        have hw : |(2569445169/5000000000 : ℝ)|=(2569445169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s2_2 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5340938963/10000000000 : ℝ)*x 0 + (2569445169/5000000000 : ℝ)*x 1 + (-388193827/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5340938963/10000000000 : ℝ)^5367 ≤ (23033759740439/50000000000000 : ℝ)^4343 := by
    have hnat : (5340938963 : ℕ)^5367*50000000000000^4343 ≤ 23033759740439^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5340938963 10000000000 23033759740439 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569445169/5000000000 : ℝ)^5367 ≤ (21961784876661/50000000000000 : ℝ)^4343 := by
    have hnat : (2569445169 : ℕ)^5367*50000000000000^4343 ≤ 21961784876661^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569445169 5000000000 21961784876661 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (388193827/2500000000 : ℝ)^5367 ≤ (2502227686547/25000000000000 : ℝ)^4343 := by
    have hnat : (388193827 : ℕ)^5367*25000000000000^4343 ≤ 2502227686547^4343*2500000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388193827 2500000000 2502227686547 25000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5340938963/10000000000 : ℝ), (2569445169/5000000000 : ℝ), (-388193827/2500000000 : ℝ)] ![(23033759740439/50000000000000 : ℝ), (21961784876661/50000000000000 : ℝ), (2502227686547/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5340938963/10000000000 : ℝ)|^5367 ≤ (23033759740439/50000000000000 : ℝ)^4343
        have hw : |(5340938963/10000000000 : ℝ)|=(5340938963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569445169/5000000000 : ℝ)|^5367 ≤ (21961784876661/50000000000000 : ℝ)^4343
        have hw : |(2569445169/5000000000 : ℝ)|=(2569445169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-388193827/2500000000 : ℝ)|^5367 ≤ (2502227686547/25000000000000 : ℝ)^4343
        have hw : |(-388193827/2500000000 : ℝ)|=(388193827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s2_3 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4094496719/10000000000 : ℝ)*x 0 + (453769921/1250000000 : ℝ)*x 1 + (4593973539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4094496719/10000000000 : ℝ)^5367 ≤ (1658572674663/5000000000000 : ℝ)^4343 := by
    have hnat : (4094496719 : ℕ)^5367*5000000000000^4343 ≤ 1658572674663^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4094496719 10000000000 1658572674663 5000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453769921/1250000000 : ℝ)^5367 ≤ (2858671257489/10000000000000 : ℝ)^4343 := by
    have hnat : (453769921 : ℕ)^5367*10000000000000^4343 ≤ 2858671257489^4343*1250000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453769921 1250000000 2858671257489 10000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4593973539/10000000000 : ℝ)^5367 ≤ (9560458481063/25000000000000 : ℝ)^4343 := by
    have hnat : (4593973539 : ℕ)^5367*25000000000000^4343 ≤ 9560458481063^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4593973539 10000000000 9560458481063 25000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4094496719/10000000000 : ℝ), (453769921/1250000000 : ℝ), (4593973539/10000000000 : ℝ)] ![(1658572674663/5000000000000 : ℝ), (2858671257489/10000000000000 : ℝ), (9560458481063/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4094496719/10000000000 : ℝ)|^5367 ≤ (1658572674663/5000000000000 : ℝ)^4343
        have hw : |(4094496719/10000000000 : ℝ)|=(4094496719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(453769921/1250000000 : ℝ)|^5367 ≤ (2858671257489/10000000000000 : ℝ)^4343
        have hw : |(453769921/1250000000 : ℝ)|=(453769921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4593973539/10000000000 : ℝ)|^5367 ≤ (9560458481063/25000000000000 : ℝ)^4343
        have hw : |(4593973539/10000000000 : ℝ)|=(4593973539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s2_4 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-691867169/5000000000 : ℝ)*x 0 + (5142539297/10000000000 : ℝ)*x 1 + (5461660409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (691867169/5000000000 : ℝ)^5367 ≤ (1085022304123/12500000000000 : ℝ)^4343 := by
    have hnat : (691867169 : ℕ)^5367*12500000000000^4343 ≤ 1085022304123^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691867169 5000000000 1085022304123 12500000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5142539297/10000000000 : ℝ)^5367 ≤ (43962115403459/100000000000000 : ℝ)^4343 := by
    have hnat : (5142539297 : ℕ)^5367*100000000000000^4343 ≤ 43962115403459^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5142539297 10000000000 43962115403459 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5461660409/10000000000 : ℝ)^5367 ≤ (9471541229549/20000000000000 : ℝ)^4343 := by
    have hnat : (5461660409 : ℕ)^5367*20000000000000^4343 ≤ 9471541229549^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461660409 10000000000 9471541229549 20000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-691867169/5000000000 : ℝ), (5142539297/10000000000 : ℝ), (5461660409/10000000000 : ℝ)] ![(1085022304123/12500000000000 : ℝ), (43962115403459/100000000000000 : ℝ), (9471541229549/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-691867169/5000000000 : ℝ)|^5367 ≤ (1085022304123/12500000000000 : ℝ)^4343
        have hw : |(-691867169/5000000000 : ℝ)|=(691867169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5142539297/10000000000 : ℝ)|^5367 ≤ (43962115403459/100000000000000 : ℝ)^4343
        have hw : |(5142539297/10000000000 : ℝ)|=(5142539297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5461660409/10000000000 : ℝ)|^5367 ≤ (9471541229549/20000000000000 : ℝ)^4343
        have hw : |(5461660409/10000000000 : ℝ)|=(5461660409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s2_5 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5253542653/10000000000 : ℝ)*x 0 + (-246001037/2000000000 : ℝ)*x 1 + (682707551/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253542653/10000000000 : ℝ)^5367 ≤ (9027552288039/20000000000000 : ℝ)^4343 := by
    have hnat : (5253542653 : ℕ)^5367*20000000000000^4343 ≤ 9027552288039^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253542653 10000000000 9027552288039 20000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (246001037/2000000000 : ℝ)^5367 ≤ (7504532413363/100000000000000 : ℝ)^4343 := by
    have hnat : (246001037 : ℕ)^5367*100000000000000^4343 ≤ 7504532413363^4343*2000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246001037 2000000000 7504532413363 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682707551/1250000000 : ℝ)^5367 ≤ (4735770613703/10000000000000 : ℝ)^4343 := by
    have hnat : (682707551 : ℕ)^5367*10000000000000^4343 ≤ 4735770613703^4343*1250000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682707551 1250000000 4735770613703 10000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253542653/10000000000 : ℝ), (-246001037/2000000000 : ℝ), (682707551/1250000000 : ℝ)] ![(9027552288039/20000000000000 : ℝ), (7504532413363/100000000000000 : ℝ), (4735770613703/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253542653/10000000000 : ℝ)|^5367 ≤ (9027552288039/20000000000000 : ℝ)^4343
        have hw : |(5253542653/10000000000 : ℝ)|=(5253542653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-246001037/2000000000 : ℝ)|^5367 ≤ (7504532413363/100000000000000 : ℝ)^4343
        have hw : |(-246001037/2000000000 : ℝ)|=(246001037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682707551/1250000000 : ℝ)|^5367 ≤ (4735770613703/10000000000000 : ℝ)^4343
        have hw : |(682707551/1250000000 : ℝ)|=(682707551/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s2_6 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5253542651/10000000000 : ℝ)*x 0 + (546166041/1000000000 : ℝ)*x 1 + (-19218831/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253542651/10000000000 : ℝ)^5367 ≤ (45137761418959/100000000000000 : ℝ)^4343 := by
    have hnat : (5253542651 : ℕ)^5367*100000000000000^4343 ≤ 45137761418959^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253542651 10000000000 45137761418959 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546166041/1000000000 : ℝ)^5367 ≤ (47357706158461/100000000000000 : ℝ)^4343 := by
    have hnat : (546166041 : ℕ)^5367*100000000000000^4343 ≤ 47357706158461^4343*1000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546166041 1000000000 47357706158461 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19218831/156250000 : ℝ)^5367 ≤ (117258318841/1562500000000 : ℝ)^4343 := by
    have hnat : (19218831 : ℕ)^5367*1562500000000^4343 ≤ 117258318841^4343*156250000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19218831 156250000 117258318841 1562500000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253542651/10000000000 : ℝ), (546166041/1000000000 : ℝ), (-19218831/156250000 : ℝ)] ![(45137761418959/100000000000000 : ℝ), (47357706158461/100000000000000 : ℝ), (117258318841/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253542651/10000000000 : ℝ)|^5367 ≤ (45137761418959/100000000000000 : ℝ)^4343
        have hw : |(5253542651/10000000000 : ℝ)|=(5253542651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546166041/1000000000 : ℝ)|^5367 ≤ (47357706158461/100000000000000 : ℝ)^4343
        have hw : |(546166041/1000000000 : ℝ)|=(546166041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-19218831/156250000 : ℝ)|^5367 ≤ (117258318841/1562500000000 : ℝ)^4343
        have hw : |(-19218831/156250000 : ℝ)|=(19218831/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s2_7 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1023732849/2500000000 : ℝ)*x 0 + (458320121/1000000000 : ℝ)*x 1 + (3641092457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1023732849/2500000000 : ℝ)^5367 ≤ (33175805382529/100000000000000 : ℝ)^4343 := by
    have hnat : (1023732849 : ℕ)^5367*100000000000000^4343 ≤ 33175805382529^4343*2500000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023732849 2500000000 33175805382529 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458320121/1000000000 : ℝ)^5367 ≤ (38131048799359/100000000000000 : ℝ)^4343 := by
    have hnat : (458320121 : ℕ)^5367*100000000000000^4343 ≤ 38131048799359^4343*1000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458320121 1000000000 38131048799359 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3641092457/10000000000 : ℝ)^5367 ≤ (14346572900531/50000000000000 : ℝ)^4343 := by
    have hnat : (3641092457 : ℕ)^5367*50000000000000^4343 ≤ 14346572900531^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3641092457 10000000000 14346572900531 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1023732849/2500000000 : ℝ), (458320121/1000000000 : ℝ), (3641092457/10000000000 : ℝ)] ![(33175805382529/100000000000000 : ℝ), (38131048799359/100000000000000 : ℝ), (14346572900531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1023732849/2500000000 : ℝ)|^5367 ≤ (33175805382529/100000000000000 : ℝ)^4343
        have hw : |(1023732849/2500000000 : ℝ)|=(1023732849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(458320121/1000000000 : ℝ)|^5367 ≤ (38131048799359/100000000000000 : ℝ)^4343
        have hw : |(458320121/1000000000 : ℝ)|=(458320121/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3641092457/10000000000 : ℝ)|^5367 ≤ (14346572900531/50000000000000 : ℝ)^4343
        have hw : |(3641092457/10000000000 : ℝ)|=(3641092457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1718_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (197609909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17299/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2013/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4261/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17299/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9843/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17299/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9843/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17299/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9843/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17299/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9843/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17299/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9843/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17299/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9843/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9843/100000 : ℝ) ^ (5359/1024 : ℝ) ≤ (134454382492271/25000000000000000000 : ℝ) := by
    have hpowers : (9843/100000 : ℝ)^5359 ≤ (134454382492271/25000000000000000000 : ℝ)^1024 := by
      have hnat : (9843 : ℕ)^5359*25000000000000000000^1024 ≤ 134454382492271^1024*100000^5359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9843 100000 134454382492271 25000000000000000000 5359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9843/100000 : ℝ)) (X := (134454382492271/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17299/100000 : ℝ) ^ (5359/1024 : ℝ) ≤ (411453040905679/4000000000000000000 : ℝ) := by
    have hpowers : (17299/100000 : ℝ)^5359 ≤ (411453040905679/4000000000000000000 : ℝ)^1024 := by
      have hnat : (17299 : ℕ)^5359*4000000000000000000^1024 ≤ 411453040905679^1024*100000^5359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17299 100000 411453040905679 4000000000000000000 5359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17299/100000 : ℝ)) (X := (411453040905679/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500134454382492271/12500000000000000000 : ℝ) ≤ (312500642287221/312500000000000 : ℝ) ^ (5359/1024 : ℝ) := by
    have hpowers : (12500134454382492271/12500000000000000000 : ℝ)^1024 ≤ (312500642287221/312500000000000 : ℝ)^5359 := by
      have hnat : (12500134454382492271 : ℕ)^1024*312500000000000^5359 ≤ 312500642287221^5359*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500134454382492271 12500000000000000000 312500642287221 312500000000000 1024 5359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312500642287221/312500000000000 : ℝ)) (X := (12500134454382492271/12500000000000000000 : ℝ)) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100010824143552611059/100000000000000000000 : ℝ) ≤ (2000041363828263/2000000000000000 : ℝ) ^ (5359/1024 : ℝ) := by
    have hpowers : (100010824143552611059/100000000000000000000 : ℝ)^1024 ≤ (2000041363828263/2000000000000000 : ℝ)^5359 := by
      have hnat : (100010824143552611059 : ℕ)^1024*2000000000000000^5359 ≤ 2000041363828263^5359*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100010824143552611059 100000000000000000000 2000041363828263 2000000000000000 1024 5359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000041363828263/2000000000000000 : ℝ)) (X := (100010824143552611059/100000000000000000000 : ℝ)) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2000411453040905679/2000000000000000000 : ℝ) ≤ (5000196542545779/5000000000000000 : ℝ) ^ (5359/1024 : ℝ) := by
    have hpowers : (2000411453040905679/2000000000000000000 : ℝ)^1024 ≤ (5000196542545779/5000000000000000 : ℝ)^5359 := by
      have hnat : (2000411453040905679 : ℕ)^1024*5000000000000000^5359 ≤ 5000196542545779^5359*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000411453040905679 2000000000000000000 5000196542545779 5000000000000000 1024 5359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000196542545779/5000000000000000 : ℝ)) (X := (2000411453040905679/2000000000000000000 : ℝ)) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(134454382492271/25000000000000000000 : ℝ) ≤ ((37278243206548074567/37280000000000000000 : ℝ)+2*(186265950243/745600000000000 : ℝ)*(9843/100000 : ℝ))^(5359/1024 : ℝ) := by
    rw [show (37278243206548074567/37280000000000000000 : ℝ)+2*(186265950243/745600000000000 : ℝ)*(9843/100000 : ℝ)=(312500642287221/312500000000000 : ℝ) by norm_num, show 1+2*(134454382492271/25000000000000000000 : ℝ)=(12500134454382492271/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(411453040905679/4000000000000000000 : ℝ)+(134454382492271/25000000000000000000 : ℝ) ≤ ((37278243206548074567/37280000000000000000 : ℝ)+(186265950243/745600000000000 : ℝ)*((17299/100000 : ℝ)+(9843/100000 : ℝ)))^(5359/1024 : ℝ) := by
    rw [show (37278243206548074567/37280000000000000000 : ℝ)+(186265950243/745600000000000 : ℝ)*((17299/100000 : ℝ)+(9843/100000 : ℝ))=(2000041363828263/2000000000000000 : ℝ) by norm_num, show 1+(411453040905679/4000000000000000000 : ℝ)+(134454382492271/25000000000000000000 : ℝ)=(100010824143552611059/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(411453040905679/4000000000000000000 : ℝ) ≤ ((37278243206548074567/37280000000000000000 : ℝ)+2*(186265950243/745600000000000 : ℝ)*(17299/100000 : ℝ))^(5359/1024 : ℝ) := by
    rw [show (37278243206548074567/37280000000000000000 : ℝ)+2*(186265950243/745600000000000 : ℝ)*(17299/100000 : ℝ)=(5000196542545779/5000000000000000 : ℝ) by norm_num, show 1+2*(411453040905679/4000000000000000000 : ℝ)=(2000411453040905679/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37278243206548074567/37280000000000000000 : ℝ)*(X 1 0+X 2 0)+(186265950243/745600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5359/1024 : ℝ)) (lo := (9843/100000 : ℝ)) (hi := (17299/100000 : ℝ)) (c := (37278243206548074567/37280000000000000000 : ℝ)) (alpha := (186265950243/745600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37278243206548074567/37280000000000000000 : ℝ)*(X 0 1+X 2 1)+(186265950243/745600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5359/1024 : ℝ)) (lo := (9843/100000 : ℝ)) (hi := (17299/100000 : ℝ)) (c := (37278243206548074567/37280000000000000000 : ℝ)) (alpha := (186265950243/745600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37278243206548074567/37280000000000000000 : ℝ)*(X 0 2+X 1 2)+(186265950243/745600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5359/1024 : ℝ)) (lo := (9843/100000 : ℝ)) (hi := (17299/100000 : ℝ)) (c := (37278243206548074567/37280000000000000000 : ℝ)) (alpha := (186265950243/745600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-691793631/5000000000 : ℝ)*X 0 0+(273268183/500000000 : ℝ)*X 0 1+(5138890419/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2670469501/5000000000 : ℝ)*X 1 0+(-194096907/1250000000 : ℝ)*X 1 1+(2569445169/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5340938963/10000000000 : ℝ)*X 2 0+(2569445169/5000000000 : ℝ)*X 2 1+(-388193827/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4094496719/10000000000 : ℝ)*X 0 0+(453769921/1250000000 : ℝ)*X 0 1+(4593973539/10000000000 : ℝ)*X 0 2+(4094496719/10000000000 : ℝ)*X 1 0+(453769921/1250000000 : ℝ)*X 1 1+(4593973539/10000000000 : ℝ)*X 1 2+(4094496719/10000000000 : ℝ)*X 2 0+(453769921/1250000000 : ℝ)*X 2 1+(4593973539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-691867169/5000000000 : ℝ)*X 0 0+(5142539297/10000000000 : ℝ)*X 0 1+(5461660409/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5253542653/10000000000 : ℝ)*X 1 0+(-246001037/2000000000 : ℝ)*X 1 1+(682707551/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5253542651/10000000000 : ℝ)*X 2 0+(546166041/1000000000 : ℝ)*X 2 1+(-19218831/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1023732849/2500000000 : ℝ)*X 0 0+(458320121/1000000000 : ℝ)*X 0 1+(3641092457/10000000000 : ℝ)*X 0 2+(1023732849/2500000000 : ℝ)*X 1 0+(458320121/1000000000 : ℝ)*X 1 1+(3641092457/10000000000 : ℝ)*X 1 2+(1023732849/2500000000 : ℝ)*X 2 0+(458320121/1000000000 : ℝ)*X 2 1+(3641092457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (309955972260787230093692001/93200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (568191637/100000000000000 : ℝ)*(base19) + (6046981/1250000000000 : ℝ)*(base23) + (128827141/100000000000000 : ℝ)*(upper3) + (33149353/100000000000000 : ℝ)*(upper4) + (12754847/25000000000000 : ℝ)*(upper5) + (102514869641699/5000000000000 : ℝ)*(major0) + (102514869641699/5000000000000 : ℝ)*(major1) + (102514869641699/5000000000000 : ℝ)*(major2) + (3063043011988703/100000000000000 : ℝ)*(sp0) + (765761560281367/25000000000000 : ℝ)*(sp1) + (95720197673707/3125000000000 : ℝ)*(sp2) + (103754585935443/10000000000000 : ℝ)*(sp3) + (3797328401/100000000000000 : ℝ)*(sp4) + (2006139491/100000000000000 : ℝ)*(sp7) + (1037547865493921/100000000000000 : ℝ)*(f.failure) + (191440425582319/6250000000000 : ℝ)*(f.sum) + (6523976042809/1864000000000000000000000000 : ℝ)*base65 + (1223047606774619333/186400000000000000000000000000000 : ℝ)*base67 + (714535676400219333/186400000000000000000000000000000 : ℝ)*base69 + (1104332034938619333/186400000000000000000000000000000 : ℝ)*base71 + (8172638076569/1864000000000000000000000000 : ℝ)*base73 + (1159719234794980667/186400000000000000000000000000000 : ℝ)*base76 + (1244958909812219333/186400000000000000000000000000000 : ℝ)*base77 + (242572317669380667/186400000000000000000000000000000 : ℝ)*base80 + (746972024097/1864000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (31136811/10000000000000000000000 : ℝ)*base90 + (31136811/10000000000000000000000 : ℝ)*base92 + (31136811/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33980583009428413841037/3728000000000000000000000000 : ℝ) := by norm_num
    linear_combination (620965793/50000000000000 : ℝ)*(base19) + (1337205861/100000000000000 : ℝ)*(base23) + (194276083/100000000000000 : ℝ)*(upper3) + (21651203/50000000000000 : ℝ)*(lower4) + (190824301/100000000000000 : ℝ)*(upper5) + (209752733036037/10000000000000 : ℝ)*(major0) + (209752733036037/10000000000000 : ℝ)*(major1) + (209752733036037/10000000000000 : ℝ)*(major2) + (91468527/800000000000 : ℝ)*(sp1) + (2455532737/20000000000000 : ℝ)*(sp2) + (156680294984291/5000000000000 : ℝ)*(sp4) + (78339830604709/2500000000000 : ℝ)*(sp5) + (1566796142408137/50000000000000 : ℝ)*(sp6) + (1061448457202807/100000000000000 : ℝ)*(sp7) + (1061448457202807/100000000000000 : ℝ)*(f.failure) + (156680294984291/5000000000000 : ℝ)*(f.sum) + (3361039535389/745600000000000000000000000 : ℝ)*base66 + (1168322414195720979/372800000000000000000000000000000 : ℝ)*base67 + (645633722407479021/372800000000000000000000000000000 : ℝ)*base70 + (2348575631141879021/372800000000000000000000000000000 : ℝ)*base72 + (652208183631/3728000000000000000000000000 : ℝ)*base73 + (286912980407479021/372800000000000000000000000000000 : ℝ)*base76 + (1120445726670920979/372800000000000000000000000000000 : ℝ)*base77 + (204328967971720979/372800000000000000000000000000000 : ℝ)*base79 + (25025926011393/3728000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (85814563/10000000000000000000000 : ℝ)*base89 + (85814563/10000000000000000000000 : ℝ)*base91 + (85814563/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1718_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (197609909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17299/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2013/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4261/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1718_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1718_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (197609909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2013/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4261/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1718_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1718_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1718_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (197609909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2013/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4261/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1718_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

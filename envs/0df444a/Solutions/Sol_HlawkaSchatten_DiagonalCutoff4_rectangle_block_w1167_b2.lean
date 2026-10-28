-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1167_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:43:11.847263+00:00
-- url     : https://prove2.me/submissions/993f6187-61b7-4dc1-816d-bdc7598b0a8a

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
theorem support_rectangle_w1167_s6_0 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2154962481/10000000000 : ℝ)*x 0 + (1348220647/2500000000 : ℝ)*x 1 + (210633953/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154962481/10000000000 : ℝ)^1045 ≤ (13096844379631/100000000000000 : ℝ)^789 := by
    have hnat : (2154962481 : ℕ)^1045*100000000000000^789 ≤ 13096844379631^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154962481 10000000000 13096844379631 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348220647/2500000000 : ℝ)^1045 ≤ (44137449646987/100000000000000 : ℝ)^789 := by
    have hnat : (1348220647 : ℕ)^1045*100000000000000^789 ≤ 44137449646987^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348220647 2500000000 44137449646987 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210633953/400000000 : ℝ)^1045 ≤ (42765705962011/100000000000000 : ℝ)^789 := by
    have hnat : (210633953 : ℕ)^1045*100000000000000^789 ≤ 42765705962011^789*400000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210633953 400000000 42765705962011 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2154962481/10000000000 : ℝ), (1348220647/2500000000 : ℝ), (210633953/400000000 : ℝ)] ![(13096844379631/100000000000000 : ℝ), (44137449646987/100000000000000 : ℝ), (42765705962011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2154962481/10000000000 : ℝ)|^1045 ≤ (13096844379631/100000000000000 : ℝ)^789
        have hw : |(-2154962481/10000000000 : ℝ)|=(2154962481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348220647/2500000000 : ℝ)|^1045 ≤ (44137449646987/100000000000000 : ℝ)^789
        have hw : |(1348220647/2500000000 : ℝ)|=(1348220647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210633953/400000000 : ℝ)|^1045 ≤ (42765705962011/100000000000000 : ℝ)^789
        have hw : |(210633953/400000000 : ℝ)|=(210633953/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s6_1 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (334046039/625000000 : ℝ)*x 0 + (-88775773/400000000 : ℝ)*x 1 + (164557777/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334046039/625000000 : ℝ)^1045 ≤ (5452038660829/12500000000000 : ℝ)^789 := by
    have hnat : (334046039 : ℕ)^1045*12500000000000^789 ≤ 5452038660829^789*625000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334046039 625000000 5452038660829 12500000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88775773/400000000 : ℝ)^1045 ≤ (6808992154227/50000000000000 : ℝ)^789 := by
    have hnat : (88775773 : ℕ)^1045*50000000000000^789 ≤ 6808992154227^789*400000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88775773 400000000 6808992154227 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164557777/312500000 : ℝ)^1045 ≤ (42765706381511/100000000000000 : ℝ)^789 := by
    have hnat : (164557777 : ℕ)^1045*100000000000000^789 ≤ 42765706381511^789*312500000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164557777 312500000 42765706381511 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334046039/625000000 : ℝ), (-88775773/400000000 : ℝ), (164557777/312500000 : ℝ)] ![(5452038660829/12500000000000 : ℝ), (6808992154227/50000000000000 : ℝ), (42765706381511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334046039/625000000 : ℝ)|^1045 ≤ (5452038660829/12500000000000 : ℝ)^789
        have hw : |(334046039/625000000 : ℝ)|=(334046039/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-88775773/400000000 : ℝ)|^1045 ≤ (6808992154227/50000000000000 : ℝ)^789
        have hw : |(-88775773/400000000 : ℝ)|=(88775773/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164557777/312500000 : ℝ)|^1045 ≤ (42765706381511/100000000000000 : ℝ)^789
        have hw : |(164557777/312500000 : ℝ)|=(164557777/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s6_2 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672368369/5000000000 : ℝ)*x 0 + (2632924347/5000000000 : ℝ)*x 1 + (-2774243/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672368369/5000000000 : ℝ)^1045 ≤ (4361631051879/10000000000000 : ℝ)^789 := by
    have hnat : (2672368369 : ℕ)^1045*10000000000000^789 ≤ 4361631051879^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672368369 5000000000 4361631051879 10000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632924347/5000000000 : ℝ)^1045 ≤ (10691426138231/25000000000000 : ℝ)^789 := by
    have hnat : (2632924347 : ℕ)^1045*25000000000000^789 ≤ 10691426138231^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632924347 5000000000 10691426138231 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2774243/12500000 : ℝ)^1045 ≤ (6808992458981/50000000000000 : ℝ)^789 := by
    have hnat : (2774243 : ℕ)^1045*50000000000000^789 ≤ 6808992458981^789*12500000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2774243 12500000 6808992458981 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672368369/5000000000 : ℝ), (2632924347/5000000000 : ℝ), (-2774243/12500000 : ℝ)] ![(4361631051879/10000000000000 : ℝ), (10691426138231/25000000000000 : ℝ), (6808992458981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672368369/5000000000 : ℝ)|^1045 ≤ (4361631051879/10000000000000 : ℝ)^789
        have hw : |(2672368369/5000000000 : ℝ)|=(2672368369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632924347/5000000000 : ℝ)|^1045 ≤ (10691426138231/25000000000000 : ℝ)^789
        have hw : |(2632924347/5000000000 : ℝ)|=(2632924347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2774243/12500000 : ℝ)|^1045 ≤ (6808992458981/50000000000000 : ℝ)^789
        have hw : |(-2774243/12500000 : ℝ)|=(2774243/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s6_3 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4361148239/10000000000 : ℝ)*x 0 + (2117995781/5000000000 : ℝ)*x 1 + (2244981181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361148239/10000000000 : ℝ)^1045 ≤ (33316951468677/100000000000000 : ℝ)^789 := by
    have hnat : (4361148239 : ℕ)^1045*100000000000000^789 ≤ 33316951468677^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361148239 10000000000 33316951468677 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117995781/5000000000 : ℝ)^1045 ≤ (16028262145841/50000000000000 : ℝ)^789 := by
    have hnat : (2117995781 : ℕ)^1045*50000000000000^789 ≤ 16028262145841^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117995781 5000000000 16028262145841 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244981181/5000000000 : ℝ)^1045 ≤ (17313262118279/50000000000000 : ℝ)^789 := by
    have hnat : (2244981181 : ℕ)^1045*50000000000000^789 ≤ 17313262118279^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244981181 5000000000 17313262118279 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361148239/10000000000 : ℝ), (2117995781/5000000000 : ℝ), (2244981181/5000000000 : ℝ)] ![(33316951468677/100000000000000 : ℝ), (16028262145841/50000000000000 : ℝ), (17313262118279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361148239/10000000000 : ℝ)|^1045 ≤ (33316951468677/100000000000000 : ℝ)^789
        have hw : |(4361148239/10000000000 : ℝ)|=(4361148239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2117995781/5000000000 : ℝ)|^1045 ≤ (16028262145841/50000000000000 : ℝ)^789
        have hw : |(2117995781/5000000000 : ℝ)|=(2117995781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2244981181/5000000000 : ℝ)|^1045 ≤ (17313262118279/50000000000000 : ℝ)^789
        have hw : |(2244981181/5000000000 : ℝ)|=(2244981181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s6_4 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-215496751/1000000000 : ℝ)*x 0 + (5266169581/10000000000 : ℝ)*x 1 + (2696280281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215496751/1000000000 : ℝ)^1045 ≤ (6548442430167/50000000000000 : ℝ)^789 := by
    have hnat : (215496751 : ℕ)^1045*50000000000000^789 ≤ 6548442430167^789*1000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215496751 1000000000 6548442430167 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266169581/10000000000 : ℝ)^1045 ≤ (2138457808639/5000000000000 : ℝ)^789 := by
    have hnat : (5266169581 : ℕ)^1045*5000000000000^789 ≤ 2138457808639^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266169581 10000000000 2138457808639 5000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696280281/5000000000 : ℝ)^1045 ≤ (44133958948903/100000000000000 : ℝ)^789 := by
    have hnat : (2696280281 : ℕ)^1045*100000000000000^789 ≤ 44133958948903^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696280281 5000000000 44133958948903 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215496751/1000000000 : ℝ), (5266169581/10000000000 : ℝ), (2696280281/5000000000 : ℝ)] ![(6548442430167/50000000000000 : ℝ), (2138457808639/5000000000000 : ℝ), (44133958948903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215496751/1000000000 : ℝ)|^1045 ≤ (6548442430167/50000000000000 : ℝ)^789
        have hw : |(-215496751/1000000000 : ℝ)|=(215496751/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266169581/10000000000 : ℝ)|^1045 ≤ (2138457808639/5000000000000 : ℝ)^789
        have hw : |(5266169581/10000000000 : ℝ)|=(5266169581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696280281/5000000000 : ℝ)|^1045 ≤ (44133958948903/100000000000000 : ℝ)^789
        have hw : |(2696280281/5000000000 : ℝ)|=(2696280281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s6_5 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (265624657/500000000 : ℝ)*x 0 + (-1046341281/5000000000 : ℝ)*x 1 + (5392560549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265624657/500000000 : ℝ)^1045 ≤ (21634074983997/50000000000000 : ℝ)^789 := by
    have hnat : (265624657 : ℕ)^1045*50000000000000^789 ≤ 21634074983997^789*500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265624657 500000000 21634074983997 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046341281/5000000000 : ℝ)^1045 ≤ (12597891205621/100000000000000 : ℝ)^789 := by
    have hnat : (1046341281 : ℕ)^1045*100000000000000^789 ≤ 12597891205621^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046341281 5000000000 12597891205621 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392560549/10000000000 : ℝ)^1045 ≤ (44133958807987/100000000000000 : ℝ)^789 := by
    have hnat : (5392560549 : ℕ)^1045*100000000000000^789 ≤ 44133958807987^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392560549 10000000000 44133958807987 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265624657/500000000 : ℝ), (-1046341281/5000000000 : ℝ), (5392560549/10000000000 : ℝ)] ![(21634074983997/50000000000000 : ℝ), (12597891205621/100000000000000 : ℝ), (44133958807987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265624657/500000000 : ℝ)|^1045 ≤ (21634074983997/50000000000000 : ℝ)^789
        have hw : |(265624657/500000000 : ℝ)|=(265624657/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1046341281/5000000000 : ℝ)|^1045 ≤ (12597891205621/100000000000000 : ℝ)^789
        have hw : |(-1046341281/5000000000 : ℝ)|=(1046341281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392560549/10000000000 : ℝ)|^1045 ≤ (44133958807987/100000000000000 : ℝ)^789
        have hw : |(5392560549/10000000000 : ℝ)|=(5392560549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s6_6 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656246571/5000000000 : ℝ)*x 0 + (2696280259/5000000000 : ℝ)*x 1 + (-1046341301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656246571/5000000000 : ℝ)^1045 ≤ (43268149989569/100000000000000 : ℝ)^789 := by
    have hnat : (2656246571 : ℕ)^1045*100000000000000^789 ≤ 43268149989569^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656246571 5000000000 43268149989569 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696280259/5000000000 : ℝ)^1045 ≤ (44133958471957/100000000000000 : ℝ)^789 := by
    have hnat : (2696280259 : ℕ)^1045*100000000000000^789 ≤ 44133958471957^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696280259 5000000000 44133958471957 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046341301/5000000000 : ℝ)^1045 ≤ (12597891524549/100000000000000 : ℝ)^789 := by
    have hnat : (1046341301 : ℕ)^1045*100000000000000^789 ≤ 12597891524549^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046341301 5000000000 12597891524549 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656246571/5000000000 : ℝ), (2696280259/5000000000 : ℝ), (-1046341301/5000000000 : ℝ)] ![(43268149989569/100000000000000 : ℝ), (44133958471957/100000000000000 : ℝ), (12597891524549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656246571/5000000000 : ℝ)|^1045 ≤ (43268149989569/100000000000000 : ℝ)^789
        have hw : |(2656246571/5000000000 : ℝ)|=(2656246571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696280259/5000000000 : ℝ)|^1045 ≤ (44133958471957/100000000000000 : ℝ)^789
        have hw : |(2696280259/5000000000 : ℝ)|=(2696280259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1046341301/5000000000 : ℝ)|^1045 ≤ (12597891524549/100000000000000 : ℝ)^789
        have hw : |(-1046341301/5000000000 : ℝ)|=(1046341301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s6_7 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4361157797/10000000000 : ℝ)*x 0 + (280582547/625000000 : ℝ)*x 1 + (264789733/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361157797/10000000000 : ℝ)^1045 ≤ (8329262044641/25000000000000 : ℝ)^789 := by
    have hnat : (4361157797 : ℕ)^1045*25000000000000^789 ≤ 8329262044641^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361157797 10000000000 8329262044641 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280582547/625000000 : ℝ)^1045 ≤ (8654992709647/25000000000000 : ℝ)^789 := by
    have hnat : (280582547 : ℕ)^1045*25000000000000^789 ≤ 8654992709647^789*625000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280582547 625000000 8654992709647 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264789733/625000000 : ℝ)^1045 ≤ (16031490484969/50000000000000 : ℝ)^789 := by
    have hnat : (264789733 : ℕ)^1045*50000000000000^789 ≤ 16031490484969^789*625000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264789733 625000000 16031490484969 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361157797/10000000000 : ℝ), (280582547/625000000 : ℝ), (264789733/625000000 : ℝ)] ![(8329262044641/25000000000000 : ℝ), (8654992709647/25000000000000 : ℝ), (16031490484969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361157797/10000000000 : ℝ)|^1045 ≤ (8329262044641/25000000000000 : ℝ)^789
        have hw : |(4361157797/10000000000 : ℝ)|=(4361157797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280582547/625000000 : ℝ)|^1045 ≤ (8654992709647/25000000000000 : ℝ)^789
        have hw : |(280582547/625000000 : ℝ)|=(280582547/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264789733/625000000 : ℝ)|^1045 ≤ (16031490484969/50000000000000 : ℝ)^789
        have hw : |(264789733/625000000 : ℝ)|=(264789733/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1167_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11379/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1407/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14099/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11351/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14099/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11351/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14099/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11351/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14099/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11351/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14099/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11351/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14099/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11351/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11351/100000 : ℝ) ^ (8359/2048 : ℝ) ≤ (13902124444782599/100000000000000000000 : ℝ) := by
    have hpowers : (11351/100000 : ℝ)^8359 ≤ (13902124444782599/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11351 : ℕ)^8359*100000000000000000000^2048 ≤ 13902124444782599^2048*100000^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11351 100000 13902124444782599 100000000000000000000 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11351/100000 : ℝ)) (X := (13902124444782599/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14099/100000 : ℝ) ^ (8359/2048 : ℝ) ≤ (1684013371060143/5000000000000000000 : ℝ) := by
    have hpowers : (14099/100000 : ℝ)^8359 ≤ (1684013371060143/5000000000000000000 : ℝ)^2048 := by
      have hnat : (14099 : ℕ)^8359*5000000000000000000^2048 ≤ 1684013371060143^2048*100000^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14099 100000 1684013371060143 5000000000000000000 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14099/100000 : ℝ)) (X := (1684013371060143/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013902124444782599/50000000000000000000 : ℝ) ≤ (10000681147576663/10000000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (50013902124444782599/50000000000000000000 : ℝ)^2048 ≤ (10000681147576663/10000000000000000 : ℝ)^8359 := by
      have hnat : (50013902124444782599 : ℕ)^2048*10000000000000000^8359 ≤ 10000681147576663^8359*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013902124444782599 50000000000000000000 10000681147576663 10000000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000681147576663/10000000000000000 : ℝ)) (X := (50013902124444782599/50000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047582391865985459/100000000000000000000 : ℝ) ≤ (2500291396218001/2500000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (100047582391865985459/100000000000000000000 : ℝ)^2048 ≤ (2500291396218001/2500000000000000 : ℝ)^8359 := by
      have hnat : (100047582391865985459 : ℕ)^2048*2500000000000000^8359 ≤ 2500291396218001^8359*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047582391865985459 100000000000000000000 2500291396218001 2500000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500291396218001/2500000000000000 : ℝ)) (X := (100047582391865985459/100000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501684013371060143/2500000000000000000 : ℝ) ≤ (2000330004433469/2000000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (2501684013371060143/2500000000000000000 : ℝ)^2048 ≤ (2000330004433469/2000000000000000 : ℝ)^8359 := by
      have hnat : (2501684013371060143 : ℕ)^2048*2000000000000000^8359 ≤ 2000330004433469^8359*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501684013371060143 2500000000000000000 2000330004433469 2000000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000330004433469/2000000000000000 : ℝ)) (X := (2501684013371060143/2500000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13902124444782599/100000000000000000000 : ℝ) ≤ ((4578479016343639757/4580000000000000000 : ℝ)+2*(161479098447/91600000000000 : ℝ)*(11351/100000 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (4578479016343639757/4580000000000000000 : ℝ)+2*(161479098447/91600000000000 : ℝ)*(11351/100000 : ℝ)=(10000681147576663/10000000000000000 : ℝ) by norm_num, show 1+2*(13902124444782599/100000000000000000000 : ℝ)=(50013902124444782599/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1684013371060143/5000000000000000000 : ℝ)+(13902124444782599/100000000000000000000 : ℝ) ≤ ((4578479016343639757/4580000000000000000 : ℝ)+(161479098447/91600000000000 : ℝ)*((14099/100000 : ℝ)+(11351/100000 : ℝ)))^(8359/2048 : ℝ) := by
    rw [show (4578479016343639757/4580000000000000000 : ℝ)+(161479098447/91600000000000 : ℝ)*((14099/100000 : ℝ)+(11351/100000 : ℝ))=(2500291396218001/2500000000000000 : ℝ) by norm_num, show 1+(1684013371060143/5000000000000000000 : ℝ)+(13902124444782599/100000000000000000000 : ℝ)=(100047582391865985459/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1684013371060143/5000000000000000000 : ℝ) ≤ ((4578479016343639757/4580000000000000000 : ℝ)+2*(161479098447/91600000000000 : ℝ)*(14099/100000 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (4578479016343639757/4580000000000000000 : ℝ)+2*(161479098447/91600000000000 : ℝ)*(14099/100000 : ℝ)=(2000330004433469/2000000000000000 : ℝ) by norm_num, show 1+2*(1684013371060143/5000000000000000000 : ℝ)=(2501684013371060143/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4578479016343639757/4580000000000000000 : ℝ)*(X 1 0+X 2 0)+(161479098447/91600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (11351/100000 : ℝ)) (hi := (14099/100000 : ℝ)) (c := (4578479016343639757/4580000000000000000 : ℝ)) (alpha := (161479098447/91600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4578479016343639757/4580000000000000000 : ℝ)*(X 0 1+X 2 1)+(161479098447/91600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (11351/100000 : ℝ)) (hi := (14099/100000 : ℝ)) (c := (4578479016343639757/4580000000000000000 : ℝ)) (alpha := (161479098447/91600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4578479016343639757/4580000000000000000 : ℝ)*(X 0 2+X 1 2)+(161479098447/91600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (11351/100000 : ℝ)) (hi := (14099/100000 : ℝ)) (c := (4578479016343639757/4580000000000000000 : ℝ)) (alpha := (161479098447/91600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2154962481/10000000000 : ℝ)*X 0 0+(1348220647/2500000000 : ℝ)*X 0 1+(210633953/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334046039/625000000 : ℝ)*X 1 0+(-88775773/400000000 : ℝ)*X 1 1+(164557777/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672368369/5000000000 : ℝ)*X 2 0+(2632924347/5000000000 : ℝ)*X 2 1+(-2774243/12500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361148239/10000000000 : ℝ)*X 0 0+(2117995781/5000000000 : ℝ)*X 0 1+(2244981181/5000000000 : ℝ)*X 0 2+(4361148239/10000000000 : ℝ)*X 1 0+(2117995781/5000000000 : ℝ)*X 1 1+(2244981181/5000000000 : ℝ)*X 1 2+(4361148239/10000000000 : ℝ)*X 2 0+(2117995781/5000000000 : ℝ)*X 2 1+(2244981181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-215496751/1000000000 : ℝ)*X 0 0+(5266169581/10000000000 : ℝ)*X 0 1+(2696280281/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265624657/500000000 : ℝ)*X 1 0+(-1046341281/5000000000 : ℝ)*X 1 1+(5392560549/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656246571/5000000000 : ℝ)*X 2 0+(2696280259/5000000000 : ℝ)*X 2 1+(-1046341301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4361157797/10000000000 : ℝ)*X 0 0+(280582547/625000000 : ℝ)*X 0 1+(264789733/625000000 : ℝ)*X 0 2+(4361157797/10000000000 : ℝ)*X 1 0+(280582547/625000000 : ℝ)*X 1 1+(264789733/625000000 : ℝ)*X 1 2+(4361157797/10000000000 : ℝ)*X 2 0+(280582547/625000000 : ℝ)*X 2 1+(264789733/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1954663894768563572279219829/229000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (697013669/50000000000000 : ℝ)*(base19) + (311995603/25000000000000 : ℝ)*(base23) + (37020491/20000000000000 : ℝ)*(lower2) + (80141677/25000000000000 : ℝ)*(upper3) + (4326153/25000000000000 : ℝ)*(lower4) + (5904746700624033/100000000000000 : ℝ)*(major0) + (5904746700624033/100000000000000 : ℝ)*(major1) + (5904746700624033/100000000000000 : ℝ)*(major2) + (3935980655546153/50000000000000 : ℝ)*(sp0) + (7871989124119899/100000000000000 : ℝ)*(sp1) + (314879570806593/4000000000000 : ℝ)*(sp2) + (1968738493653857/50000000000000 : ℝ)*(sp3) + (29207054931/100000000000000 : ℝ)*(sp4) + (25611271431/100000000000000 : ℝ)*(sp7) + (1968751299289573/50000000000000 : ℝ)*(f.failure) + (7871990518147237/100000000000000 : ℝ)*(f.sum) + (24413286542309/4580000000000000000000000000 : ℝ)*base66 + (5808100805015970019/458000000000000000000000000000000 : ℝ)*base68 + (5513309878577970019/458000000000000000000000000000000 : ℝ)*base70 + (1746294329795970019/458000000000000000000000000000000 : ℝ)*base72 + (8068283522149/4580000000000000000000000000 : ℝ)*base74 + (2332075341889970019/458000000000000000000000000000000 : ℝ)*base76 + (7031779152087970019/458000000000000000000000000000000 : ℝ)*base78 + (5979652358653970019/458000000000000000000000000000000 : ℝ)*base80 + (1364056764129/4580000000000000000000000000 : ℝ)*base82 + (46862353/2500000000000000000000 : ℝ)*base89 + (46862353/2500000000000000000000 : ℝ)*base91 + (46862353/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (701687563540401818532279861/114500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1034544427/100000000000000 : ℝ)*(base19) + (1030350393/100000000000000 : ℝ)*(base23) + (10530059/100000000000000 : ℝ)*(upper2) + (45201727/50000000000000 : ℝ)*(upper3) + (37805619/25000000000000 : ℝ)*(upper5) + (2967363561144097/50000000000000 : ℝ)*(major0) + (2967363561144097/50000000000000 : ℝ)*(major1) + (2967363561144097/50000000000000 : ℝ)*(major2) + (29671381807/100000000000000 : ℝ)*(sp1) + (12611860049/50000000000000 : ℝ)*(sp2) + (1977989848060201/25000000000000 : ℝ)*(sp4) + (1977982171578643/25000000000000 : ℝ)*(sp5) + (7911933138170313/100000000000000 : ℝ)*(sp6) + (3957494648059719/100000000000000 : ℝ)*(sp7) + (3957494648059719/100000000000000 : ℝ)*(f.failure) + (1977989848060201/25000000000000 : ℝ)*(f.sum) + (3760424379511/2290000000000000000000000000 : ℝ)*base66 + (208929884944985571/229000000000000000000000000000000 : ℝ)*base68 + (2137829052116985571/229000000000000000000000000000000 : ℝ)*base70 + (3899412104235985571/229000000000000000000000000000000 : ℝ)*base72 + (2915271534149/2290000000000000000000000000 : ℝ)*base73 + (6812787435128985571/229000000000000000000000000000000 : ℝ)*base76 + (1347852454173985571/229000000000000000000000000000000 : ℝ)*base78 + (1369174648982985571/229000000000000000000000000000000 : ℝ)*base80 + (3397671811619/2290000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base85 + (10038059/5000000000000000000000 : ℝ)*base89 + (10038059/5000000000000000000000 : ℝ)*base91 + (10038059/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1167_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1167_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1167_s7_0 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1077493091/5000000000 : ℝ)*x 0 + (5392598147/10000000000 : ℝ)*x 1 + (5266117733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077493091/5000000000 : ℝ)^1045 ≤ (13097035160001/100000000000000 : ℝ)^789 := by
    have hnat : (1077493091 : ℕ)^1045*100000000000000^789 ≤ 13097035160001^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077493091 5000000000 13097035160001 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392598147/10000000000 : ℝ)^1045 ≤ (2758397897461/6250000000000 : ℝ)^789 := by
    have hnat : (5392598147 : ℕ)^1045*6250000000000^789 ≤ 2758397897461^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392598147 10000000000 2758397897461 6250000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266117733/10000000000 : ℝ)^1045 ≤ (42768598465333/100000000000000 : ℝ)^789 := by
    have hnat : (5266117733 : ℕ)^1045*100000000000000^789 ≤ 42768598465333^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266117733 10000000000 42768598465333 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1077493091/5000000000 : ℝ), (5392598147/10000000000 : ℝ), (5266117733/10000000000 : ℝ)] ![(13097035160001/100000000000000 : ℝ), (2758397897461/6250000000000 : ℝ), (42768598465333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1077493091/5000000000 : ℝ)|^1045 ≤ (13097035160001/100000000000000 : ℝ)^789
        have hw : |(-1077493091/5000000000 : ℝ)|=(1077493091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392598147/10000000000 : ℝ)|^1045 ≤ (2758397897461/6250000000000 : ℝ)^789
        have hw : |(5392598147/10000000000 : ℝ)|=(5392598147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266117733/10000000000 : ℝ)|^1045 ≤ (42768598465333/100000000000000 : ℝ)^789
        have hw : |(5266117733/10000000000 : ℝ)|=(5266117733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s7_1 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1068933067/2000000000 : ℝ)*x 0 + (-1109566631/5000000000 : ℝ)*x 1 + (5266117733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068933067/2000000000 : ℝ)^1045 ≤ (21807769383707/50000000000000 : ℝ)^789 := by
    have hnat : (1068933067 : ℕ)^1045*50000000000000^789 ≤ 21807769383707^789*2000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068933067 2000000000 21807769383707 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1109566631/5000000000 : ℝ)^1045 ≤ (3403965687891/25000000000000 : ℝ)^789 := by
    have hnat : (1109566631 : ℕ)^1045*25000000000000^789 ≤ 3403965687891^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109566631 5000000000 3403965687891 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266117733/10000000000 : ℝ)^1045 ≤ (42768598465333/100000000000000 : ℝ)^789 := by
    have hnat : (5266117733 : ℕ)^1045*100000000000000^789 ≤ 42768598465333^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266117733 10000000000 42768598465333 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068933067/2000000000 : ℝ), (-1109566631/5000000000 : ℝ), (5266117733/10000000000 : ℝ)] ![(21807769383707/50000000000000 : ℝ), (3403965687891/25000000000000 : ℝ), (42768598465333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068933067/2000000000 : ℝ)|^1045 ≤ (21807769383707/50000000000000 : ℝ)^789
        have hw : |(1068933067/2000000000 : ℝ)|=(1068933067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1109566631/5000000000 : ℝ)|^1045 ≤ (3403965687891/25000000000000 : ℝ)^789
        have hw : |(-1109566631/5000000000 : ℝ)|=(1109566631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266117733/10000000000 : ℝ)|^1045 ≤ (42768598465333/100000000000000 : ℝ)^789
        have hw : |(5266117733/10000000000 : ℝ)|=(5266117733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s7_2 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1068933067/2000000000 : ℝ)*x 0 + (5266117733/10000000000 : ℝ)*x 1 + (-1109566631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068933067/2000000000 : ℝ)^1045 ≤ (21807769383707/50000000000000 : ℝ)^789 := by
    have hnat : (1068933067 : ℕ)^1045*50000000000000^789 ≤ 21807769383707^789*2000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068933067 2000000000 21807769383707 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266117733/10000000000 : ℝ)^1045 ≤ (42768598465333/100000000000000 : ℝ)^789 := by
    have hnat : (5266117733 : ℕ)^1045*100000000000000^789 ≤ 42768598465333^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266117733 10000000000 42768598465333 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1109566631/5000000000 : ℝ)^1045 ≤ (3403965687891/25000000000000 : ℝ)^789 := by
    have hnat : (1109566631 : ℕ)^1045*25000000000000^789 ≤ 3403965687891^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109566631 5000000000 3403965687891 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068933067/2000000000 : ℝ), (5266117733/10000000000 : ℝ), (-1109566631/5000000000 : ℝ)] ![(21807769383707/50000000000000 : ℝ), (42768598465333/100000000000000 : ℝ), (3403965687891/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068933067/2000000000 : ℝ)|^1045 ≤ (21807769383707/50000000000000 : ℝ)^789
        have hw : |(1068933067/2000000000 : ℝ)|=(1068933067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266117733/10000000000 : ℝ)|^1045 ≤ (42768598465333/100000000000000 : ℝ)^789
        have hw : |(5266117733/10000000000 : ℝ)|=(5266117733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1109566631/5000000000 : ℝ)|^1045 ≤ (3403965687891/25000000000000 : ℝ)^789
        have hw : |(-1109566631/5000000000 : ℝ)|=(1109566631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s7_3 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1090290541/2500000000 : ℝ)*x 0 + (264783951/625000000 : ℝ)*x 1 + (897881443/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090290541/2500000000 : ℝ)^1045 ≤ (16658546182413/50000000000000 : ℝ)^789 := by
    have hnat : (1090290541 : ℕ)^1045*50000000000000^789 ≤ 16658546182413^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090290541 2500000000 16658546182413 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264783951/625000000 : ℝ)^1045 ≤ (32062053673499/100000000000000 : ℝ)^789 := by
    have hnat : (264783951 : ℕ)^1045*100000000000000^789 ≤ 32062053673499^789*625000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264783951 625000000 32062053673499 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897881443/2000000000 : ℝ)^1045 ≤ (34620853953069/100000000000000 : ℝ)^789 := by
    have hnat : (897881443 : ℕ)^1045*100000000000000^789 ≤ 34620853953069^789*2000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897881443 2000000000 34620853953069 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090290541/2500000000 : ℝ), (264783951/625000000 : ℝ), (897881443/2000000000 : ℝ)] ![(16658546182413/50000000000000 : ℝ), (32062053673499/100000000000000 : ℝ), (34620853953069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090290541/2500000000 : ℝ)|^1045 ≤ (16658546182413/50000000000000 : ℝ)^789
        have hw : |(1090290541/2500000000 : ℝ)|=(1090290541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264783951/625000000 : ℝ)|^1045 ≤ (32062053673499/100000000000000 : ℝ)^789
        have hw : |(264783951/625000000 : ℝ)|=(264783951/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897881443/2000000000 : ℝ)|^1045 ≤ (34620853953069/100000000000000 : ℝ)^789
        have hw : |(897881443/2000000000 : ℝ)|=(897881443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s7_4 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2154991357/10000000000 : ℝ)*x 0 + (131660889/250000000 : ℝ)*x 1 + (5392278909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154991357/10000000000 : ℝ)^1045 ≤ (13097076816073/100000000000000 : ℝ)^789 := by
    have hnat : (2154991357 : ℕ)^1045*100000000000000^789 ≤ 13097076816073^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154991357 10000000000 13097076816073 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131660889/250000000 : ℝ)^1045 ≤ (21386008613329/50000000000000 : ℝ)^789 := by
    have hnat : (131660889 : ℕ)^1045*50000000000000^789 ≤ 21386008613329^789*250000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131660889 250000000 21386008613329 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392278909/10000000000 : ℝ)^1045 ≤ (44130905941593/100000000000000 : ℝ)^789 := by
    have hnat : (5392278909 : ℕ)^1045*100000000000000^789 ≤ 44130905941593^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392278909 10000000000 44130905941593 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2154991357/10000000000 : ℝ), (131660889/250000000 : ℝ), (5392278909/10000000000 : ℝ)] ![(13097076816073/100000000000000 : ℝ), (21386008613329/50000000000000 : ℝ), (44130905941593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2154991357/10000000000 : ℝ)|^1045 ≤ (13097076816073/100000000000000 : ℝ)^789
        have hw : |(-2154991357/10000000000 : ℝ)|=(2154991357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131660889/250000000 : ℝ)|^1045 ≤ (21386008613329/50000000000000 : ℝ)^789
        have hw : |(131660889/250000000 : ℝ)|=(131660889/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392278909/10000000000 : ℝ)|^1045 ≤ (44130905941593/100000000000000 : ℝ)^789
        have hw : |(5392278909/10000000000 : ℝ)|=(5392278909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s7_5 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312562623/10000000000 : ℝ)*x 0 + (-1046485957/5000000000 : ℝ)*x 1 + (33701741/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312562623/10000000000 : ℝ)^1045 ≤ (21634449748733/50000000000000 : ℝ)^789 := by
    have hnat : (5312562623 : ℕ)^1045*50000000000000^789 ≤ 21634449748733^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312562623 10000000000 21634449748733 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046485957/5000000000 : ℝ)^1045 ≤ (3150049581181/25000000000000 : ℝ)^789 := by
    have hnat : (1046485957 : ℕ)^1045*25000000000000^789 ≤ 3150049581181^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046485957 5000000000 3150049581181 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33701741/62500000 : ℝ)^1045 ≤ (44130902158603/100000000000000 : ℝ)^789 := by
    have hnat : (33701741 : ℕ)^1045*100000000000000^789 ≤ 44130902158603^789*62500000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33701741 62500000 44130902158603 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312562623/10000000000 : ℝ), (-1046485957/5000000000 : ℝ), (33701741/62500000 : ℝ)] ![(21634449748733/50000000000000 : ℝ), (3150049581181/25000000000000 : ℝ), (44130902158603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312562623/10000000000 : ℝ)|^1045 ≤ (21634449748733/50000000000000 : ℝ)^789
        have hw : |(5312562623/10000000000 : ℝ)|=(5312562623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1046485957/5000000000 : ℝ)|^1045 ≤ (3150049581181/25000000000000 : ℝ)^789
        have hw : |(-1046485957/5000000000 : ℝ)|=(1046485957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33701741/62500000 : ℝ)|^1045 ≤ (44130902158603/100000000000000 : ℝ)^789
        have hw : |(33701741/62500000 : ℝ)|=(33701741/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s7_6 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656281343/5000000000 : ℝ)*x 0 + (337017399/625000000 : ℝ)*x 1 + (-2092972067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656281343/5000000000 : ℝ)^1045 ≤ (43268900177063/100000000000000 : ℝ)^789 := by
    have hnat : (2656281343 : ℕ)^1045*100000000000000^789 ≤ 43268900177063^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656281343 5000000000 43268900177063 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337017399/625000000 : ℝ)^1045 ≤ (1379090632839/3125000000000 : ℝ)^789 := by
    have hnat : (337017399 : ℕ)^1045*3125000000000^789 ≤ 1379090632839^789*625000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337017399 625000000 1379090632839 3125000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2092972067/10000000000 : ℝ)^1045 ≤ (6300099772341/50000000000000 : ℝ)^789 := by
    have hnat : (2092972067 : ℕ)^1045*50000000000000^789 ≤ 6300099772341^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092972067 10000000000 6300099772341 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656281343/5000000000 : ℝ), (337017399/625000000 : ℝ), (-2092972067/10000000000 : ℝ)] ![(43268900177063/100000000000000 : ℝ), (1379090632839/3125000000000 : ℝ), (6300099772341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656281343/5000000000 : ℝ)|^1045 ≤ (43268900177063/100000000000000 : ℝ)^789
        have hw : |(2656281343/5000000000 : ℝ)|=(2656281343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337017399/625000000 : ℝ)|^1045 ≤ (1379090632839/3125000000000 : ℝ)^789
        have hw : |(337017399/625000000 : ℝ)|=(337017399/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2092972067/10000000000 : ℝ)|^1045 ≤ (6300099772341/50000000000000 : ℝ)^789
        have hw : |(-2092972067/10000000000 : ℝ)|=(2092972067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s7_7 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4361171809/10000000000 : ℝ)*x 0 + (2244385597/5000000000 : ℝ)*x 1 + (4237181547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361171809/10000000000 : ℝ)^1045 ≤ (33317189955099/100000000000000 : ℝ)^789 := by
    have hnat : (4361171809 : ℕ)^1045*100000000000000^789 ≤ 33317189955099^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361171809 10000000000 33317189955099 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244385597/5000000000 : ℝ)^1045 ≤ (34614357900417/100000000000000 : ℝ)^789 := by
    have hnat : (2244385597 : ℕ)^1045*100000000000000^789 ≤ 34614357900417^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244385597 5000000000 34614357900417 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4237181547/10000000000 : ℝ)^1045 ≤ (32068452134607/100000000000000 : ℝ)^789 := by
    have hnat : (4237181547 : ℕ)^1045*100000000000000^789 ≤ 32068452134607^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237181547 10000000000 32068452134607 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361171809/10000000000 : ℝ), (2244385597/5000000000 : ℝ), (4237181547/10000000000 : ℝ)] ![(33317189955099/100000000000000 : ℝ), (34614357900417/100000000000000 : ℝ), (32068452134607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361171809/10000000000 : ℝ)|^1045 ≤ (33317189955099/100000000000000 : ℝ)^789
        have hw : |(4361171809/10000000000 : ℝ)|=(4361171809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244385597/5000000000 : ℝ)|^1045 ≤ (34614357900417/100000000000000 : ℝ)^789
        have hw : |(2244385597/5000000000 : ℝ)|=(2244385597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4237181547/10000000000 : ℝ)|^1045 ≤ (32068452134607/100000000000000 : ℝ)^789
        have hw : |(4237181547/10000000000 : ℝ)|=(4237181547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1167_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2277/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (879/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1407/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11379/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1407/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11379/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1407/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11379/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1407/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11379/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1407/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11379/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1407/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11379/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11379/100000 : ℝ) ^ (8359/2048 : ℝ) ≤ (1404262555544413/10000000000000000000 : ℝ) := by
    have hpowers : (11379/100000 : ℝ)^8359 ≤ (1404262555544413/10000000000000000000 : ℝ)^2048 := by
      have hnat : (11379 : ℕ)^8359*10000000000000000000^2048 ≤ 1404262555544413^2048*100000^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11379 100000 1404262555544413 10000000000000000000 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11379/100000 : ℝ)) (X := (1404262555544413/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1407/10000 : ℝ) ^ (8359/2048 : ℝ) ≤ (16699203851083931/50000000000000000000 : ℝ) := by
    have hpowers : (1407/10000 : ℝ)^8359 ≤ (16699203851083931/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1407 : ℕ)^8359*50000000000000000000^2048 ≤ 16699203851083931^2048*10000^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1407 10000 16699203851083931 50000000000000000000 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1407/10000 : ℝ)) (X := (16699203851083931/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001404262555544413/5000000000000000000 : ℝ) ≤ (10000688030830173/10000000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (5001404262555544413/5000000000000000000 : ℝ)^2048 ≤ (10000688030830173/10000000000000000 : ℝ)^8359 := by
      have hnat : (5001404262555544413 : ℕ)^2048*10000000000000000^8359 ≤ 10000688030830173^8359*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001404262555544413 5000000000000000000 10000688030830173 10000000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000688030830173/10000000000000000 : ℝ)) (X := (5001404262555544413/5000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505930129157201499/12500000000000000000 : ℝ) ≤ (10001162122751827/10000000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (12505930129157201499/12500000000000000000 : ℝ)^2048 ≤ (10001162122751827/10000000000000000 : ℝ)^8359 := by
      have hnat : (12505930129157201499 : ℕ)^2048*10000000000000000^8359 ≤ 10001162122751827^8359*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505930129157201499 12500000000000000000 10001162122751827 10000000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001162122751827/10000000000000000 : ℝ)) (X := (12505930129157201499/12500000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016699203851083931/25000000000000000000 : ℝ) ≤ (10001636214673481/10000000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (25016699203851083931/25000000000000000000 : ℝ)^2048 ≤ (10001636214673481/10000000000000000 : ℝ)^8359 := by
      have hnat : (25016699203851083931 : ℕ)^2048*10000000000000000^8359 ≤ 10001636214673481^8359*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016699203851083931 25000000000000000000 10001636214673481 10000000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001636214673481/10000000000000000 : ℝ)) (X := (25016699203851083931/25000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1404262555544413/10000000000000000000 : ℝ) ≤ ((689770823256692149/690000000000000000 : ℝ)+2*(18234304679/10350000000000 : ℝ)*(11379/100000 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (689770823256692149/690000000000000000 : ℝ)+2*(18234304679/10350000000000 : ℝ)*(11379/100000 : ℝ)=(10000688030830173/10000000000000000 : ℝ) by norm_num, show 1+2*(1404262555544413/10000000000000000000 : ℝ)=(5001404262555544413/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16699203851083931/50000000000000000000 : ℝ)+(1404262555544413/10000000000000000000 : ℝ) ≤ ((689770823256692149/690000000000000000 : ℝ)+(18234304679/10350000000000 : ℝ)*((1407/10000 : ℝ)+(11379/100000 : ℝ)))^(8359/2048 : ℝ) := by
    rw [show (689770823256692149/690000000000000000 : ℝ)+(18234304679/10350000000000 : ℝ)*((1407/10000 : ℝ)+(11379/100000 : ℝ))=(10001162122751827/10000000000000000 : ℝ) by norm_num, show 1+(16699203851083931/50000000000000000000 : ℝ)+(1404262555544413/10000000000000000000 : ℝ)=(12505930129157201499/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16699203851083931/50000000000000000000 : ℝ) ≤ ((689770823256692149/690000000000000000 : ℝ)+2*(18234304679/10350000000000 : ℝ)*(1407/10000 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (689770823256692149/690000000000000000 : ℝ)+2*(18234304679/10350000000000 : ℝ)*(1407/10000 : ℝ)=(10001636214673481/10000000000000000 : ℝ) by norm_num, show 1+2*(16699203851083931/50000000000000000000 : ℝ)=(25016699203851083931/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (689770823256692149/690000000000000000 : ℝ)*(X 1 0+X 2 0)+(18234304679/10350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (11379/100000 : ℝ)) (hi := (1407/10000 : ℝ)) (c := (689770823256692149/690000000000000000 : ℝ)) (alpha := (18234304679/10350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (689770823256692149/690000000000000000 : ℝ)*(X 0 1+X 2 1)+(18234304679/10350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (11379/100000 : ℝ)) (hi := (1407/10000 : ℝ)) (c := (689770823256692149/690000000000000000 : ℝ)) (alpha := (18234304679/10350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (689770823256692149/690000000000000000 : ℝ)*(X 0 2+X 1 2)+(18234304679/10350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (11379/100000 : ℝ)) (hi := (1407/10000 : ℝ)) (c := (689770823256692149/690000000000000000 : ℝ)) (alpha := (18234304679/10350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1077493091/5000000000 : ℝ)*X 0 0+(5392598147/10000000000 : ℝ)*X 0 1+(5266117733/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068933067/2000000000 : ℝ)*X 1 0+(-1109566631/5000000000 : ℝ)*X 1 1+(5266117733/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068933067/2000000000 : ℝ)*X 2 0+(5266117733/10000000000 : ℝ)*X 2 1+(-1109566631/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1090290541/2500000000 : ℝ)*X 0 0+(264783951/625000000 : ℝ)*X 0 1+(897881443/2000000000 : ℝ)*X 0 2+(1090290541/2500000000 : ℝ)*X 1 0+(264783951/625000000 : ℝ)*X 1 1+(897881443/2000000000 : ℝ)*X 1 2+(1090290541/2500000000 : ℝ)*X 2 0+(264783951/625000000 : ℝ)*X 2 1+(897881443/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2154991357/10000000000 : ℝ)*X 0 0+(131660889/250000000 : ℝ)*X 0 1+(5392278909/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312562623/10000000000 : ℝ)*X 1 0+(-1046485957/5000000000 : ℝ)*X 1 1+(33701741/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656281343/5000000000 : ℝ)*X 2 0+(337017399/625000000 : ℝ)*X 2 1+(-2092972067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4361171809/10000000000 : ℝ)*X 0 0+(2244385597/5000000000 : ℝ)*X 0 1+(4237181547/10000000000 : ℝ)*X 0 2+(4361171809/10000000000 : ℝ)*X 1 0+(2244385597/5000000000 : ℝ)*X 1 1+(4237181547/10000000000 : ℝ)*X 1 2+(4361171809/10000000000 : ℝ)*X 2 0+(2244385597/5000000000 : ℝ)*X 2 1+(4237181547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18496897573929040588590589/3450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (527948959/50000000000000 : ℝ)*(base19) + (39306929/4000000000000 : ℝ)*(base23) + (39136147/100000000000000 : ℝ)*(lower2) + (27133259/20000000000000 : ℝ)*(upper3) + (637493/781250000000 : ℝ)*(upper5) + (593057323185187/10000000000000 : ℝ)*(major0) + (593057323185187/10000000000000 : ℝ)*(major1) + (593057323185187/10000000000000 : ℝ)*(major2) + (3953196368782369/50000000000000 : ℝ)*(sp0) + (7906420548181673/100000000000000 : ℝ)*(sp1) + (3953210310703183/50000000000000 : ℝ)*(sp2) + (988677267026739/25000000000000 : ℝ)*(sp3) + (14433257427/50000000000000 : ℝ)*(sp4) + (15612803197/100000000000000 : ℝ)*(sp7) + (3954724680910153/100000000000000 : ℝ)*(f.failure) + (7906421604079591/100000000000000 : ℝ)*(f.sum) + (492665449/207000000000000000000000000 : ℝ)*base66 + (412575584785409411/20700000000000000000000000000000 : ℝ)*base68 + (227878594834709411/20700000000000000000000000000000 : ℝ)*base70 + (7656664154190589/20700000000000000000000000000000 : ℝ)*base71 + (64347798803/25875000000000000000000000 : ℝ)*base74 + (507622412063009411/20700000000000000000000000000000 : ℝ)*base76 + (165045860954309411/20700000000000000000000000000000 : ℝ)*base78 + (216983046488190589/20700000000000000000000000000000 : ℝ)*base79 + (805438753357/207000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (35581733/5000000000000000000000 : ℝ)*base89 + (35581733/5000000000000000000000 : ℝ)*base91 + (35581733/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (100751477565957980969/345000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1085866063/50000000000000 : ℝ)*(base19) + (2747980183/100000000000000 : ℝ)*(base23) + (137959309/50000000000000 : ℝ)*(upper2) + (3226501/50000000000000 : ℝ)*(upper3) + (5758053/2000000000000 : ℝ)*(upper5) + (1490138974509047/25000000000000 : ℝ)*(major0) + (1490138974509047/25000000000000 : ℝ)*(major1) + (1490138974509047/25000000000000 : ℝ)*(major2) + (28411811657/50000000000000 : ℝ)*(sp1) + (50641849131/100000000000000 : ℝ)*(sp2) + (1589278711843697/20000000000000 : ℝ)*(sp4) + (3973167281931523/50000000000000 : ℝ)*(sp5) + (7946340169389171/100000000000000 : ℝ)*(sp6) + (993679556779861/25000000000000 : ℝ)*(sp7) + (993679556779861/25000000000000 : ℝ)*(f.failure) + (1589278711843697/20000000000000 : ℝ)*(f.sum) + (8925362805481/1035000000000000000000000000 : ℝ)*base66 + (30558853077716009/51750000000000000000000000000000 : ℝ)*base67 + (132904310732966009/51750000000000000000000000000000 : ℝ)*base69 + (117181254611283991/51750000000000000000000000000000 : ℝ)*base72 + (617449266317/129375000000000000000000000 : ℝ)*base74 + (44862653783216009/51750000000000000000000000000000 : ℝ)*base75 + (112963492111533991/51750000000000000000000000000000 : ℝ)*base78 + (6876739174533991/51750000000000000000000000000000 : ℝ)*base80 + (3143153225189/1035000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (15240321/1250000000000000000000 : ℝ)*base89 + (15240321/1250000000000000000000 : ℝ)*base91 + (15240321/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1167_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (879/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1167_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1167_s8_0 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2154990427/10000000000 : ℝ)*x 0 + (269626959/500000000 : ℝ)*x 1 + (5266173979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154990427/10000000000 : ℝ)^1045 ≤ (3274267332513/25000000000000 : ℝ)^789 := by
    have hnat : (2154990427 : ℕ)^1045*25000000000000^789 ≤ 3274267332513^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154990427 10000000000 3274267332513 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269626959/500000000 : ℝ)^1045 ≤ (44133727174651/100000000000000 : ℝ)^789 := by
    have hnat : (269626959 : ℕ)^1045*100000000000000^789 ≤ 44133727174651^789*500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269626959 500000000 44133727174651 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266173979/10000000000 : ℝ)^1045 ≤ (21384601740163/50000000000000 : ℝ)^789 := by
    have hnat : (5266173979 : ℕ)^1045*50000000000000^789 ≤ 21384601740163^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266173979 10000000000 21384601740163 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2154990427/10000000000 : ℝ), (269626959/500000000 : ℝ), (5266173979/10000000000 : ℝ)] ![(3274267332513/25000000000000 : ℝ), (44133727174651/100000000000000 : ℝ), (21384601740163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2154990427/10000000000 : ℝ)|^1045 ≤ (3274267332513/25000000000000 : ℝ)^789
        have hw : |(-2154990427/10000000000 : ℝ)|=(2154990427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269626959/500000000 : ℝ)|^1045 ≤ (44133727174651/100000000000000 : ℝ)^789
        have hw : |(269626959/500000000 : ℝ)|=(269626959/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266173979/10000000000 : ℝ)|^1045 ≤ (21384601740163/50000000000000 : ℝ)^789
        have hw : |(5266173979/10000000000 : ℝ)|=(5266173979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s8_1 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344650747/10000000000 : ℝ)*x 0 + (-110953913/500000000 : ℝ)*x 1 + (1053234789/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344650747/10000000000 : ℝ)^1045 ≤ (10903845273763/25000000000000 : ℝ)^789 := by
    have hnat : (5344650747 : ℕ)^1045*25000000000000^789 ≤ 10903845273763^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344650747 10000000000 10903845273763 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110953913/500000000 : ℝ)^1045 ≤ (13615415782151/100000000000000 : ℝ)^789 := by
    have hnat : (110953913 : ℕ)^1045*100000000000000^789 ≤ 13615415782151^789*500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110953913 500000000 13615415782151 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053234789/2000000000 : ℝ)^1045 ≤ (42769203114601/100000000000000 : ℝ)^789 := by
    have hnat : (1053234789 : ℕ)^1045*100000000000000^789 ≤ 42769203114601^789*2000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053234789 2000000000 42769203114601 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344650747/10000000000 : ℝ), (-110953913/500000000 : ℝ), (1053234789/2000000000 : ℝ)] ![(10903845273763/25000000000000 : ℝ), (13615415782151/100000000000000 : ℝ), (42769203114601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344650747/10000000000 : ℝ)|^1045 ≤ (10903845273763/25000000000000 : ℝ)^789
        have hw : |(5344650747/10000000000 : ℝ)|=(5344650747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-110953913/500000000 : ℝ)|^1045 ≤ (13615415782151/100000000000000 : ℝ)^789
        have hw : |(-110953913/500000000 : ℝ)|=(110953913/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053234789/2000000000 : ℝ)|^1045 ≤ (42769203114601/100000000000000 : ℝ)^789
        have hw : |(1053234789/2000000000 : ℝ)|=(1053234789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s8_2 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (534465077/1000000000 : ℝ)*x 0 + (5266173931/10000000000 : ℝ)*x 1 + (-277384781/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534465077/1000000000 : ℝ)^1045 ≤ (10903845335911/25000000000000 : ℝ)^789 := by
    have hnat : (534465077 : ℕ)^1045*25000000000000^789 ≤ 10903845335911^789*1000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534465077 1000000000 10903845335911 25000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266173931/10000000000 : ℝ)^1045 ≤ (42769202964009/100000000000000 : ℝ)^789 := by
    have hnat : (5266173931 : ℕ)^1045*100000000000000^789 ≤ 42769202964009^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266173931 10000000000 42769202964009 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277384781/1250000000 : ℝ)^1045 ≤ (6807707842317/50000000000000 : ℝ)^789 := by
    have hnat : (277384781 : ℕ)^1045*50000000000000^789 ≤ 6807707842317^789*1250000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277384781 1250000000 6807707842317 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534465077/1000000000 : ℝ), (5266173931/10000000000 : ℝ), (-277384781/1250000000 : ℝ)] ![(10903845335911/25000000000000 : ℝ), (42769202964009/100000000000000 : ℝ), (6807707842317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534465077/1000000000 : ℝ)|^1045 ≤ (10903845335911/25000000000000 : ℝ)^789
        have hw : |(534465077/1000000000 : ℝ)|=(534465077/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266173931/10000000000 : ℝ)|^1045 ≤ (42769202964009/100000000000000 : ℝ)^789
        have hw : |(5266173931/10000000000 : ℝ)|=(5266173931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-277384781/1250000000 : ℝ)|^1045 ≤ (6807707842317/50000000000000 : ℝ)^789
        have hw : |(-277384781/1250000000 : ℝ)|=(277384781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s8_3 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4361165067/10000000000 : ℝ)*x 0 + (2118328981/5000000000 : ℝ)*x 1 + (4489291731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361165067/10000000000 : ℝ)^1045 ≤ (33317121738023/100000000000000 : ℝ)^789 := by
    have hnat : (4361165067 : ℕ)^1045*100000000000000^789 ≤ 33317121738023^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361165067 10000000000 33317121738023 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2118328981/5000000000 : ℝ)^1045 ≤ (16031601916997/50000000000000 : ℝ)^789 := by
    have hnat : (2118328981 : ℕ)^1045*50000000000000^789 ≤ 16031601916997^789*5000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118328981 5000000000 16031601916997 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489291731/10000000000 : ℝ)^1045 ≤ (17309837212787/50000000000000 : ℝ)^789 := by
    have hnat : (4489291731 : ℕ)^1045*50000000000000^789 ≤ 17309837212787^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489291731 10000000000 17309837212787 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361165067/10000000000 : ℝ), (2118328981/5000000000 : ℝ), (4489291731/10000000000 : ℝ)] ![(33317121738023/100000000000000 : ℝ), (16031601916997/50000000000000 : ℝ), (17309837212787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361165067/10000000000 : ℝ)|^1045 ≤ (33317121738023/100000000000000 : ℝ)^789
        have hw : |(4361165067/10000000000 : ℝ)|=(4361165067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2118328981/5000000000 : ℝ)|^1045 ≤ (16031601916997/50000000000000 : ℝ)^789
        have hw : |(2118328981/5000000000 : ℝ)|=(2118328981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489291731/10000000000 : ℝ)|^1045 ≤ (17309837212787/50000000000000 : ℝ)^789
        have hw : |(4489291731/10000000000 : ℝ)|=(4489291731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s8_4 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2154995301/10000000000 : ℝ)*x 0 + (658311457/1250000000 : ℝ)*x 1 + (5392220313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154995301/10000000000 : ℝ)^1045 ≤ (6548554281627/50000000000000 : ℝ)^789 := by
    have hnat : (2154995301 : ℕ)^1045*50000000000000^789 ≤ 6548554281627^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154995301 10000000000 6548554281627 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658311457/1250000000 : ℝ)^1045 ≤ (1710904825599/4000000000000 : ℝ)^789 := by
    have hnat : (658311457 : ℕ)^1045*4000000000000^789 ≤ 1710904825599^789*1250000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658311457 1250000000 1710904825599 4000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392220313/10000000000 : ℝ)^1045 ≤ (44130270790591/100000000000000 : ℝ)^789 := by
    have hnat : (5392220313 : ℕ)^1045*100000000000000^789 ≤ 44130270790591^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392220313 10000000000 44130270790591 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2154995301/10000000000 : ℝ), (658311457/1250000000 : ℝ), (5392220313/10000000000 : ℝ)] ![(6548554281627/50000000000000 : ℝ), (1710904825599/4000000000000 : ℝ), (44130270790591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2154995301/10000000000 : ℝ)|^1045 ≤ (6548554281627/50000000000000 : ℝ)^789
        have hw : |(-2154995301/10000000000 : ℝ)|=(2154995301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658311457/1250000000 : ℝ)|^1045 ≤ (1710904825599/4000000000000 : ℝ)^789
        have hw : |(658311457/1250000000 : ℝ)|=(658311457/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392220313/10000000000 : ℝ)|^1045 ≤ (44130270790591/100000000000000 : ℝ)^789
        have hw : |(5392220313/10000000000 : ℝ)|=(5392220313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s8_5 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1328144173/2500000000 : ℝ)*x 0 + (-523257921/2500000000 : ℝ)*x 1 + (337013787/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328144173/2500000000 : ℝ)^1045 ≤ (43269051263467/100000000000000 : ℝ)^789 := by
    have hnat : (1328144173 : ℕ)^1045*100000000000000^789 ≤ 43269051263467^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328144173 2500000000 43269051263467 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523257921/2500000000 : ℝ)^1045 ≤ (196885545433/1562500000000 : ℝ)^789 := by
    have hnat : (523257921 : ℕ)^1045*1562500000000^789 ≤ 196885545433^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523257921 2500000000 196885545433 1562500000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337013787/625000000 : ℝ)^1045 ≤ (8826054762961/20000000000000 : ℝ)^789 := by
    have hnat : (337013787 : ℕ)^1045*20000000000000^789 ≤ 8826054762961^789*625000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337013787 625000000 8826054762961 20000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328144173/2500000000 : ℝ), (-523257921/2500000000 : ℝ), (337013787/625000000 : ℝ)] ![(43269051263467/100000000000000 : ℝ), (196885545433/1562500000000 : ℝ), (8826054762961/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328144173/2500000000 : ℝ)|^1045 ≤ (43269051263467/100000000000000 : ℝ)^789
        have hw : |(1328144173/2500000000 : ℝ)|=(1328144173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-523257921/2500000000 : ℝ)|^1045 ≤ (196885545433/1562500000000 : ℝ)^789
        have hw : |(-523257921/2500000000 : ℝ)|=(523257921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337013787/625000000 : ℝ)|^1045 ≤ (8826054762961/20000000000000 : ℝ)^789
        have hw : |(337013787/625000000 : ℝ)|=(337013787/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s8_6 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (132814421/250000000 : ℝ)*x 0 + (5392220397/10000000000 : ℝ)*x 1 + (-2093031749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132814421/250000000 : ℝ)^1045 ≤ (43269052859983/100000000000000 : ℝ)^789 := by
    have hnat : (132814421 : ℕ)^1045*100000000000000^789 ≤ 43269052859983^789*250000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132814421 250000000 43269052859983 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392220397/10000000000 : ℝ)^1045 ≤ (44130271701107/100000000000000 : ℝ)^789 := by
    have hnat : (5392220397 : ℕ)^1045*100000000000000^789 ≤ 44130271701107^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392220397 10000000000 44130271701107 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2093031749/10000000000 : ℝ)^1045 ≤ (12600675425999/100000000000000 : ℝ)^789 := by
    have hnat : (2093031749 : ℕ)^1045*100000000000000^789 ≤ 12600675425999^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093031749 10000000000 12600675425999 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132814421/250000000 : ℝ), (5392220397/10000000000 : ℝ), (-2093031749/10000000000 : ℝ)] ![(43269052859983/100000000000000 : ℝ), (44130271701107/100000000000000 : ℝ), (12600675425999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132814421/250000000 : ℝ)|^1045 ≤ (43269052859983/100000000000000 : ℝ)^789
        have hw : |(132814421/250000000 : ℝ)|=(132814421/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392220397/10000000000 : ℝ)|^1045 ≤ (44130271701107/100000000000000 : ℝ)^789
        have hw : |(5392220397/10000000000 : ℝ)|=(5392220397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2093031749/10000000000 : ℝ)|^1045 ≤ (12600675425999/100000000000000 : ℝ)^789
        have hw : |(-2093031749/10000000000 : ℝ)|=(2093031749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1167_s8_7 (p : ℝ) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ)) (x : Fin 3 → ℝ) :
    (872234931/2000000000 : ℝ)*x 0 + (1122164217/2500000000 : ℝ)*x 1 + (4237295159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872234931/2000000000 : ℝ)^1045 ≤ (16658609375789/50000000000000 : ℝ)^789 := by
    have hnat : (872234931 : ℕ)^1045*50000000000000^789 ≤ 16658609375789^789*2000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872234931 2000000000 16658609375789 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122164217/2500000000 : ℝ)^1045 ≤ (34613190254103/100000000000000 : ℝ)^789 := by
    have hnat : (1122164217 : ℕ)^1045*100000000000000^789 ≤ 34613190254103^789*2500000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122164217 2500000000 34613190254103 100000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4237295159/10000000000 : ℝ)^1045 ≤ (16034795492017/50000000000000 : ℝ)^789 := by
    have hnat : (4237295159 : ℕ)^1045*50000000000000^789 ≤ 16034795492017^789*10000000000^1045 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237295159 10000000000 16034795492017 50000000000000 1045 789 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1045/256 : ℝ)) 1045 789 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872234931/2000000000 : ℝ), (1122164217/2500000000 : ℝ), (4237295159/10000000000 : ℝ)] ![(16658609375789/50000000000000 : ℝ), (34613190254103/100000000000000 : ℝ), (16034795492017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872234931/2000000000 : ℝ)|^1045 ≤ (16658609375789/50000000000000 : ℝ)^789
        have hw : |(872234931/2000000000 : ℝ)|=(872234931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122164217/2500000000 : ℝ)|^1045 ≤ (34613190254103/100000000000000 : ℝ)^789
        have hw : |(1122164217/2500000000 : ℝ)|=(1122164217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4237295159/10000000000 : ℝ)|^1045 ≤ (16034795492017/50000000000000 : ℝ)^789
        have hw : |(4237295159/10000000000 : ℝ)|=(4237295159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1167_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (879/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5693/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14063/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (879/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2277/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (879/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2277/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (879/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2277/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (879/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2277/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (879/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2277/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (879/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2277/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2277/20000 : ℝ) ^ (8359/2048 : ℝ) ≤ (14072871883665947/100000000000000000000 : ℝ) := by
    have hpowers : (2277/20000 : ℝ)^8359 ≤ (14072871883665947/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2277 : ℕ)^8359*100000000000000000000^2048 ≤ 14072871883665947^2048*20000^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2277 20000 14072871883665947 100000000000000000000 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2277/20000 : ℝ)) (X := (14072871883665947/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (879/6250 : ℝ) ^ (8359/2048 : ℝ) ≤ (6668062990656201/20000000000000000000 : ℝ) := by
    have hpowers : (879/6250 : ℝ)^8359 ≤ (6668062990656201/20000000000000000000 : ℝ)^2048 := by
      have hnat : (879 : ℕ)^8359*20000000000000000000^2048 ≤ 6668062990656201^2048*6250^8359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        879 6250 6668062990656201 20000000000000000000 8359 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (879/6250 : ℝ)) (X := (6668062990656201/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014072871883665947/50000000000000000000 : ℝ) ≤ (2500172378154573/2500000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (50014072871883665947/50000000000000000000 : ℝ)^2048 ≤ (2500172378154573/2500000000000000 : ℝ)^8359 := by
      have hnat : (50014072871883665947 : ℕ)^2048*2500000000000000^8359 ≤ 2500172378154573^8359*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014072871883665947 50000000000000000000 2500172378154573 2500000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500172378154573/2500000000000000 : ℝ)) (X := (50014072871883665947/50000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505926648354618369/12500000000000000000 : ℝ) ≤ (2500290360185931/2500000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (12505926648354618369/12500000000000000000 : ℝ)^2048 ≤ (2500290360185931/2500000000000000 : ℝ)^8359 := by
      have hnat : (12505926648354618369 : ℕ)^2048*2500000000000000^8359 ≤ 2500290360185931^8359*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505926648354618369 12500000000000000000 2500290360185931 2500000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500290360185931/2500000000000000 : ℝ)) (X := (12505926648354618369/12500000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006668062990656201/10000000000000000000 : ℝ) ≤ (2500408342217289/2500000000000000 : ℝ) ^ (8359/2048 : ℝ) := by
    have hpowers : (10006668062990656201/10000000000000000000 : ℝ)^2048 ≤ (2500408342217289/2500000000000000 : ℝ)^8359 := by
      have hnat : (10006668062990656201 : ℕ)^2048*2500000000000000^8359 ≤ 2500408342217289^8359*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006668062990656201 10000000000000000000 2500408342217289 2500000000000000 2048 8359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500408342217289/2500000000000000 : ℝ)) (X := (10006668062990656201/10000000000000000000 : ℝ)) (by norm_num) 8359 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14072871883665947/100000000000000000000 : ℝ) ≤ ((2231758450074026469/2232500000000000000 : ℝ)+2*(19663671893/11162500000000 : ℝ)*(2277/20000 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (2231758450074026469/2232500000000000000 : ℝ)+2*(19663671893/11162500000000 : ℝ)*(2277/20000 : ℝ)=(2500172378154573/2500000000000000 : ℝ) by norm_num, show 1+2*(14072871883665947/100000000000000000000 : ℝ)=(50014072871883665947/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6668062990656201/20000000000000000000 : ℝ)+(14072871883665947/100000000000000000000 : ℝ) ≤ ((2231758450074026469/2232500000000000000 : ℝ)+(19663671893/11162500000000 : ℝ)*((879/6250 : ℝ)+(2277/20000 : ℝ)))^(8359/2048 : ℝ) := by
    rw [show (2231758450074026469/2232500000000000000 : ℝ)+(19663671893/11162500000000 : ℝ)*((879/6250 : ℝ)+(2277/20000 : ℝ))=(2500290360185931/2500000000000000 : ℝ) by norm_num, show 1+(6668062990656201/20000000000000000000 : ℝ)+(14072871883665947/100000000000000000000 : ℝ)=(12505926648354618369/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6668062990656201/20000000000000000000 : ℝ) ≤ ((2231758450074026469/2232500000000000000 : ℝ)+2*(19663671893/11162500000000 : ℝ)*(879/6250 : ℝ))^(8359/2048 : ℝ) := by
    rw [show (2231758450074026469/2232500000000000000 : ℝ)+2*(19663671893/11162500000000 : ℝ)*(879/6250 : ℝ)=(2500408342217289/2500000000000000 : ℝ) by norm_num, show 1+2*(6668062990656201/20000000000000000000 : ℝ)=(10006668062990656201/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2231758450074026469/2232500000000000000 : ℝ)*(X 1 0+X 2 0)+(19663671893/11162500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (2277/20000 : ℝ)) (hi := (879/6250 : ℝ)) (c := (2231758450074026469/2232500000000000000 : ℝ)) (alpha := (19663671893/11162500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2231758450074026469/2232500000000000000 : ℝ)*(X 0 1+X 2 1)+(19663671893/11162500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (2277/20000 : ℝ)) (hi := (879/6250 : ℝ)) (c := (2231758450074026469/2232500000000000000 : ℝ)) (alpha := (19663671893/11162500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2231758450074026469/2232500000000000000 : ℝ)*(X 0 2+X 1 2)+(19663671893/11162500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8359/2048 : ℝ)) (lo := (2277/20000 : ℝ)) (hi := (879/6250 : ℝ)) (c := (2231758450074026469/2232500000000000000 : ℝ)) (alpha := (19663671893/11162500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2154990427/10000000000 : ℝ)*X 0 0+(269626959/500000000 : ℝ)*X 0 1+(5266173979/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344650747/10000000000 : ℝ)*X 1 0+(-110953913/500000000 : ℝ)*X 1 1+(1053234789/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534465077/1000000000 : ℝ)*X 2 0+(5266173931/10000000000 : ℝ)*X 2 1+(-277384781/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361165067/10000000000 : ℝ)*X 0 0+(2118328981/5000000000 : ℝ)*X 0 1+(4489291731/10000000000 : ℝ)*X 0 2+(4361165067/10000000000 : ℝ)*X 1 0+(2118328981/5000000000 : ℝ)*X 1 1+(4489291731/10000000000 : ℝ)*X 1 2+(4361165067/10000000000 : ℝ)*X 2 0+(2118328981/5000000000 : ℝ)*X 2 1+(4489291731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2154995301/10000000000 : ℝ)*X 0 0+(658311457/1250000000 : ℝ)*X 0 1+(5392220313/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328144173/2500000000 : ℝ)*X 1 0+(-523257921/2500000000 : ℝ)*X 1 1+(337013787/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132814421/250000000 : ℝ)*X 2 0+(5392220397/10000000000 : ℝ)*X 2 1+(-2093031749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872234931/2000000000 : ℝ)*X 0 0+(1122164217/2500000000 : ℝ)*X 0 1+(4237295159/10000000000 : ℝ)*X 0 2+(872234931/2000000000 : ℝ)*X 1 0+(1122164217/2500000000 : ℝ)*X 1 1+(4237295159/10000000000 : ℝ)*X 1 2+(872234931/2000000000 : ℝ)*X 2 0+(1122164217/2500000000 : ℝ)*X 2 1+(4237295159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1167_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (389794766859083854657828443/55812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (726439793/50000000000000 : ℝ)*(base19) + (1408621021/100000000000000 : ℝ)*(base23) + (837121/2000000000000 : ℝ)*(lower2) + (15492999/10000000000000 : ℝ)*(upper3) + (24564947/20000000000000 : ℝ)*(upper5) + (5935996131162549/100000000000000 : ℝ)*(major0) + (5935996131162549/100000000000000 : ℝ)*(major1) + (5935996131162549/100000000000000 : ℝ)*(major2) + (7913611021069289/100000000000000 : ℝ)*(sp0) + (7913649706724851/100000000000000 : ℝ)*(sp1) + (989206218872927/12500000000000 : ℝ)*(sp2) + (1979159630539999/50000000000000 : ℝ)*(sp3) + (10034633787/25000000000000 : ℝ)*(sp4) + (21608840493/100000000000000 : ℝ)*(sp7) + (989585217480123/25000000000000 : ℝ)*(f.failure) + (7913651159604437/100000000000000 : ℝ)*(f.sum) + (460627496947/2232500000000000000000000000 : ℝ)*base66 + (1326185798692090519/223250000000000000000000000000000 : ℝ)*base68 + (3324115700266090519/223250000000000000000000000000000 : ℝ)*base70 + (592224716294590519/223250000000000000000000000000000 : ℝ)*base72 + (334640605511/1116250000000000000000000000 : ℝ)*base74 + (1543097510621090519/223250000000000000000000000000000 : ℝ)*base76 + (4334121677379340519/223250000000000000000000000000000 : ℝ)*base78 + (3245849139336909481/223250000000000000000000000000000 : ℝ)*base79 + (58144730092051/4465000000000000000000000000 : ℝ)*base81 + (10425903/1250000000000000000000 : ℝ)*base89 + (10425903/1250000000000000000000 : ℝ)*base91 + (10425903/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (838300210472558315891754453/111625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1404363439/100000000000000 : ℝ)*(base19) + (1701370759/100000000000000 : ℝ)*(base23) + (118273967/20000000000000 : ℝ)*(lower1) + (2072167/12500000000000 : ℝ)*(upper2) + (277634737/100000000000000 : ℝ)*(upper3) + (25484827/50000000000000 : ℝ)*(upper5) + (5965946559593007/100000000000000 : ℝ)*(major0) + (5965946559593007/100000000000000 : ℝ)*(major1) + (5965946559593007/100000000000000 : ℝ)*(major2) + (7325925583/100000000000000 : ℝ)*(sp2) + (3976789975022839/50000000000000 : ℝ)*(sp4) + (3976789272841119/50000000000000 : ℝ)*(sp5) + (994196365343667/12500000000000 : ℝ)*(sp6) + (795662583761609/20000000000000 : ℝ)*(sp7) + (795662583761609/20000000000000 : ℝ)*(f.failure) + (3976789975022839/50000000000000 : ℝ)*(f.sum) + (11190146145403/4465000000000000000000000000 : ℝ)*base65 + (627286997734502283/223250000000000000000000000000000 : ℝ)*base67 + (7362506080706252283/223250000000000000000000000000000 : ℝ)*base69 + (2291117823659752283/223250000000000000000000000000000 : ℝ)*base71 + (1884165397153/1116250000000000000000000000 : ℝ)*base74 + (3736303730699752283/223250000000000000000000000000000 : ℝ)*base75 + (1204910474804252283/223250000000000000000000000000000 : ℝ)*base77 + (1401491119104252283/223250000000000000000000000000000 : ℝ)*base79 + (69363173278253/4465000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8434651/1000000000000000000000 : ℝ)*base90 + (8434651/1000000000000000000000 : ℝ)*base92 + (8434651/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1167_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (879/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1167_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1167_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1167_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1167_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1167_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8359/2048 : ℝ) ≤ p) (hpb : p ≤ (1045/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74980861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1167_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

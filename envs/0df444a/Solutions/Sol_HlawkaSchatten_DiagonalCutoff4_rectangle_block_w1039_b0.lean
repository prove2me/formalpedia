-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1039_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:45:04.179999+00:00
-- url     : https://prove2.me/submissions/8a14b94c-00d4-4afe-9718-8dc87854753d

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
theorem support_rectangle_w1039_s0_0 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5483197569/10000000000 : ℝ)*x 0 + (-1347988311/5000000000 : ℝ)*x 1 + (2397835097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5483197569/10000000000 : ℝ)^1029 ≤ (22468695908497/50000000000000 : ℝ)^773 := by
    have hnat : (5483197569 : ℕ)^1029*50000000000000^773 ≤ 22468695908497^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483197569 10000000000 22468695908497 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347988311/5000000000 : ℝ)^1029 ≤ (17465549872811/100000000000000 : ℝ)^773 := by
    have hnat : (1347988311 : ℕ)^1029*100000000000000^773 ≤ 17465549872811^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347988311 5000000000 17465549872811 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2397835097/5000000000 : ℝ)^1029 ≤ (7519411659413/20000000000000 : ℝ)^773 := by
    have hnat : (2397835097 : ℕ)^1029*20000000000000^773 ≤ 7519411659413^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397835097 5000000000 7519411659413 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5483197569/10000000000 : ℝ), (-1347988311/5000000000 : ℝ), (2397835097/5000000000 : ℝ)] ![(22468695908497/50000000000000 : ℝ), (17465549872811/100000000000000 : ℝ), (7519411659413/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5483197569/10000000000 : ℝ)|^1029 ≤ (22468695908497/50000000000000 : ℝ)^773
        have hw : |(5483197569/10000000000 : ℝ)|=(5483197569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1347988311/5000000000 : ℝ)|^1029 ≤ (17465549872811/100000000000000 : ℝ)^773
        have hw : |(-1347988311/5000000000 : ℝ)|=(1347988311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2397835097/5000000000 : ℝ)|^1029 ≤ (7519411659413/20000000000000 : ℝ)^773
        have hw : |(2397835097/5000000000 : ℝ)|=(2397835097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s0_1 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5486820813/10000000000 : ℝ)*x 0 + (957006527/2000000000 : ℝ)*x 1 + (-1352128307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5486820813/10000000000 : ℝ)^1029 ≤ (1405528886787/3125000000000 : ℝ)^773 := by
    have hnat : (5486820813 : ℕ)^1029*3125000000000^773 ≤ 1405528886787^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486820813 10000000000 1405528886787 3125000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (957006527/2000000000 : ℝ)^1029 ≤ (9371520974963/25000000000000 : ℝ)^773 := by
    have hnat : (957006527 : ℕ)^1029*25000000000000^773 ≤ 9371520974963^773*2000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957006527 2000000000 9371520974963 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352128307/5000000000 : ℝ)^1029 ≤ (1753699170733/10000000000000 : ℝ)^773 := by
    have hnat : (1352128307 : ℕ)^1029*10000000000000^773 ≤ 1753699170733^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352128307 5000000000 1753699170733 10000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5486820813/10000000000 : ℝ), (957006527/2000000000 : ℝ), (-1352128307/5000000000 : ℝ)] ![(1405528886787/3125000000000 : ℝ), (9371520974963/25000000000000 : ℝ), (1753699170733/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5486820813/10000000000 : ℝ)|^1029 ≤ (1405528886787/3125000000000 : ℝ)^773
        have hw : |(5486820813/10000000000 : ℝ)|=(5486820813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(957006527/2000000000 : ℝ)|^1029 ≤ (9371520974963/25000000000000 : ℝ)^773
        have hw : |(957006527/2000000000 : ℝ)|=(957006527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1352128307/5000000000 : ℝ)|^1029 ≤ (1753699170733/10000000000000 : ℝ)^773
        have hw : |(-1352128307/5000000000 : ℝ)|=(1352128307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s0_2 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1930300543/10000000000 : ℝ)*x 0 + (2400587177/5000000000 : ℝ)*x 1 + (377712217/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1930300543/10000000000 : ℝ)^1029 ≤ (11195414454507/100000000000000 : ℝ)^773 := by
    have hnat : (1930300543 : ℕ)^1029*100000000000000^773 ≤ 11195414454507^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930300543 10000000000 11195414454507 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2400587177/5000000000 : ℝ)^1029 ≤ (3765451146729/10000000000000 : ℝ)^773 := by
    have hnat : (2400587177 : ℕ)^1029*10000000000000^773 ≤ 3765451146729^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2400587177 5000000000 3765451146729 10000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (377712217/625000000 : ℝ)^1029 ≤ (3196879628703/6250000000000 : ℝ)^773 := by
    have hnat : (377712217 : ℕ)^1029*6250000000000^773 ≤ 3196879628703^773*625000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377712217 625000000 3196879628703 6250000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1930300543/10000000000 : ℝ), (2400587177/5000000000 : ℝ), (377712217/625000000 : ℝ)] ![(11195414454507/100000000000000 : ℝ), (3765451146729/10000000000000 : ℝ), (3196879628703/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1930300543/10000000000 : ℝ)|^1029 ≤ (11195414454507/100000000000000 : ℝ)^773
        have hw : |(-1930300543/10000000000 : ℝ)|=(1930300543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2400587177/5000000000 : ℝ)|^1029 ≤ (3765451146729/10000000000000 : ℝ)^773
        have hw : |(2400587177/5000000000 : ℝ)|=(2400587177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(377712217/625000000 : ℝ)|^1029 ≤ (3196879628703/6250000000000 : ℝ)^773
        have hw : |(377712217/625000000 : ℝ)|=(377712217/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s0_3 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5166884087/10000000000 : ℝ)*x 0 + (-1404265199/10000000000 : ℝ)*x 1 + (1208679127/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5166884087/10000000000 : ℝ)^1029 ≤ (41519928767403/100000000000000 : ℝ)^773 := by
    have hnat : (5166884087 : ℕ)^1029*100000000000000^773 ≤ 41519928767403^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5166884087 10000000000 41519928767403 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1404265199/10000000000 : ℝ)^1029 ≤ (1465999063759/20000000000000 : ℝ)^773 := by
    have hnat : (1404265199 : ℕ)^1029*20000000000000^773 ≤ 1465999063759^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404265199 10000000000 1465999063759 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1208679127/2000000000 : ℝ)^1029 ≤ (51150075895739/100000000000000 : ℝ)^773 := by
    have hnat : (1208679127 : ℕ)^1029*100000000000000^773 ≤ 51150075895739^773*2000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208679127 2000000000 51150075895739 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5166884087/10000000000 : ℝ), (-1404265199/10000000000 : ℝ), (1208679127/2000000000 : ℝ)] ![(41519928767403/100000000000000 : ℝ), (1465999063759/20000000000000 : ℝ), (51150075895739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5166884087/10000000000 : ℝ)|^1029 ≤ (41519928767403/100000000000000 : ℝ)^773
        have hw : |(5166884087/10000000000 : ℝ)|=(5166884087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1404265199/10000000000 : ℝ)|^1029 ≤ (1465999063759/20000000000000 : ℝ)^773
        have hw : |(-1404265199/10000000000 : ℝ)|=(1404265199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1208679127/2000000000 : ℝ)|^1029 ≤ (51150075895739/100000000000000 : ℝ)^773
        have hw : |(1208679127/2000000000 : ℝ)|=(1208679127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s0_4 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5166878971/10000000000 : ℝ)*x 0 + (3021700233/5000000000 : ℝ)*x 1 + (-702132621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5166878971/10000000000 : ℝ)^1029 ≤ (41519874041337/100000000000000 : ℝ)^773 := by
    have hnat : (5166878971 : ℕ)^1029*100000000000000^773 ≤ 41519874041337^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5166878971 10000000000 41519874041337 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3021700233/5000000000 : ℝ)^1029 ≤ (25575065162863/50000000000000 : ℝ)^773 := by
    have hnat : (3021700233 : ℕ)^1029*50000000000000^773 ≤ 25575065162863^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3021700233 5000000000 25575065162863 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (702132621/5000000000 : ℝ)^1029 ≤ (366499780879/5000000000000 : ℝ)^773 := by
    have hnat : (702132621 : ℕ)^1029*5000000000000^773 ≤ 366499780879^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702132621 5000000000 366499780879 5000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5166878971/10000000000 : ℝ), (3021700233/5000000000 : ℝ), (-702132621/5000000000 : ℝ)] ![(41519874041337/100000000000000 : ℝ), (25575065162863/50000000000000 : ℝ), (366499780879/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5166878971/10000000000 : ℝ)|^1029 ≤ (41519874041337/100000000000000 : ℝ)^773
        have hw : |(5166878971/10000000000 : ℝ)|=(5166878971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3021700233/5000000000 : ℝ)|^1029 ≤ (25575065162863/50000000000000 : ℝ)^773
        have hw : |(3021700233/5000000000 : ℝ)|=(3021700233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-702132621/5000000000 : ℝ)|^1029 ≤ (366499780879/5000000000000 : ℝ)^773
        have hw : |(-702132621/5000000000 : ℝ)|=(702132621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s0_5 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (52751053/125000000 : ℝ)*x 0 + (5616207033/10000000000 : ℝ)*x 1 + (798665567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52751053/125000000 : ℝ)^1029 ≤ (6342580702489/20000000000000 : ℝ)^773 := by
    have hnat : (52751053 : ℕ)^1029*20000000000000^773 ≤ 6342580702489^773*125000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52751053 125000000 6342580702489 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5616207033/10000000000 : ℝ)^1029 ≤ (11598568191903/25000000000000 : ℝ)^773 := by
    have hnat : (5616207033 : ℕ)^1029*25000000000000^773 ≤ 11598568191903^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5616207033 10000000000 11598568191903 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (798665567/2500000000 : ℝ)^1029 ≤ (5473205928551/25000000000000 : ℝ)^773 := by
    have hnat : (798665567 : ℕ)^1029*25000000000000^773 ≤ 5473205928551^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      798665567 2500000000 5473205928551 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52751053/125000000 : ℝ), (5616207033/10000000000 : ℝ), (798665567/2500000000 : ℝ)] ![(6342580702489/20000000000000 : ℝ), (11598568191903/25000000000000 : ℝ), (5473205928551/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52751053/125000000 : ℝ)|^1029 ≤ (6342580702489/20000000000000 : ℝ)^773
        have hw : |(52751053/125000000 : ℝ)|=(52751053/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5616207033/10000000000 : ℝ)|^1029 ≤ (11598568191903/25000000000000 : ℝ)^773
        have hw : |(5616207033/10000000000 : ℝ)|=(5616207033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(798665567/2500000000 : ℝ)|^1029 ≤ (5473205928551/25000000000000 : ℝ)^773
        have hw : |(798665567/2500000000 : ℝ)|=(798665567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1039_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (0 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5643/20000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base43 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*X 2 1) ≤ (0 : ℝ) := by
    linarith only [sign0]
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
  have hpowlo : (0 : ℝ) ^ (8231/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8231 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8231*1^2048 ≤ 0^2048*1^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8231/2048 : ℝ) ≤ (2515718283855826361/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8231 ≤ (2515718283855826361/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8231*100000000000000000000^2048 ≤ 2515718283855826361^2048*5^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2515718283855826361 100000000000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2515718283855826361/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8231 := by
      have hnat : (1 : ℕ)^2048*1^8231 ≤ 1^8231*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102515718283855826361/100000000000000000000 : ℝ) ≤ (16099219274533/16000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (102515718283855826361/100000000000000000000 : ℝ)^2048 ≤ (16099219274533/16000000000000 : ℝ)^8231 := by
      have hnat : (102515718283855826361 : ℕ)^2048*16000000000000^8231 ≤ 16099219274533^8231*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102515718283855826361 100000000000000000000 16099219274533 16000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (16099219274533/16000000000000 : ℝ)) (X := (102515718283855826361/100000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52515718283855826361/50000000000000000000 : ℝ) ≤ (8099219274533/8000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (52515718283855826361/50000000000000000000 : ℝ)^2048 ≤ (8099219274533/8000000000000 : ℝ)^8231 := by
      have hnat : (52515718283855826361 : ℕ)^2048*8000000000000^8231 ≤ 8099219274533^8231*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52515718283855826361 50000000000000000000 8099219274533 8000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (8099219274533/8000000000000 : ℝ)) (X := (52515718283855826361/50000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(99219274533/6400000000000 : ℝ)*(0 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(99219274533/6400000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2515718283855826361/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(99219274533/6400000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8231/2048 : ℝ) := by
    rw [show (1 : ℝ)+(99219274533/6400000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(16099219274533/16000000000000 : ℝ) by norm_num, show 1+(2515718283855826361/100000000000000000000 : ℝ)+(0 : ℝ)=(102515718283855826361/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2515718283855826361/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(99219274533/6400000000000 : ℝ)*(2/5 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(99219274533/6400000000000 : ℝ)*(2/5 : ℝ)=(8099219274533/8000000000000 : ℝ) by norm_num, show 1+2*(2515718283855826361/100000000000000000000 : ℝ)=(52515718283855826361/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(99219274533/6400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (99219274533/6400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(99219274533/6400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (99219274533/6400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(99219274533/6400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (99219274533/6400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5483197569/10000000000 : ℝ)*X 1 0+(-1347988311/5000000000 : ℝ)*X 1 1+(2397835097/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s0_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5486820813/10000000000 : ℝ)*X 2 0+(957006527/2000000000 : ℝ)*X 2 1+(-1352128307/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s0_1 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-1930300543/10000000000 : ℝ)*X 0 0+(2400587177/5000000000 : ℝ)*X 0 1+(377712217/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s0_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5166884087/10000000000 : ℝ)*X 1 0+(-1404265199/10000000000 : ℝ)*X 1 1+(1208679127/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s0_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5166878971/10000000000 : ℝ)*X 2 0+(3021700233/5000000000 : ℝ)*X 2 1+(-702132621/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s0_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((52751053/125000000 : ℝ)*X 0 0+(5616207033/10000000000 : ℝ)*X 0 1+(798665567/2500000000 : ℝ)*X 0 2+(52751053/125000000 : ℝ)*X 1 0+(5616207033/10000000000 : ℝ)*X 1 1+(798665567/2500000000 : ℝ)*X 1 2+(52751053/125000000 : ℝ)*X 2 0+(5616207033/10000000000 : ℝ)*X 2 1+(798665567/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s0_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(base43) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1571594874625776753633/320000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60597427/6250000000000 : ℝ)*(base19) + (165752601/12500000000000 : ℝ)*(base23) + (944581167/100000000000000 : ℝ)*(base39) + (19239059/12500000000000 : ℝ)*(upper2) + (412442313/100000000000000 : ℝ)*(upper5) + (76122643394881/12500000000000 : ℝ)*(major0) + (76122643394881/12500000000000 : ℝ)*(major1) + (608980202577881/100000000000000 : ℝ)*(major2) + (635937379/20000000000000 : ℝ)*(sp0) + (2165214023/100000000000000 : ℝ)*(sp1) + (161000647276969/20000000000000 : ℝ)*(sp2) + (402499543569559/50000000000000 : ℝ)*(sp3) + (402500344865591/50000000000000 : ℝ)*(sp4) + (10323948741107/2500000000000 : ℝ)*(sp5) + (10323948741107/2500000000000 : ℝ)*(f.failure) + (201251045241503/25000000000000 : ℝ)*(f.sum) + (3437373544443/640000000000000000000000000 : ℝ)*base66 + (4138861127773/640000000000000000000000000 : ℝ)*base67 + (143770044827/80000000000000000000000000 : ℝ)*base70 + (2246871143133/640000000000000000000000000 : ℝ)*base71 + (958260565637/640000000000000000000000000 : ℝ)*base73 + (227004902427/80000000000000000000000000 : ℝ)*base76 + (486836664107/80000000000000000000000000 : ℝ)*base78 + (499925546987/80000000000000000000000000 : ℝ)*base80 + (48723750613/40000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (141239/250000000000000000000 : ℝ)*base89 + (141239/250000000000000000000 : ℝ)*base91 + (141239/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1039_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5643/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1039_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1039_s1_0 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1068435783/5000000000 : ℝ)*x 0 + (1432454429/2500000000 : ℝ)*x 1 + (2490068987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068435783/5000000000 : ℝ)^1029 ≤ (12817882699311/100000000000000 : ℝ)^773 := by
    have hnat : (1068435783 : ℕ)^1029*100000000000000^773 ≤ 12817882699311^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068435783 5000000000 12817882699311 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1432454429/2500000000 : ℝ)^1029 ≤ (9529553294331/20000000000000 : ℝ)^773 := by
    have hnat : (1432454429 : ℕ)^1029*20000000000000^773 ≤ 9529553294331^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1432454429 2500000000 9529553294331 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2490068987/5000000000 : ℝ)^1029 ≤ (1976717540717/5000000000000 : ℝ)^773 := by
    have hnat : (2490068987 : ℕ)^1029*5000000000000^773 ≤ 1976717540717^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2490068987 5000000000 1976717540717 5000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1068435783/5000000000 : ℝ), (1432454429/2500000000 : ℝ), (2490068987/5000000000 : ℝ)] ![(12817882699311/100000000000000 : ℝ), (9529553294331/20000000000000 : ℝ), (1976717540717/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1068435783/5000000000 : ℝ)|^1029 ≤ (12817882699311/100000000000000 : ℝ)^773
        have hw : |(-1068435783/5000000000 : ℝ)|=(1068435783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1432454429/2500000000 : ℝ)|^1029 ≤ (9529553294331/20000000000000 : ℝ)^773
        have hw : |(1432454429/2500000000 : ℝ)|=(1432454429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2490068987/5000000000 : ℝ)|^1029 ≤ (1976717540717/5000000000000 : ℝ)^773
        have hw : |(2490068987/5000000000 : ℝ)|=(2490068987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s1_1 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5424805511/10000000000 : ℝ)*x 0 + (-2543627419/10000000000 : ℝ)*x 1 + (4980138293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5424805511/10000000000 : ℝ)^1029 ≤ (1772059293979/4000000000000 : ℝ)^773 := by
    have hnat : (5424805511 : ℕ)^1029*4000000000000^773 ≤ 1772059293979^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424805511 10000000000 1772059293979 4000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2543627419/10000000000 : ℝ)^1029 ≤ (2020520430561/12500000000000 : ℝ)^773 := by
    have hnat : (2543627419 : ℕ)^1029*12500000000000^773 ≤ 2020520430561^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2543627419 10000000000 2020520430561 12500000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4980138293/10000000000 : ℝ)^1029 ≤ (39534354185349/100000000000000 : ℝ)^773 := by
    have hnat : (4980138293 : ℕ)^1029*100000000000000^773 ≤ 39534354185349^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4980138293 10000000000 39534354185349 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5424805511/10000000000 : ℝ), (-2543627419/10000000000 : ℝ), (4980138293/10000000000 : ℝ)] ![(1772059293979/4000000000000 : ℝ), (2020520430561/12500000000000 : ℝ), (39534354185349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5424805511/10000000000 : ℝ)|^1029 ≤ (1772059293979/4000000000000 : ℝ)^773
        have hw : |(5424805511/10000000000 : ℝ)|=(5424805511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2543627419/10000000000 : ℝ)|^1029 ≤ (2020520430561/12500000000000 : ℝ)^773
        have hw : |(-2543627419/10000000000 : ℝ)|=(2543627419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4980138293/10000000000 : ℝ)|^1029 ≤ (39534354185349/100000000000000 : ℝ)^773
        have hw : |(4980138293/10000000000 : ℝ)|=(4980138293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s1_2 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2712402937/5000000000 : ℝ)*x 0 + (4980137833/10000000000 : ℝ)*x 1 + (-317953441/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2712402937/5000000000 : ℝ)^1029 ≤ (11075371573913/25000000000000 : ℝ)^773 := by
    have hnat : (2712402937 : ℕ)^1029*25000000000000^773 ≤ 11075371573913^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712402937 5000000000 11075371573913 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4980137833/10000000000 : ℝ)^1029 ≤ (19767174662167/50000000000000 : ℝ)^773 := by
    have hnat : (4980137833 : ℕ)^1029*50000000000000^773 ≤ 19767174662167^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4980137833 10000000000 19767174662167 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317953441/1250000000 : ℝ)^1029 ≤ (8082082183277/50000000000000 : ℝ)^773 := by
    have hnat : (317953441 : ℕ)^1029*50000000000000^773 ≤ 8082082183277^773*1250000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317953441 1250000000 8082082183277 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2712402937/5000000000 : ℝ), (4980137833/10000000000 : ℝ), (-317953441/1250000000 : ℝ)] ![(11075371573913/25000000000000 : ℝ), (19767174662167/50000000000000 : ℝ), (8082082183277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2712402937/5000000000 : ℝ)|^1029 ≤ (11075371573913/25000000000000 : ℝ)^773
        have hw : |(2712402937/5000000000 : ℝ)|=(2712402937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4980137833/10000000000 : ℝ)|^1029 ≤ (19767174662167/50000000000000 : ℝ)^773
        have hw : |(4980137833/10000000000 : ℝ)|=(4980137833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-317953441/1250000000 : ℝ)|^1029 ≤ (8082082183277/50000000000000 : ℝ)^773
        have hw : |(-317953441/1250000000 : ℝ)|=(317953441/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s1_3 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2163036139/5000000000 : ℝ)*x 0 + (1828795163/5000000000 : ℝ)*x 1 + (2559492937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163036139/5000000000 : ℝ)^1029 ≤ (32777536806177/100000000000000 : ℝ)^773 := by
    have hnat : (2163036139 : ℕ)^1029*100000000000000^773 ≤ 32777536806177^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163036139 5000000000 32777536806177 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1828795163/5000000000 : ℝ)^1029 ≤ (13107057770817/50000000000000 : ℝ)^773 := by
    have hnat : (1828795163 : ℕ)^1029*50000000000000^773 ≤ 13107057770817^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828795163 5000000000 13107057770817 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2559492937/5000000000 : ℝ)^1029 ≤ (8201669528209/20000000000000 : ℝ)^773 := by
    have hnat : (2559492937 : ℕ)^1029*20000000000000^773 ≤ 8201669528209^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559492937 5000000000 8201669528209 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163036139/5000000000 : ℝ), (1828795163/5000000000 : ℝ), (2559492937/5000000000 : ℝ)] ![(32777536806177/100000000000000 : ℝ), (13107057770817/50000000000000 : ℝ), (8201669528209/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163036139/5000000000 : ℝ)|^1029 ≤ (32777536806177/100000000000000 : ℝ)^773
        have hw : |(2163036139/5000000000 : ℝ)|=(2163036139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1828795163/5000000000 : ℝ)|^1029 ≤ (13107057770817/50000000000000 : ℝ)^773
        have hw : |(1828795163/5000000000 : ℝ)|=(1828795163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2559492937/5000000000 : ℝ)|^1029 ≤ (8201669528209/20000000000000 : ℝ)^773
        have hw : |(2559492937/5000000000 : ℝ)|=(2559492937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s1_4 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1068917891/5000000000 : ℝ)*x 0 + (4990776869/10000000000 : ℝ)*x 1 + (2859479509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068917891/5000000000 : ℝ)^1029 ≤ (12825582518599/100000000000000 : ℝ)^773 := by
    have hnat : (1068917891 : ℕ)^1029*100000000000000^773 ≤ 12825582518599^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068917891 5000000000 12825582518599 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4990776869/10000000000 : ℝ)^1029 ≤ (19823408137679/50000000000000 : ℝ)^773 := by
    have hnat : (4990776869 : ℕ)^1029*50000000000000^773 ≤ 19823408137679^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4990776869 10000000000 19823408137679 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2859479509/5000000000 : ℝ)^1029 ≤ (47527601189069/100000000000000 : ℝ)^773 := by
    have hnat : (2859479509 : ℕ)^1029*100000000000000^773 ≤ 47527601189069^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2859479509 5000000000 47527601189069 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1068917891/5000000000 : ℝ), (4990776869/10000000000 : ℝ), (2859479509/5000000000 : ℝ)] ![(12825582518599/100000000000000 : ℝ), (19823408137679/50000000000000 : ℝ), (47527601189069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1068917891/5000000000 : ℝ)|^1029 ≤ (12825582518599/100000000000000 : ℝ)^773
        have hw : |(-1068917891/5000000000 : ℝ)|=(1068917891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4990776869/10000000000 : ℝ)|^1029 ≤ (19823408137679/50000000000000 : ℝ)^773
        have hw : |(4990776869/10000000000 : ℝ)|=(4990776869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2859479509/5000000000 : ℝ)|^1029 ≤ (47527601189069/100000000000000 : ℝ)^773
        have hw : |(2859479509/5000000000 : ℝ)|=(2859479509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s1_5 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2616808017/5000000000 : ℝ)*x 0 + (-1804805193/10000000000 : ℝ)*x 1 + (45751681/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2616808017/5000000000 : ℝ)^1029 ≤ (10558821390661/25000000000000 : ℝ)^773 := by
    have hnat : (2616808017 : ℕ)^1029*25000000000000^773 ≤ 10558821390661^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616808017 5000000000 10558821390661 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1804805193/10000000000 : ℝ)^1029 ≤ (5118550496049/50000000000000 : ℝ)^773 := by
    have hnat : (1804805193 : ℕ)^1029*50000000000000^773 ≤ 5118550496049^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1804805193 10000000000 5118550496049 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45751681/80000000 : ℝ)^1029 ≤ (47527613435581/100000000000000 : ℝ)^773 := by
    have hnat : (45751681 : ℕ)^1029*100000000000000^773 ≤ 47527613435581^773*80000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45751681 80000000 47527613435581 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2616808017/5000000000 : ℝ), (-1804805193/10000000000 : ℝ), (45751681/80000000 : ℝ)] ![(10558821390661/25000000000000 : ℝ), (5118550496049/50000000000000 : ℝ), (47527613435581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2616808017/5000000000 : ℝ)|^1029 ≤ (10558821390661/25000000000000 : ℝ)^773
        have hw : |(2616808017/5000000000 : ℝ)|=(2616808017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1804805193/10000000000 : ℝ)|^1029 ≤ (5118550496049/50000000000000 : ℝ)^773
        have hw : |(-1804805193/10000000000 : ℝ)|=(1804805193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(45751681/80000000 : ℝ)|^1029 ≤ (47527613435581/100000000000000 : ℝ)^773
        have hw : |(45751681/80000000 : ℝ)|=(45751681/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s1_6 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (654201771/1250000000 : ℝ)*x 0 + (1429740543/2500000000 : ℝ)*x 1 + (-112800303/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (654201771/1250000000 : ℝ)^1029 ≤ (42235265516951/100000000000000 : ℝ)^773 := by
    have hnat : (654201771 : ℕ)^1029*100000000000000^773 ≤ 42235265516951^773*1250000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654201771 1250000000 42235265516951 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1429740543/2500000000 : ℝ)^1029 ≤ (23763818040561/50000000000000 : ℝ)^773 := by
    have hnat : (1429740543 : ℕ)^1029*50000000000000^773 ≤ 23763818040561^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1429740543 2500000000 23763818040561 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112800303/625000000 : ℝ)^1029 ≤ (2047419677427/20000000000000 : ℝ)^773 := by
    have hnat : (112800303 : ℕ)^1029*20000000000000^773 ≤ 2047419677427^773*625000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112800303 625000000 2047419677427 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(654201771/1250000000 : ℝ), (1429740543/2500000000 : ℝ), (-112800303/625000000 : ℝ)] ![(42235265516951/100000000000000 : ℝ), (23763818040561/50000000000000 : ℝ), (2047419677427/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(654201771/1250000000 : ℝ)|^1029 ≤ (42235265516951/100000000000000 : ℝ)^773
        have hw : |(654201771/1250000000 : ℝ)|=(654201771/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1429740543/2500000000 : ℝ)|^1029 ≤ (23763818040561/50000000000000 : ℝ)^773
        have hw : |(1429740543/2500000000 : ℝ)|=(1429740543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-112800303/625000000 : ℝ)|^1029 ≤ (2047419677427/20000000000000 : ℝ)^773
        have hw : |(-112800303/625000000 : ℝ)|=(112800303/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s1_7 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2163974453/5000000000 : ℝ)*x 0 + (1274560879/2500000000 : ℝ)*x 1 + (3678755413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163974453/5000000000 : ℝ)^1029 ≤ (32796465812103/100000000000000 : ℝ)^773 := by
    have hnat : (2163974453 : ℕ)^1029*100000000000000^773 ≤ 32796465812103^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163974453 5000000000 32796465812103 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1274560879/2500000000 : ℝ)^1029 ≤ (40787297607777/100000000000000 : ℝ)^773 := by
    have hnat : (1274560879 : ℕ)^1029*100000000000000^773 ≤ 40787297607777^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274560879 2500000000 40787297607777 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3678755413/10000000000 : ℝ)^1029 ≤ (26416236567629/100000000000000 : ℝ)^773 := by
    have hnat : (3678755413 : ℕ)^1029*100000000000000^773 ≤ 26416236567629^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3678755413 10000000000 26416236567629 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163974453/5000000000 : ℝ), (1274560879/2500000000 : ℝ), (3678755413/10000000000 : ℝ)] ![(32796465812103/100000000000000 : ℝ), (40787297607777/100000000000000 : ℝ), (26416236567629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163974453/5000000000 : ℝ)|^1029 ≤ (32796465812103/100000000000000 : ℝ)^773
        have hw : |(2163974453/5000000000 : ℝ)|=(2163974453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1274560879/2500000000 : ℝ)|^1029 ≤ (40787297607777/100000000000000 : ℝ)^773
        have hw : |(1274560879/2500000000 : ℝ)|=(1274560879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3678755413/10000000000 : ℝ)|^1029 ≤ (26416236567629/100000000000000 : ℝ)^773
        have hw : |(3678755413/10000000000 : ℝ)|=(3678755413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1039_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5643/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (158/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10459/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5643/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5643/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5643/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5643/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5643/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5643/20000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (0 : ℝ) ^ (8231/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8231 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8231*1^2048 ≤ 0^2048*1^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5643/20000 : ℝ) ^ (8231/2048 : ℝ) ≤ (618665256542528089/100000000000000000000 : ℝ) := by
    have hpowers : (5643/20000 : ℝ)^8231 ≤ (618665256542528089/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5643 : ℕ)^8231*100000000000000000000^2048 ≤ 618665256542528089^2048*20000^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5643 20000 618665256542528089 100000000000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5643/20000 : ℝ)) (X := (618665256542528089/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8231 := by
      have hnat : (1 : ℕ)^2048*1^8231 ≤ 1^8231*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100618665256542528089/100000000000000000000 : ℝ) ≤ (500767885369531/500000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (100618665256542528089/100000000000000000000 : ℝ)^2048 ≤ (500767885369531/500000000000000 : ℝ)^8231 := by
      have hnat : (100618665256542528089 : ℕ)^2048*500000000000000^8231 ≤ 500767885369531^8231*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100618665256542528089 100000000000000000000 500767885369531 500000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500767885369531/500000000000000 : ℝ)) (X := (100618665256542528089/100000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50618665256542528089/50000000000000000000 : ℝ) ≤ (250767885369531/250000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (50618665256542528089/50000000000000000000 : ℝ)^2048 ≤ (250767885369531/250000000000000 : ℝ)^8231 := by
      have hnat : (50618665256542528089 : ℕ)^2048*250000000000000^8231 ≤ 250767885369531^8231*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50618665256542528089 50000000000000000000 250767885369531 250000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250767885369531/250000000000000 : ℝ)) (X := (50618665256542528089/50000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(40415019449/7425000000000 : ℝ)*(0 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(40415019449/7425000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(618665256542528089/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(40415019449/7425000000000 : ℝ)*((5643/20000 : ℝ)+(0 : ℝ)))^(8231/2048 : ℝ) := by
    rw [show (1 : ℝ)+(40415019449/7425000000000 : ℝ)*((5643/20000 : ℝ)+(0 : ℝ))=(500767885369531/500000000000000 : ℝ) by norm_num, show 1+(618665256542528089/100000000000000000000 : ℝ)+(0 : ℝ)=(100618665256542528089/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(618665256542528089/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(40415019449/7425000000000 : ℝ)*(5643/20000 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(40415019449/7425000000000 : ℝ)*(5643/20000 : ℝ)=(250767885369531/250000000000000 : ℝ) by norm_num, show 1+2*(618665256542528089/100000000000000000000 : ℝ)=(50618665256542528089/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(40415019449/7425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (5643/20000 : ℝ)) (c := (1 : ℝ)) (alpha := (40415019449/7425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(40415019449/7425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (5643/20000 : ℝ)) (c := (1 : ℝ)) (alpha := (40415019449/7425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(40415019449/7425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (5643/20000 : ℝ)) (c := (1 : ℝ)) (alpha := (40415019449/7425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1068435783/5000000000 : ℝ)*X 0 0+(1432454429/2500000000 : ℝ)*X 0 1+(2490068987/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5424805511/10000000000 : ℝ)*X 1 0+(-2543627419/10000000000 : ℝ)*X 1 1+(4980138293/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2712402937/5000000000 : ℝ)*X 2 0+(4980137833/10000000000 : ℝ)*X 2 1+(-317953441/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2163036139/5000000000 : ℝ)*X 0 0+(1828795163/5000000000 : ℝ)*X 0 1+(2559492937/5000000000 : ℝ)*X 0 2+(2163036139/5000000000 : ℝ)*X 1 0+(1828795163/5000000000 : ℝ)*X 1 1+(2559492937/5000000000 : ℝ)*X 1 2+(2163036139/5000000000 : ℝ)*X 2 0+(1828795163/5000000000 : ℝ)*X 2 1+(2559492937/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1068917891/5000000000 : ℝ)*X 0 0+(4990776869/10000000000 : ℝ)*X 0 1+(2859479509/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2616808017/5000000000 : ℝ)*X 1 0+(-1804805193/10000000000 : ℝ)*X 1 1+(45751681/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((654201771/1250000000 : ℝ)*X 2 0+(1429740543/2500000000 : ℝ)*X 2 1+(-112800303/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2163974453/5000000000 : ℝ)*X 0 0+(1274560879/2500000000 : ℝ)*X 0 1+(3678755413/10000000000 : ℝ)*X 0 2+(2163974453/5000000000 : ℝ)*X 1 0+(1274560879/2500000000 : ℝ)*X 1 1+(3678755413/10000000000 : ℝ)*X 1 2+(2163974453/5000000000 : ℝ)*X 2 0+(1274560879/2500000000 : ℝ)*X 2 1+(3678755413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3725138165783892301183/495000000000000000000000000 : ℝ) := by norm_num
    linear_combination (117328981/100000000000000 : ℝ)*(base1) + (849705261/50000000000000 : ℝ)*(base19) + (894334727/50000000000000 : ℝ)*(base23) + (93083889/50000000000000 : ℝ)*(upper3) + (87240707/50000000000000 : ℝ)*(upper5) + (504551533553071/50000000000000 : ℝ)*(major0) + (504551533553071/50000000000000 : ℝ)*(major1) + (504551533553071/50000000000000 : ℝ)*(major2) + (1333911418290731/100000000000000 : ℝ)*(sp0) + (666959206669353/50000000000000 : ℝ)*(sp1) + (666959162039887/50000000000000 : ℝ)*(sp2) + (342140708233137/50000000000000 : ℝ)*(sp3) + (4405893739/50000000000000 : ℝ)*(sp4) + (4236816741/100000000000000 : ℝ)*(sp7) + (171071442652999/25000000000000 : ℝ)*(f.failure) + (333480028187307/25000000000000 : ℝ)*(f.sum) + (95328639541/185625000000000000000000000 : ℝ)*base66 + (3851929211807/742500000000000000000000000 : ℝ)*base68 + (3642791277379/1485000000000000000000000000 : ℝ)*base70 + (278453860639/92812500000000000000000000 : ℝ)*base72 + (895118536489/742500000000000000000000000 : ℝ)*base74 + (6756499568479/1485000000000000000000000000 : ℝ)*base76 + (6253008289787/742500000000000000000000000 : ℝ)*base78 + (4400527537577/742500000000000000000000000 : ℝ)*base80 + (1512140125087/1485000000000000000000000000 : ℝ)*base81 + (9187077/2500000000000000000000 : ℝ)*base90 + (9187077/2500000000000000000000 : ℝ)*base92 + (9187077/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27667027112117770451/20625000000000000000000000 : ℝ) := by norm_num
    linear_combination (1861248263/100000000000000 : ℝ)*(base19) + (216510899/12500000000000 : ℝ)*(base23) + (177267831/100000000000000 : ℝ)*(upper2) + (17593847/6250000000000 : ℝ)*(upper3) + (437332899/100000000000000 : ℝ)*(upper5) + (519440132999211/50000000000000 : ℝ)*(major0) + (519440132999211/50000000000000 : ℝ)*(major1) + (519440132999211/50000000000000 : ℝ)*(major2) + (22580837/250000000000 : ℝ)*(sp1) + (1925576579/20000000000000 : ℝ)*(sp2) + (343320603764101/25000000000000 : ℝ)*(sp4) + (68663576073667/5000000000000 : ℝ)*(sp5) + (343317763771579/25000000000000 : ℝ)*(sp6) + (704478072226047/100000000000000 : ℝ)*(sp7) + (704478072226047/100000000000000 : ℝ)*(f.failure) + (343320603764101/25000000000000 : ℝ)*(f.sum) + (900326142787/247500000000000000000000000 : ℝ)*base65 + (584692305677/123750000000000000000000000 : ℝ)*base68 + (4013707333433/495000000000000000000000000 : ℝ)*base70 + (867407538319/247500000000000000000000000 : ℝ)*base72 + (21837718601/7734375000000000000000000 : ℝ)*base73 + (1416250584293/495000000000000000000000000 : ℝ)*base76 + (37168985731/61875000000000000000000000 : ℝ)*base78 + (1382620199153/495000000000000000000000000 : ℝ)*base80 + (1181397117781/495000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (60401619/10000000000000000000000 : ℝ)*base89 + (60401619/10000000000000000000000 : ℝ)*base91 + (60401619/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1039_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5643/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (158/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10459/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1039_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1039_s2_0 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1097937881/5000000000 : ℝ)*x 0 + (1382875627/2500000000 : ℝ)*x 1 + (5141037977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097937881/5000000000 : ℝ)^1029 ≤ (13291171055337/100000000000000 : ℝ)^773 := by
    have hnat : (1097937881 : ℕ)^1029*100000000000000^773 ≤ 13291171055337^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097937881 5000000000 13291171055337 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1382875627/2500000000 : ℝ)^1029 ≤ (11366286967963/25000000000000 : ℝ)^773 := by
    have hnat : (1382875627 : ℕ)^1029*25000000000000^773 ≤ 11366286967963^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382875627 2500000000 11366286967963 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5141037977/10000000000 : ℝ)^1029 ≤ (20621840535577/50000000000000 : ℝ)^773 := by
    have hnat : (5141037977 : ℕ)^1029*50000000000000^773 ≤ 20621840535577^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5141037977 10000000000 20621840535577 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1097937881/5000000000 : ℝ), (1382875627/2500000000 : ℝ), (5141037977/10000000000 : ℝ)] ![(13291171055337/100000000000000 : ℝ), (11366286967963/25000000000000 : ℝ), (20621840535577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1097937881/5000000000 : ℝ)|^1029 ≤ (13291171055337/100000000000000 : ℝ)^773
        have hw : |(-1097937881/5000000000 : ℝ)|=(1097937881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1382875627/2500000000 : ℝ)|^1029 ≤ (11366286967963/25000000000000 : ℝ)^773
        have hw : |(1382875627/2500000000 : ℝ)|=(1382875627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5141037977/10000000000 : ℝ)|^1029 ≤ (20621840535577/50000000000000 : ℝ)^773
        have hw : |(5141037977/10000000000 : ℝ)|=(5141037977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s2_1 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2689202317/5000000000 : ℝ)*x 0 + (-95989671/400000000 : ℝ)*x 1 + (2570519389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689202317/5000000000 : ℝ)^1029 ≤ (8759554736181/20000000000000 : ℝ)^773 := by
    have hnat : (2689202317 : ℕ)^1029*20000000000000^773 ≤ 8759554736181^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689202317 5000000000 8759554736181 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (95989671/400000000 : ℝ)^1029 ≤ (14958536683821/100000000000000 : ℝ)^773 := by
    have hnat : (95989671 : ℕ)^1029*100000000000000^773 ≤ 14958536683821^773*400000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95989671 400000000 14958536683821 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2570519389/5000000000 : ℝ)^1029 ≤ (10310922406317/25000000000000 : ℝ)^773 := by
    have hnat : (2570519389 : ℕ)^1029*25000000000000^773 ≤ 10310922406317^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570519389 5000000000 10310922406317 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689202317/5000000000 : ℝ), (-95989671/400000000 : ℝ), (2570519389/5000000000 : ℝ)] ![(8759554736181/20000000000000 : ℝ), (14958536683821/100000000000000 : ℝ), (10310922406317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689202317/5000000000 : ℝ)|^1029 ≤ (8759554736181/20000000000000 : ℝ)^773
        have hw : |(2689202317/5000000000 : ℝ)|=(2689202317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-95989671/400000000 : ℝ)|^1029 ≤ (14958536683821/100000000000000 : ℝ)^773
        have hw : |(-95989671/400000000 : ℝ)|=(95989671/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2570519389/5000000000 : ℝ)|^1029 ≤ (10310922406317/25000000000000 : ℝ)^773
        have hw : |(2570519389/5000000000 : ℝ)|=(2570519389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s2_2 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5378404839/10000000000 : ℝ)*x 0 + (205641543/400000000 : ℝ)*x 1 + (-299967721/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378404839/10000000000 : ℝ)^1029 ≤ (43797775903131/100000000000000 : ℝ)^773 := by
    have hnat : (5378404839 : ℕ)^1029*100000000000000^773 ≤ 43797775903131^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378404839 10000000000 43797775903131 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205641543/400000000 : ℝ)^1029 ≤ (41243687457371/100000000000000 : ℝ)^773 := by
    have hnat : (205641543 : ℕ)^1029*100000000000000^773 ≤ 41243687457371^773*400000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205641543 400000000 41243687457371 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299967721/1250000000 : ℝ)^1029 ≤ (14958536625737/100000000000000 : ℝ)^773 := by
    have hnat : (299967721 : ℕ)^1029*100000000000000^773 ≤ 14958536625737^773*1250000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299967721 1250000000 14958536625737 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378404839/10000000000 : ℝ), (205641543/400000000 : ℝ), (-299967721/1250000000 : ℝ)] ![(43797775903131/100000000000000 : ℝ), (41243687457371/100000000000000 : ℝ), (14958536625737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378404839/10000000000 : ℝ)|^1029 ≤ (43797775903131/100000000000000 : ℝ)^773
        have hw : |(5378404839/10000000000 : ℝ)|=(5378404839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205641543/400000000 : ℝ)|^1029 ≤ (41243687457371/100000000000000 : ℝ)^773
        have hw : |(205641543/400000000 : ℝ)|=(205641543/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-299967721/1250000000 : ℝ)|^1029 ≤ (14958536625737/100000000000000 : ℝ)^773
        have hw : |(-299967721/1250000000 : ℝ)|=(299967721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s2_3 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (136443359/312500000 : ℝ)*x 0 + (500305281/1250000000 : ℝ)*x 1 + (595449549/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136443359/312500000 : ℝ)^1029 ≤ (16591379145609/50000000000000 : ℝ)^773 := by
    have hnat : (136443359 : ℕ)^1029*50000000000000^773 ≤ 16591379145609^773*312500000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136443359 312500000 16591379145609 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (500305281/1250000000 : ℝ)^1029 ≤ (1477726962291/5000000000000 : ℝ)^773 := by
    have hnat : (500305281 : ℕ)^1029*5000000000000^773 ≤ 1477726962291^773*1250000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500305281 1250000000 1477726962291 5000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (595449549/1250000000 : ℝ)^1029 ≤ (37262702445653/100000000000000 : ℝ)^773 := by
    have hnat : (595449549 : ℕ)^1029*100000000000000^773 ≤ 37262702445653^773*1250000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595449549 1250000000 37262702445653 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136443359/312500000 : ℝ), (500305281/1250000000 : ℝ), (595449549/1250000000 : ℝ)] ![(16591379145609/50000000000000 : ℝ), (1477726962291/5000000000000 : ℝ), (37262702445653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136443359/312500000 : ℝ)|^1029 ≤ (16591379145609/50000000000000 : ℝ)^773
        have hw : |(136443359/312500000 : ℝ)|=(136443359/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(500305281/1250000000 : ℝ)|^1029 ≤ (1477726962291/5000000000000 : ℝ)^773
        have hw : |(500305281/1250000000 : ℝ)|=(500305281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(595449549/1250000000 : ℝ)|^1029 ≤ (37262702445653/100000000000000 : ℝ)^773
        have hw : |(595449549/1250000000 : ℝ)|=(595449549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s2_4 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-549002751/2500000000 : ℝ)*x 0 + (2571966173/5000000000 : ℝ)*x 1 + (110571547/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549002751/2500000000 : ℝ)^1029 ≤ (6646130378203/50000000000000 : ℝ)^773 := by
    have hnat : (549002751 : ℕ)^1029*50000000000000^773 ≤ 6646130378203^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549002751 2500000000 6646130378203 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2571966173/5000000000 : ℝ)^1029 ≤ (322457763797/781250000000 : ℝ)^773 := by
    have hnat : (2571966173 : ℕ)^1029*781250000000^773 ≤ 322457763797^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571966173 5000000000 322457763797 781250000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110571547/200000000 : ℝ)^1029 ≤ (9086629092611/20000000000000 : ℝ)^773 := by
    have hnat : (110571547 : ℕ)^1029*20000000000000^773 ≤ 9086629092611^773*200000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110571547 200000000 9086629092611 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-549002751/2500000000 : ℝ), (2571966173/5000000000 : ℝ), (110571547/200000000 : ℝ)] ![(6646130378203/50000000000000 : ℝ), (322457763797/781250000000 : ℝ), (9086629092611/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-549002751/2500000000 : ℝ)|^1029 ≤ (6646130378203/50000000000000 : ℝ)^773
        have hw : |(-549002751/2500000000 : ℝ)|=(549002751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2571966173/5000000000 : ℝ)|^1029 ≤ (322457763797/781250000000 : ℝ)^773
        have hw : |(2571966173/5000000000 : ℝ)|=(2571966173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(110571547/200000000 : ℝ)|^1029 ≤ (9086629092611/20000000000000 : ℝ)^773
        have hw : |(110571547/200000000 : ℝ)|=(110571547/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s2_5 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5280037163/10000000000 : ℝ)*x 0 + (-2012203199/10000000000 : ℝ)*x 1 + (2764288703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280037163/10000000000 : ℝ)^1029 ≤ (42734700236901/100000000000000 : ℝ)^773 := by
    have hnat : (5280037163 : ℕ)^1029*100000000000000^773 ≤ 42734700236901^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280037163 10000000000 42734700236901 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2012203199/10000000000 : ℝ)^1029 ≤ (11832153663833/100000000000000 : ℝ)^773 := by
    have hnat : (2012203199 : ℕ)^1029*100000000000000^773 ≤ 11832153663833^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012203199 10000000000 11832153663833 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2764288703/5000000000 : ℝ)^1029 ≤ (2839571629729/6250000000000 : ℝ)^773 := by
    have hnat : (2764288703 : ℕ)^1029*6250000000000^773 ≤ 2839571629729^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2764288703 5000000000 2839571629729 6250000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280037163/10000000000 : ℝ), (-2012203199/10000000000 : ℝ), (2764288703/5000000000 : ℝ)] ![(42734700236901/100000000000000 : ℝ), (11832153663833/100000000000000 : ℝ), (2839571629729/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280037163/10000000000 : ℝ)|^1029 ≤ (42734700236901/100000000000000 : ℝ)^773
        have hw : |(5280037163/10000000000 : ℝ)|=(5280037163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2012203199/10000000000 : ℝ)|^1029 ≤ (11832153663833/100000000000000 : ℝ)^773
        have hw : |(-2012203199/10000000000 : ℝ)|=(2012203199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2764288703/5000000000 : ℝ)|^1029 ≤ (2839571629729/6250000000000 : ℝ)^773
        have hw : |(2764288703/5000000000 : ℝ)|=(2764288703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s2_6 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5280037373/10000000000 : ℝ)*x 0 + (2764288627/5000000000 : ℝ)*x 1 + (-503050781/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280037373/10000000000 : ℝ)^1029 ≤ (21367351249727/50000000000000 : ℝ)^773 := by
    have hnat : (5280037373 : ℕ)^1029*50000000000000^773 ≤ 21367351249727^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280037373 10000000000 21367351249727 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2764288627/5000000000 : ℝ)^1029 ≤ (11358286103217/25000000000000 : ℝ)^773 := by
    have hnat : (2764288627 : ℕ)^1029*25000000000000^773 ≤ 11358286103217^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2764288627 5000000000 11358286103217 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (503050781/2500000000 : ℝ)^1029 ≤ (2958038269191/25000000000000 : ℝ)^773 := by
    have hnat : (503050781 : ℕ)^1029*25000000000000^773 ≤ 2958038269191^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503050781 2500000000 2958038269191 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280037373/10000000000 : ℝ), (2764288627/5000000000 : ℝ), (-503050781/2500000000 : ℝ)] ![(21367351249727/50000000000000 : ℝ), (11358286103217/25000000000000 : ℝ), (2958038269191/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280037373/10000000000 : ℝ)|^1029 ≤ (21367351249727/50000000000000 : ℝ)^773
        have hw : |(5280037373/10000000000 : ℝ)|=(5280037373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2764288627/5000000000 : ℝ)|^1029 ≤ (11358286103217/25000000000000 : ℝ)^773
        have hw : |(2764288627/5000000000 : ℝ)|=(2764288627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-503050781/2500000000 : ℝ)|^1029 ≤ (2958038269191/25000000000000 : ℝ)^773
        have hw : |(-503050781/2500000000 : ℝ)|=(503050781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s2_7 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (272903223/625000000 : ℝ)*x 0 + (29737223/62500000 : ℝ)*x 1 + (400814343/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272903223/625000000 : ℝ)^1029 ≤ (16592714989931/50000000000000 : ℝ)^773 := by
    have hnat : (272903223 : ℕ)^1029*50000000000000^773 ≤ 16592714989931^773*625000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272903223 625000000 16592714989931 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (29737223/62500000 : ℝ)^1029 ≤ (7440795462463/20000000000000 : ℝ)^773 := by
    have hnat : (29737223 : ℕ)^1029*20000000000000^773 ≤ 7440795462463^773*62500000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29737223 62500000 7440795462463 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (400814343/1000000000 : ℝ)^1029 ≤ (5922118537851/20000000000000 : ℝ)^773 := by
    have hnat : (400814343 : ℕ)^1029*20000000000000^773 ≤ 5922118537851^773*1000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400814343 1000000000 5922118537851 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272903223/625000000 : ℝ), (29737223/62500000 : ℝ), (400814343/1000000000 : ℝ)] ![(16592714989931/50000000000000 : ℝ), (7440795462463/20000000000000 : ℝ), (5922118537851/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272903223/625000000 : ℝ)|^1029 ≤ (16592714989931/50000000000000 : ℝ)^773
        have hw : |(272903223/625000000 : ℝ)|=(272903223/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(29737223/62500000 : ℝ)|^1029 ≤ (7440795462463/20000000000000 : ℝ)^773
        have hw : |(29737223/62500000 : ℝ)|=(29737223/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(400814343/1000000000 : ℝ)|^1029 ≤ (5922118537851/20000000000000 : ℝ)^773
        have hw : |(400814343/1000000000 : ℝ)|=(400814343/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1039_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10459/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (158/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (8579/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1683/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10459/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (158/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10459/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (158/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10459/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (158/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10459/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (158/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10459/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (158/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10459/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (158/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (158/3125 : ℝ) ^ (8231/2048 : ℝ) ≤ (308684557656489/50000000000000000000 : ℝ) := by
    have hpowers : (158/3125 : ℝ)^8231 ≤ (308684557656489/50000000000000000000 : ℝ)^2048 := by
      have hnat : (158 : ℕ)^8231*50000000000000000000^2048 ≤ 308684557656489^2048*3125^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        158 3125 308684557656489 50000000000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (158/3125 : ℝ)) (X := (308684557656489/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10459/50000 : ℝ) ^ (8231/2048 : ℝ) ≤ (1451882102256591/781250000000000000 : ℝ) := by
    have hpowers : (10459/50000 : ℝ)^8231 ≤ (1451882102256591/781250000000000000 : ℝ)^2048 := by
      have hnat : (10459 : ℕ)^8231*781250000000000000^2048 ≤ 1451882102256591^2048*50000^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10459 50000 1451882102256591 781250000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10459/50000 : ℝ)) (X := (1451882102256591/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000308684557656489/25000000000000000000 : ℝ) ≤ (10000030722052839/10000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (25000308684557656489/25000000000000000000 : ℝ)^2048 ≤ (10000030722052839/10000000000000000 : ℝ)^8231 := by
      have hnat : (25000308684557656489 : ℕ)^2048*10000000000000000^8231 ≤ 10000030722052839^8231*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000308684557656489 25000000000000000000 10000030722052839 10000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000030722052839/10000000000000000 : ℝ)) (X := (25000308684557656489/25000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50093229139102078313/50000000000000000000 : ℝ) ≤ (10004636124584811/10000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (50093229139102078313/50000000000000000000 : ℝ)^2048 ≤ (10004636124584811/10000000000000000 : ℝ)^8231 := by
      have hnat : (50093229139102078313 : ℕ)^2048*10000000000000000^8231 ≤ 10004636124584811^8231*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50093229139102078313 50000000000000000000 10004636124584811 10000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004636124584811/10000000000000000 : ℝ)) (X := (50093229139102078313/50000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (392076882102256591/390625000000000000 : ℝ) ≤ (10009241527116783/10000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (392076882102256591/390625000000000000 : ℝ)^2048 ≤ (10009241527116783/10000000000000000 : ℝ)^8231 := by
      have hnat : (392076882102256591 : ℕ)^2048*10000000000000000^8231 ≤ 10009241527116783^8231*390625000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        392076882102256591 390625000000000000 10009241527116783 10000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009241527116783/10000000000000000 : ℝ)) (X := (392076882102256591/390625000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(308684557656489/50000000000000000000 : ℝ) ≤ ((7207905340127219607/7210000000000000000 : ℝ)+2*(104668239363/36050000000000 : ℝ)*(158/3125 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (7207905340127219607/7210000000000000000 : ℝ)+2*(104668239363/36050000000000 : ℝ)*(158/3125 : ℝ)=(10000030722052839/10000000000000000 : ℝ) by norm_num, show 1+2*(308684557656489/50000000000000000000 : ℝ)=(25000308684557656489/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1451882102256591/781250000000000000 : ℝ)+(308684557656489/50000000000000000000 : ℝ) ≤ ((7207905340127219607/7210000000000000000 : ℝ)+(104668239363/36050000000000 : ℝ)*((10459/50000 : ℝ)+(158/3125 : ℝ)))^(8231/2048 : ℝ) := by
    rw [show (7207905340127219607/7210000000000000000 : ℝ)+(104668239363/36050000000000 : ℝ)*((10459/50000 : ℝ)+(158/3125 : ℝ))=(10004636124584811/10000000000000000 : ℝ) by norm_num, show 1+(1451882102256591/781250000000000000 : ℝ)+(308684557656489/50000000000000000000 : ℝ)=(50093229139102078313/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1451882102256591/781250000000000000 : ℝ) ≤ ((7207905340127219607/7210000000000000000 : ℝ)+2*(104668239363/36050000000000 : ℝ)*(10459/50000 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (7207905340127219607/7210000000000000000 : ℝ)+2*(104668239363/36050000000000 : ℝ)*(10459/50000 : ℝ)=(10009241527116783/10000000000000000 : ℝ) by norm_num, show 1+2*(1451882102256591/781250000000000000 : ℝ)=(392076882102256591/390625000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7207905340127219607/7210000000000000000 : ℝ)*(X 1 0+X 2 0)+(104668239363/36050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (158/3125 : ℝ)) (hi := (10459/50000 : ℝ)) (c := (7207905340127219607/7210000000000000000 : ℝ)) (alpha := (104668239363/36050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7207905340127219607/7210000000000000000 : ℝ)*(X 0 1+X 2 1)+(104668239363/36050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (158/3125 : ℝ)) (hi := (10459/50000 : ℝ)) (c := (7207905340127219607/7210000000000000000 : ℝ)) (alpha := (104668239363/36050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7207905340127219607/7210000000000000000 : ℝ)*(X 0 2+X 1 2)+(104668239363/36050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (158/3125 : ℝ)) (hi := (10459/50000 : ℝ)) (c := (7207905340127219607/7210000000000000000 : ℝ)) (alpha := (104668239363/36050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1097937881/5000000000 : ℝ)*X 0 0+(1382875627/2500000000 : ℝ)*X 0 1+(5141037977/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2689202317/5000000000 : ℝ)*X 1 0+(-95989671/400000000 : ℝ)*X 1 1+(2570519389/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5378404839/10000000000 : ℝ)*X 2 0+(205641543/400000000 : ℝ)*X 2 1+(-299967721/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((136443359/312500000 : ℝ)*X 0 0+(500305281/1250000000 : ℝ)*X 0 1+(595449549/1250000000 : ℝ)*X 0 2+(136443359/312500000 : ℝ)*X 1 0+(500305281/1250000000 : ℝ)*X 1 1+(595449549/1250000000 : ℝ)*X 1 2+(136443359/312500000 : ℝ)*X 2 0+(500305281/1250000000 : ℝ)*X 2 1+(595449549/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-549002751/2500000000 : ℝ)*X 0 0+(2571966173/5000000000 : ℝ)*X 0 1+(110571547/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280037163/10000000000 : ℝ)*X 1 0+(-2012203199/10000000000 : ℝ)*X 1 1+(2764288703/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5280037373/10000000000 : ℝ)*X 2 0+(2764288627/5000000000 : ℝ)*X 2 1+(-503050781/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((272903223/625000000 : ℝ)*X 0 0+(29737223/62500000 : ℝ)*X 0 1+(400814343/1000000000 : ℝ)*X 0 2+(272903223/625000000 : ℝ)*X 1 0+(29737223/62500000 : ℝ)*X 1 1+(400814343/1000000000 : ℝ)*X 1 2+(272903223/625000000 : ℝ)*X 2 0+(29737223/62500000 : ℝ)*X 2 1+(400814343/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36041144089726704270862833/10300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (979774469/100000000000000 : ℝ)*(base19) + (491667677/50000000000000 : ℝ)*(base23) + (78754693/50000000000000 : ℝ)*(upper3) + (12646727/25000000000000 : ℝ)*(upper4) + (6917737/6250000000000 : ℝ)*(upper5) + (387488290916811/20000000000000 : ℝ)*(major0) + (387488290916811/20000000000000 : ℝ)*(major1) + (387488290916811/20000000000000 : ℝ)*(major2) + (2561065305987251/100000000000000 : ℝ)*(sp0) + (640269459930201/25000000000000 : ℝ)*(sp1) + (2561077836159919/100000000000000 : ℝ)*(sp2) + (656899394398937/50000000000000 : ℝ)*(sp3) + (6756754011/50000000000000 : ℝ)*(sp4) + (5184236951/100000000000000 : ℝ)*(sp7) + (52552158921393/4000000000000 : ℝ)*(f.failure) + (320134852436909/12500000000000 : ℝ)*(f.sum) + (23291520713/6437500000000000000000000 : ℝ)*base65 + (84268660907812389/20600000000000000000000000000000 : ℝ)*base68 + (20581039915612389/20600000000000000000000000000000 : ℝ)*base70 + (26835835093787611/20600000000000000000000000000000 : ℝ)*base71 + (128651135601/51500000000000000000000000 : ℝ)*base73 + (14730734366612389/20600000000000000000000000000000 : ℝ)*base76 + (108666403610787611/20600000000000000000000000000000 : ℝ)*base77 + (183747509190812389/20600000000000000000000000000000 : ℝ)*base80 + (1076172933/321875000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (128739/400000000000000000000 : ℝ)*base90 + (128739/400000000000000000000 : ℝ)*base92 + (128739/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29875002754886960597847/3605000000000000000000000000 : ℝ) := by norm_num
    linear_combination (399267381/25000000000000 : ℝ)*(base19) + (1812273789/100000000000000 : ℝ)*(base23) + (5098417/2500000000000 : ℝ)*(upper3) + (42631611/100000000000000 : ℝ)*(lower4) + (188919191/100000000000000 : ℝ)*(upper5) + (1966733625256069/100000000000000 : ℝ)*(major0) + (1966733625256069/100000000000000 : ℝ)*(major1) + (1966733625256069/100000000000000 : ℝ)*(major2) + (1692539257/12500000000000 : ℝ)*(sp1) + (15207663369/100000000000000 : ℝ)*(sp2) + (1299899801750973/50000000000000 : ℝ)*(sp4) + (1299892233059183/50000000000000 : ℝ)*(sp5) + (2599782583564789/100000000000000 : ℝ)*(sp6) + (333416842693363/25000000000000 : ℝ)*(sp7) + (333416842693363/25000000000000 : ℝ)*(f.failure) + (1299899801750973/50000000000000 : ℝ)*(f.sum) + (16131172566933/1802500000000000000000000000 : ℝ)*base66 + (352737431785944883/721000000000000000000000000000000 : ℝ)*base67 + (4562951476521944883/721000000000000000000000000000000 : ℝ)*base69 + (5908997039276055117/721000000000000000000000000000000 : ℝ)*base72 + (30969478303/7041015625000000000000000 : ℝ)*base74 + (4817335371377944883/721000000000000000000000000000000 : ℝ)*base75 + (1407744092722055117/721000000000000000000000000000000 : ℝ)*base78 + (5012096142279055117/721000000000000000000000000000000 : ℝ)*base80 + (2992695998617/1802500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (17272951/2500000000000000000000 : ℝ)*base89 + (17272951/2500000000000000000000 : ℝ)*base91 + (17272951/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1039_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10459/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (158/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8579/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1683/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1039_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1039_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8579/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1683/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1039_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1039_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1039_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8579/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1683/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1039_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

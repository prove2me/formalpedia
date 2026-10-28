-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1073_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:11:57.83253+00:00
-- url     : https://prove2.me/submissions/d0ac9984-39c4-403c-96b6-eb5a9330c977

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
theorem support_rectangle_w1073_s0_0 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1913842611/10000000000 : ℝ)*x 0 + (607041579/1000000000 : ℝ)*x 1 + (4771684093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1913842611/10000000000 : ℝ)^4133 ≤ (5550860238077/50000000000000 : ℝ)^3109 := by
    have hnat : (1913842611 : ℕ)^4133*50000000000000^3109 ≤ 5550860238077^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913842611 10000000000 5550860238077 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (607041579/1000000000 : ℝ)^4133 ≤ (51501263761687/100000000000000 : ℝ)^3109 := by
    have hnat : (607041579 : ℕ)^4133*100000000000000^3109 ≤ 51501263761687^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      607041579 1000000000 51501263761687 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4771684093/10000000000 : ℝ)^4133 ≤ (37397015741967/100000000000000 : ℝ)^3109 := by
    have hnat : (4771684093 : ℕ)^4133*100000000000000^3109 ≤ 37397015741967^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4771684093 10000000000 37397015741967 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1913842611/10000000000 : ℝ), (607041579/1000000000 : ℝ), (4771684093/10000000000 : ℝ)] ![(5550860238077/50000000000000 : ℝ), (51501263761687/100000000000000 : ℝ), (37397015741967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1913842611/10000000000 : ℝ)|^4133 ≤ (5550860238077/50000000000000 : ℝ)^3109
        have hw : |(-1913842611/10000000000 : ℝ)|=(1913842611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(607041579/1000000000 : ℝ)|^4133 ≤ (51501263761687/100000000000000 : ℝ)^3109
        have hw : |(607041579/1000000000 : ℝ)|=(607041579/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4771684093/10000000000 : ℝ)|^4133 ≤ (37397015741967/100000000000000 : ℝ)^3109
        have hw : |(4771684093/10000000000 : ℝ)|=(4771684093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s0_1 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5520679053/10000000000 : ℝ)*x 0 + (-2661191321/10000000000 : ℝ)*x 1 + (4771684131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5520679053/10000000000 : ℝ)^4133 ≤ (45395573799553/100000000000000 : ℝ)^3109 := by
    have hnat : (5520679053 : ℕ)^4133*100000000000000^3109 ≤ 45395573799553^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520679053 10000000000 45395573799553 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2661191321/10000000000 : ℝ)^4133 ≤ (17207410054103/100000000000000 : ℝ)^3109 := by
    have hnat : (2661191321 : ℕ)^4133*100000000000000^3109 ≤ 17207410054103^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2661191321 10000000000 17207410054103 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4771684131/10000000000 : ℝ)^4133 ≤ (18698508068937/50000000000000 : ℝ)^3109 := by
    have hnat : (4771684131 : ℕ)^4133*50000000000000^3109 ≤ 18698508068937^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4771684131 10000000000 18698508068937 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5520679053/10000000000 : ℝ), (-2661191321/10000000000 : ℝ), (4771684131/10000000000 : ℝ)] ![(45395573799553/100000000000000 : ℝ), (17207410054103/100000000000000 : ℝ), (18698508068937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5520679053/10000000000 : ℝ)|^4133 ≤ (45395573799553/100000000000000 : ℝ)^3109
        have hw : |(5520679053/10000000000 : ℝ)|=(5520679053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2661191321/10000000000 : ℝ)|^4133 ≤ (17207410054103/100000000000000 : ℝ)^3109
        have hw : |(-2661191321/10000000000 : ℝ)|=(2661191321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4771684131/10000000000 : ℝ)|^4133 ≤ (18698508068937/50000000000000 : ℝ)^3109
        have hw : |(4771684131/10000000000 : ℝ)|=(4771684131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s0_2 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2760339543/5000000000 : ℝ)*x 0 + (149115129/312500000 : ℝ)*x 1 + (-2661191283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2760339543/5000000000 : ℝ)^4133 ≤ (45395574160281/100000000000000 : ℝ)^3109 := by
    have hnat : (2760339543 : ℕ)^4133*100000000000000^3109 ≤ 45395574160281^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760339543 5000000000 45395574160281 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149115129/312500000 : ℝ)^4133 ≤ (18698508053309/50000000000000 : ℝ)^3109 := by
    have hnat : (149115129 : ℕ)^4133*50000000000000^3109 ≤ 18698508053309^3109*312500000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149115129 312500000 18698508053309 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2661191283/10000000000 : ℝ)^4133 ≤ (2150926215933/12500000000000 : ℝ)^3109 := by
    have hnat : (2661191283 : ℕ)^4133*12500000000000^3109 ≤ 2150926215933^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2661191283 10000000000 2150926215933 12500000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2760339543/5000000000 : ℝ), (149115129/312500000 : ℝ), (-2661191283/10000000000 : ℝ)] ![(45395574160281/100000000000000 : ℝ), (18698508053309/50000000000000 : ℝ), (2150926215933/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2760339543/5000000000 : ℝ)|^4133 ≤ (45395574160281/100000000000000 : ℝ)^3109
        have hw : |(2760339543/5000000000 : ℝ)|=(2760339543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(149115129/312500000 : ℝ)|^4133 ≤ (18698508053309/50000000000000 : ℝ)^3109
        have hw : |(149115129/312500000 : ℝ)|=(149115129/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2661191283/10000000000 : ℝ)|^4133 ≤ (2150926215933/12500000000000 : ℝ)^3109
        have hw : |(-2661191283/10000000000 : ℝ)|=(2661191283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s0_3 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105165767/250000000 : ℝ)*x 0 + (1562247413/5000000000 : ℝ)*x 1 + (5673365357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105165767/250000000 : ℝ)^4133 ≤ (6325589711737/20000000000000 : ℝ)^3109 := by
    have hnat : (105165767 : ℕ)^4133*20000000000000^3109 ≤ 6325589711737^3109*250000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105165767 250000000 6325589711737 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1562247413/5000000000 : ℝ)^4133 ≤ (21299885897691/100000000000000 : ℝ)^3109 := by
    have hnat : (1562247413 : ℕ)^4133*100000000000000^3109 ≤ 21299885897691^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1562247413 5000000000 21299885897691 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5673365357/10000000000 : ℝ)^4133 ≤ (9414433103473/20000000000000 : ℝ)^3109 := by
    have hnat : (5673365357 : ℕ)^4133*20000000000000^3109 ≤ 9414433103473^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5673365357 10000000000 9414433103473 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105165767/250000000 : ℝ), (1562247413/5000000000 : ℝ), (5673365357/10000000000 : ℝ)] ![(6325589711737/20000000000000 : ℝ), (21299885897691/100000000000000 : ℝ), (9414433103473/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105165767/250000000 : ℝ)|^4133 ≤ (6325589711737/20000000000000 : ℝ)^3109
        have hw : |(105165767/250000000 : ℝ)|=(105165767/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1562247413/5000000000 : ℝ)|^4133 ≤ (21299885897691/100000000000000 : ℝ)^3109
        have hw : |(1562247413/5000000000 : ℝ)|=(1562247413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5673365357/10000000000 : ℝ)|^4133 ≤ (9414433103473/20000000000000 : ℝ)^3109
        have hw : |(5673365357/10000000000 : ℝ)|=(5673365357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s0_4 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1919194727/10000000000 : ℝ)*x 0 + (4805215639/10000000000 : ℝ)*x 1 + (301785531/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1919194727/10000000000 : ℝ)^4133 ≤ (696438209583/6250000000000 : ℝ)^3109 := by
    have hnat : (1919194727 : ℕ)^4133*6250000000000^3109 ≤ 696438209583^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919194727 10000000000 696438209583 6250000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4805215639/10000000000 : ℝ)^4133 ≤ (1509870865349/4000000000000 : ℝ)^3109 := by
    have hnat : (4805215639 : ℕ)^4133*4000000000000^3109 ≤ 1509870865349^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4805215639 10000000000 1509870865349 4000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (301785531/500000000 : ℝ)^4133 ≤ (25555108498559/50000000000000 : ℝ)^3109 := by
    have hnat : (301785531 : ℕ)^4133*50000000000000^3109 ≤ 25555108498559^3109*500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301785531 500000000 25555108498559 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1919194727/10000000000 : ℝ), (4805215639/10000000000 : ℝ), (301785531/500000000 : ℝ)] ![(696438209583/6250000000000 : ℝ), (1509870865349/4000000000000 : ℝ), (25555108498559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1919194727/10000000000 : ℝ)|^4133 ≤ (696438209583/6250000000000 : ℝ)^3109
        have hw : |(-1919194727/10000000000 : ℝ)|=(1919194727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4805215639/10000000000 : ℝ)|^4133 ≤ (1509870865349/4000000000000 : ℝ)^3109
        have hw : |(4805215639/10000000000 : ℝ)|=(4805215639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(301785531/500000000 : ℝ)|^4133 ≤ (25555108498559/50000000000000 : ℝ)^3109
        have hw : |(301785531/500000000 : ℝ)|=(301785531/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s0_5 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (516814457/1000000000 : ℝ)*x 0 + (-27943367/200000000 : ℝ)*x 1 + (3017854241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516814457/1000000000 : ℝ)^4133 ≤ (4158308762557/10000000000000 : ℝ)^3109 := by
    have hnat : (516814457 : ℕ)^4133*10000000000000^3109 ≤ 4158308762557^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516814457 1000000000 4158308762557 10000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27943367/200000000 : ℝ)^4133 ≤ (7306719428197/100000000000000 : ℝ)^3109 := by
    have hnat : (27943367 : ℕ)^4133*100000000000000^3109 ≤ 7306719428197^3109*200000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27943367 200000000 7306719428197 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3017854241/5000000000 : ℝ)^4133 ≤ (51110192929579/100000000000000 : ℝ)^3109 := by
    have hnat : (3017854241 : ℕ)^4133*100000000000000^3109 ≤ 51110192929579^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3017854241 5000000000 51110192929579 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(516814457/1000000000 : ℝ), (-27943367/200000000 : ℝ), (3017854241/5000000000 : ℝ)] ![(4158308762557/10000000000000 : ℝ), (7306719428197/100000000000000 : ℝ), (51110192929579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(516814457/1000000000 : ℝ)|^4133 ≤ (4158308762557/10000000000000 : ℝ)^3109
        have hw : |(516814457/1000000000 : ℝ)|=(516814457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27943367/200000000 : ℝ)|^4133 ≤ (7306719428197/100000000000000 : ℝ)^3109
        have hw : |(-27943367/200000000 : ℝ)|=(27943367/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3017854241/5000000000 : ℝ)|^4133 ≤ (51110192929579/100000000000000 : ℝ)^3109
        have hw : |(3017854241/5000000000 : ℝ)|=(3017854241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s0_6 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5168144487/10000000000 : ℝ)*x 0 + (6035709989/10000000000 : ℝ)*x 1 + (-1397166037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168144487/10000000000 : ℝ)^4133 ≤ (41583086737791/100000000000000 : ℝ)^3109 := by
    have hnat : (5168144487 : ℕ)^4133*100000000000000^3109 ≤ 41583086737791^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168144487 10000000000 41583086737791 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6035709989/10000000000 : ℝ)^4133 ≤ (51110209893929/100000000000000 : ℝ)^3109 := by
    have hnat : (6035709989 : ℕ)^4133*100000000000000^3109 ≤ 51110209893929^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6035709989 10000000000 51110209893929 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1397166037/10000000000 : ℝ)^4133 ≤ (7306703347907/100000000000000 : ℝ)^3109 := by
    have hnat : (1397166037 : ℕ)^4133*100000000000000^3109 ≤ 7306703347907^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397166037 10000000000 7306703347907 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168144487/10000000000 : ℝ), (6035709989/10000000000 : ℝ), (-1397166037/10000000000 : ℝ)] ![(41583086737791/100000000000000 : ℝ), (51110209893929/100000000000000 : ℝ), (7306703347907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168144487/10000000000 : ℝ)|^4133 ≤ (41583086737791/100000000000000 : ℝ)^3109
        have hw : |(5168144487/10000000000 : ℝ)|=(5168144487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6035709989/10000000000 : ℝ)|^4133 ≤ (51110209893929/100000000000000 : ℝ)^3109
        have hw : |(6035709989/10000000000 : ℝ)|=(6035709989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1397166037/10000000000 : ℝ)|^4133 ≤ (7306703347907/100000000000000 : ℝ)^3109
        have hw : |(-1397166037/10000000000 : ℝ)|=(1397166037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s0_7 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4217133069/10000000000 : ℝ)*x 0 + (2803777153/5000000000 : ℝ)*x 1 + (319260871/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4217133069/10000000000 : ℝ)^4133 ≤ (31732962714931/100000000000000 : ℝ)^3109 := by
    have hnat : (4217133069 : ℕ)^4133*100000000000000^3109 ≤ 31732962714931^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217133069 10000000000 31732962714931 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2803777153/5000000000 : ℝ)^4133 ≤ (46347672286159/100000000000000 : ℝ)^3109 := by
    have hnat : (2803777153 : ℕ)^4133*100000000000000^3109 ≤ 46347672286159^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2803777153 5000000000 46347672286159 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319260871/1000000000 : ℝ)^4133 ≤ (5479841248487/25000000000000 : ℝ)^3109 := by
    have hnat : (319260871 : ℕ)^4133*25000000000000^3109 ≤ 5479841248487^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319260871 1000000000 5479841248487 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4217133069/10000000000 : ℝ), (2803777153/5000000000 : ℝ), (319260871/1000000000 : ℝ)] ![(31732962714931/100000000000000 : ℝ), (46347672286159/100000000000000 : ℝ), (5479841248487/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4217133069/10000000000 : ℝ)|^4133 ≤ (31732962714931/100000000000000 : ℝ)^3109
        have hw : |(4217133069/10000000000 : ℝ)|=(4217133069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2803777153/5000000000 : ℝ)|^4133 ≤ (46347672286159/100000000000000 : ℝ)^3109
        have hw : |(2803777153/5000000000 : ℝ)|=(2803777153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(319260871/1000000000 : ℝ)|^4133 ≤ (5479841248487/25000000000000 : ℝ)^3109
        have hw : |(319260871/1000000000 : ℝ)|=(319260871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1073_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (63/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14041/50000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8265/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8265 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8265*1^2048 ≤ 0^2048*1^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8265/2048 : ℝ) ≤ (247773913400089841/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8265 ≤ (247773913400089841/10000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8265*10000000000000000000^2048 ≤ 247773913400089841^2048*5^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 247773913400089841 10000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (247773913400089841/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8265 := by
      have hnat : (1 : ℕ)^2048*1^8265 ≤ 1^8265*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10247773913400089841/10000000000000000000 : ℝ) ≤ (5030416181647287/5000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (10247773913400089841/10000000000000000000 : ℝ)^2048 ≤ (5030416181647287/5000000000000000 : ℝ)^8265 := by
      have hnat : (10247773913400089841 : ℕ)^2048*5000000000000000^8265 ≤ 5030416181647287^8265*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10247773913400089841 10000000000000000000 5030416181647287 5000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5030416181647287/5000000000000000 : ℝ)) (X := (10247773913400089841/10000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5247773913400089841/5000000000000000000 : ℝ) ≤ (2530416181647287/2500000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (5247773913400089841/5000000000000000000 : ℝ)^2048 ≤ (2530416181647287/2500000000000000 : ℝ)^8265 := by
      have hnat : (5247773913400089841 : ℕ)^2048*2500000000000000^8265 ≤ 2530416181647287^8265*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5247773913400089841 5000000000000000000 2530416181647287 2500000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2530416181647287/2500000000000000 : ℝ)) (X := (5247773913400089841/5000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(30416181647287/2000000000000000 : ℝ)*(0 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(30416181647287/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(247773913400089841/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(30416181647287/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8265/2048 : ℝ) := by
    rw [show (1 : ℝ)+(30416181647287/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5030416181647287/5000000000000000 : ℝ) by norm_num, show 1+(247773913400089841/10000000000000000000 : ℝ)+(0 : ℝ)=(10247773913400089841/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(247773913400089841/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(30416181647287/2000000000000000 : ℝ)*(2/5 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(30416181647287/2000000000000000 : ℝ)*(2/5 : ℝ)=(2530416181647287/2500000000000000 : ℝ) by norm_num, show 1+2*(247773913400089841/10000000000000000000 : ℝ)=(5247773913400089841/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(30416181647287/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30416181647287/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(30416181647287/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30416181647287/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(30416181647287/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30416181647287/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1913842611/10000000000 : ℝ)*X 0 0+(607041579/1000000000 : ℝ)*X 0 1+(4771684093/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5520679053/10000000000 : ℝ)*X 1 0+(-2661191321/10000000000 : ℝ)*X 1 1+(4771684131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2760339543/5000000000 : ℝ)*X 2 0+(149115129/312500000 : ℝ)*X 2 1+(-2661191283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((105165767/250000000 : ℝ)*X 0 0+(1562247413/5000000000 : ℝ)*X 0 1+(5673365357/10000000000 : ℝ)*X 0 2+(105165767/250000000 : ℝ)*X 1 0+(1562247413/5000000000 : ℝ)*X 1 1+(5673365357/10000000000 : ℝ)*X 1 2+(105165767/250000000 : ℝ)*X 2 0+(1562247413/5000000000 : ℝ)*X 2 1+(5673365357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1919194727/10000000000 : ℝ)*X 0 0+(4805215639/10000000000 : ℝ)*X 0 1+(301785531/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((516814457/1000000000 : ℝ)*X 1 0+(-27943367/200000000 : ℝ)*X 1 1+(3017854241/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5168144487/10000000000 : ℝ)*X 2 0+(6035709989/10000000000 : ℝ)*X 2 1+(-1397166037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4217133069/10000000000 : ℝ)*X 0 0+(2803777153/5000000000 : ℝ)*X 0 1+(319260871/1000000000 : ℝ)*X 0 2+(4217133069/10000000000 : ℝ)*X 1 0+(2803777153/5000000000 : ℝ)*X 1 1+(319260871/1000000000 : ℝ)*X 1 2+(4217133069/10000000000 : ℝ)*X 2 0+(2803777153/5000000000 : ℝ)*X 2 1+(319260871/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (240784373047369261690203/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27247289/50000000000000 : ℝ)*(base1) + (238264439/20000000000000 : ℝ)*(base19) + (1109478953/100000000000000 : ℝ)*(base23) + (86445859/100000000000000 : ℝ)*(base24) + (34701151/12500000000000 : ℝ)*(upper3) + (581161232498859/100000000000000 : ℝ)*(major0) + (581161232498859/100000000000000 : ℝ)*(major1) + (581161232498859/100000000000000 : ℝ)*(major2) + (384992940411659/50000000000000 : ℝ)*(sp0) + (769987183802183/100000000000000 : ℝ)*(sp1) + (153997435839913/20000000000000 : ℝ)*(sp2) + (196165909481449/50000000000000 : ℝ)*(sp3) + (1274397819/50000000000000 : ℝ)*(sp4) + (1027946471/50000000000000 : ℝ)*(sp7) + (392333929350419/100000000000000 : ℝ)*(f.failure) + (384994187562189/50000000000000 : ℝ)*(f.sum) + (274397416545533/100000000000000000000000000000 : ℝ)*base65 + (649528387545533/200000000000000000000000000000 : ℝ)*base67 + (1414616859945533/200000000000000000000000000000 : ℝ)*base69 + (1063501500545533/200000000000000000000000000000 : ℝ)*base71 + (298975942245533/100000000000000000000000000000 : ℝ)*base73 + (187836492145533/200000000000000000000000000000 : ℝ)*base75 + (1037096522345533/200000000000000000000000000000 : ℝ)*base77 + (1062522303945533/200000000000000000000000000000 : ℝ)*base79 + (154052216845533/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (4002211/10000000000000000000000 : ℝ)*base90 + (4002211/10000000000000000000000 : ℝ)*base92 + (4002211/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (170701024386157169748663/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (730920961/50000000000000 : ℝ)*(base19) + (1603391497/100000000000000 : ℝ)*(base23) + (1224133/1250000000000 : ℝ)*(base39) + (133402829/50000000000000 : ℝ)*(base45) + (69480119/50000000000000 : ℝ)*(upper3) + (40626767/12500000000000 : ℝ)*(upper5) + (153345775392717/25000000000000 : ℝ)*(major0) + (153345775392717/25000000000000 : ℝ)*(major1) + (613383003640229/100000000000000 : ℝ)*(major2) + (218258443/25000000000000 : ℝ)*(sp2) + (812679409037653/100000000000000 : ℝ)*(sp4) + (812677947195731/100000000000000 : ℝ)*(sp5) + (50792314408939/6250000000000 : ℝ)*(sp6) + (414086468572073/100000000000000 : ℝ)*(sp7) + (414086468572073/100000000000000 : ℝ)*(f.failure) + (812679506968293/100000000000000 : ℝ)*(f.sum) + (173720928856161/200000000000000000000000000000 : ℝ)*base66 + (156832400908723/200000000000000000000000000000 : ℝ)*base67 + (267543868108779/50000000000000000000000000000 : ℝ)*base69 + (722179819491277/200000000000000000000000000000 : ℝ)*base72 + (518667834743839/200000000000000000000000000000 : ℝ)*base73 + (491598094008779/50000000000000000000000000000 : ℝ)*base75 + (287338753241221/50000000000000000000000000000 : ℝ)*base78 + (83426291891221/50000000000000000000000000000 : ℝ)*base80 + (130483640958779/25000000000000000000000000000 : ℝ)*base81 + (41565863/10000000000000000000000 : ℝ)*base89 + (41565863/10000000000000000000000 : ℝ)*base91 + (58434137/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1073_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (63/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14041/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1073_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1073_s1_0 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1061735969/5000000000 : ℝ)*x 0 + (5720365493/10000000000 : ℝ)*x 1 + (311718221/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061735969/5000000000 : ℝ)^4133 ≤ (6373357751803/50000000000000 : ℝ)^3109 := by
    have hnat : (1061735969 : ℕ)^4133*50000000000000^3109 ≤ 6373357751803^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061735969 5000000000 6373357751803 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5720365493/10000000000 : ℝ)^4133 ≤ (11897818531959/25000000000000 : ℝ)^3109 := by
    have hnat : (5720365493 : ℕ)^4133*25000000000000^3109 ≤ 11897818531959^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5720365493 10000000000 11897818531959 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (311718221/625000000 : ℝ)^4133 ≤ (4957751294081/12500000000000 : ℝ)^3109 := by
    have hnat : (311718221 : ℕ)^4133*12500000000000^3109 ≤ 4957751294081^3109*625000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311718221 625000000 4957751294081 12500000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1061735969/5000000000 : ℝ), (5720365493/10000000000 : ℝ), (311718221/625000000 : ℝ)] ![(6373357751803/50000000000000 : ℝ), (11897818531959/25000000000000 : ℝ), (4957751294081/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1061735969/5000000000 : ℝ)|^4133 ≤ (6373357751803/50000000000000 : ℝ)^3109
        have hw : |(-1061735969/5000000000 : ℝ)|=(1061735969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5720365493/10000000000 : ℝ)|^4133 ≤ (11897818531959/25000000000000 : ℝ)^3109
        have hw : |(5720365493/10000000000 : ℝ)|=(5720365493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(311718221/625000000 : ℝ)|^4133 ≤ (4957751294081/12500000000000 : ℝ)^3109
        have hw : |(311718221/625000000 : ℝ)|=(311718221/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s1_1 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5422926421/10000000000 : ℝ)*x 0 + (-2520395123/10000000000 : ℝ)*x 1 + (4987491839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5422926421/10000000000 : ℝ)^4133 ≤ (11082538451761/25000000000000 : ℝ)^3109 := by
    have hnat : (5422926421 : ℕ)^4133*25000000000000^3109 ≤ 11082538451761^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422926421 10000000000 11082538451761 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2520395123/10000000000 : ℝ)^4133 ≤ (400195815521/2500000000000 : ℝ)^3109 := by
    have hnat : (2520395123 : ℕ)^4133*2500000000000^3109 ≤ 400195815521^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2520395123 10000000000 400195815521 2500000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4987491839/10000000000 : ℝ)^4133 ≤ (39662013555817/100000000000000 : ℝ)^3109 := by
    have hnat : (4987491839 : ℕ)^4133*100000000000000^3109 ≤ 39662013555817^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4987491839 10000000000 39662013555817 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5422926421/10000000000 : ℝ), (-2520395123/10000000000 : ℝ), (4987491839/10000000000 : ℝ)] ![(11082538451761/25000000000000 : ℝ), (400195815521/2500000000000 : ℝ), (39662013555817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5422926421/10000000000 : ℝ)|^4133 ≤ (11082538451761/25000000000000 : ℝ)^3109
        have hw : |(5422926421/10000000000 : ℝ)|=(5422926421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2520395123/10000000000 : ℝ)|^4133 ≤ (400195815521/2500000000000 : ℝ)^3109
        have hw : |(-2520395123/10000000000 : ℝ)|=(2520395123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4987491839/10000000000 : ℝ)|^4133 ≤ (39662013555817/100000000000000 : ℝ)^3109
        have hw : |(4987491839/10000000000 : ℝ)|=(4987491839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s1_2 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2711463537/5000000000 : ℝ)*x 0 + (62343639/125000000 : ℝ)*x 1 + (-2520395183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711463537/5000000000 : ℝ)^4133 ≤ (11082540225801/25000000000000 : ℝ)^3109 := by
    have hnat : (2711463537 : ℕ)^4133*25000000000000^3109 ≤ 11082540225801^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711463537 5000000000 11082540225801 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62343639/125000000 : ℝ)^4133 ≤ (19831002977449/50000000000000 : ℝ)^3109 := by
    have hnat : (62343639 : ℕ)^4133*50000000000000^3109 ≤ 19831002977449^3109*125000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62343639 125000000 19831002977449 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2520395183/10000000000 : ℝ)^4133 ≤ (8003916563717/50000000000000 : ℝ)^3109 := by
    have hnat : (2520395183 : ℕ)^4133*50000000000000^3109 ≤ 8003916563717^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2520395183 10000000000 8003916563717 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711463537/5000000000 : ℝ), (62343639/125000000 : ℝ), (-2520395183/10000000000 : ℝ)] ![(11082540225801/25000000000000 : ℝ), (19831002977449/50000000000000 : ℝ), (8003916563717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711463537/5000000000 : ℝ)|^4133 ≤ (11082540225801/25000000000000 : ℝ)^3109
        have hw : |(2711463537/5000000000 : ℝ)|=(2711463537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(62343639/125000000 : ℝ)|^4133 ≤ (19831002977449/50000000000000 : ℝ)^3109
        have hw : |(62343639/125000000 : ℝ)|=(62343639/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2520395183/10000000000 : ℝ)|^4133 ≤ (8003916563717/50000000000000 : ℝ)^3109
        have hw : |(-2520395183/10000000000 : ℝ)|=(2520395183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s1_3 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4323221623/10000000000 : ℝ)*x 0 + (228993129/625000000 : ℝ)*x 1 + (1020443161/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323221623/10000000000 : ℝ)^4133 ≤ (6559711488447/20000000000000 : ℝ)^3109 := by
    have hnat : (4323221623 : ℕ)^4133*20000000000000^3109 ≤ 6559711488447^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323221623 10000000000 6559711488447 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (228993129/625000000 : ℝ)^4133 ≤ (6580512999003/25000000000000 : ℝ)^3109 := by
    have hnat : (228993129 : ℕ)^4133*25000000000000^3109 ≤ 6580512999003^3109*625000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228993129 625000000 6580512999003 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1020443161/2000000000 : ℝ)^4133 ≤ (10219847637441/25000000000000 : ℝ)^3109 := by
    have hnat : (1020443161 : ℕ)^4133*25000000000000^3109 ≤ 10219847637441^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020443161 2000000000 10219847637441 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323221623/10000000000 : ℝ), (228993129/625000000 : ℝ), (1020443161/2000000000 : ℝ)] ![(6559711488447/20000000000000 : ℝ), (6580512999003/25000000000000 : ℝ), (10219847637441/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323221623/10000000000 : ℝ)|^4133 ≤ (6559711488447/20000000000000 : ℝ)^3109
        have hw : |(4323221623/10000000000 : ℝ)|=(4323221623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(228993129/625000000 : ℝ)|^4133 ≤ (6580512999003/25000000000000 : ℝ)^3109
        have hw : |(228993129/625000000 : ℝ)|=(228993129/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1020443161/2000000000 : ℝ)|^4133 ≤ (10219847637441/25000000000000 : ℝ)^3109
        have hw : |(1020443161/2000000000 : ℝ)|=(1020443161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s1_4 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-106219161/500000000 : ℝ)*x 0 + (1249440983/2500000000 : ℝ)*x 1 + (178433831/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106219161/500000000 : ℝ)^4133 ≤ (12753987939991/100000000000000 : ℝ)^3109 := by
    have hnat : (106219161 : ℕ)^4133*100000000000000^3109 ≤ 12753987939991^3109*500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106219161 500000000 12753987939991 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1249440983/2500000000 : ℝ)^4133 ≤ (9942660489801/25000000000000 : ℝ)^3109 := by
    have hnat : (1249440983 : ℕ)^4133*25000000000000^3109 ≤ 9942660489801^3109*2500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249440983 2500000000 9942660489801 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (178433831/312500000 : ℝ)^4133 ≤ (47475370085873/100000000000000 : ℝ)^3109 := by
    have hnat : (178433831 : ℕ)^4133*100000000000000^3109 ≤ 47475370085873^3109*312500000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178433831 312500000 47475370085873 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106219161/500000000 : ℝ), (1249440983/2500000000 : ℝ), (178433831/312500000 : ℝ)] ![(12753987939991/100000000000000 : ℝ), (9942660489801/25000000000000 : ℝ), (47475370085873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106219161/500000000 : ℝ)|^4133 ≤ (12753987939991/100000000000000 : ℝ)^3109
        have hw : |(-106219161/500000000 : ℝ)|=(106219161/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1249440983/2500000000 : ℝ)|^4133 ≤ (9942660489801/25000000000000 : ℝ)^3109
        have hw : |(1249440983/2500000000 : ℝ)|=(1249440983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(178433831/312500000 : ℝ)|^4133 ≤ (47475370085873/100000000000000 : ℝ)^3109
        have hw : |(178433831/312500000 : ℝ)|=(178433831/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s1_5 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2617846491/5000000000 : ℝ)*x 0 + (-224750243/1250000000 : ℝ)*x 1 + (5709884503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2617846491/5000000000 : ℝ)^4133 ≤ (42307145000169/100000000000000 : ℝ)^3109 := by
    have hnat : (2617846491 : ℕ)^4133*100000000000000^3109 ≤ 42307145000169^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617846491 5000000000 42307145000169 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224750243/1250000000 : ℝ)^4133 ≤ (5108731888117/50000000000000 : ℝ)^3109 := by
    have hnat : (224750243 : ℕ)^4133*50000000000000^3109 ≤ 5108731888117^3109*1250000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224750243 1250000000 5108731888117 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5709884503/10000000000 : ℝ)^4133 ≤ (23737695604217/50000000000000 : ℝ)^3109 := by
    have hnat : (5709884503 : ℕ)^4133*50000000000000^3109 ≤ 23737695604217^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5709884503 10000000000 23737695604217 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2617846491/5000000000 : ℝ), (-224750243/1250000000 : ℝ), (5709884503/10000000000 : ℝ)] ![(42307145000169/100000000000000 : ℝ), (5108731888117/50000000000000 : ℝ), (23737695604217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2617846491/5000000000 : ℝ)|^4133 ≤ (42307145000169/100000000000000 : ℝ)^3109
        have hw : |(2617846491/5000000000 : ℝ)|=(2617846491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-224750243/1250000000 : ℝ)|^4133 ≤ (5108731888117/50000000000000 : ℝ)^3109
        have hw : |(-224750243/1250000000 : ℝ)|=(224750243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5709884503/10000000000 : ℝ)|^4133 ≤ (23737695604217/50000000000000 : ℝ)^3109
        have hw : |(5709884503/10000000000 : ℝ)|=(5709884503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s1_6 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2617845459/5000000000 : ℝ)*x 0 + (713735849/1250000000 : ℝ)*x 1 + (-179800153/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2617845459/5000000000 : ℝ)^4133 ≤ (4230712282873/10000000000000 : ℝ)^3109 := by
    have hnat : (2617845459 : ℕ)^4133*10000000000000^3109 ≤ 4230712282873^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617845459 5000000000 4230712282873 10000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (713735849/1250000000 : ℝ)^4133 ≤ (47475416509087/100000000000000 : ℝ)^3109 := by
    have hnat : (713735849 : ℕ)^4133*100000000000000^3109 ≤ 47475416509087^3109*1250000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713735849 1250000000 47475416509087 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179800153/1000000000 : ℝ)^4133 ≤ (10217460648729/100000000000000 : ℝ)^3109 := by
    have hnat : (179800153 : ℕ)^4133*100000000000000^3109 ≤ 10217460648729^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179800153 1000000000 10217460648729 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2617845459/5000000000 : ℝ), (713735849/1250000000 : ℝ), (-179800153/1000000000 : ℝ)] ![(4230712282873/10000000000000 : ℝ), (47475416509087/100000000000000 : ℝ), (10217460648729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2617845459/5000000000 : ℝ)|^4133 ≤ (4230712282873/10000000000000 : ℝ)^3109
        have hw : |(2617845459/5000000000 : ℝ)|=(2617845459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(713735849/1250000000 : ℝ)|^4133 ≤ (47475416509087/100000000000000 : ℝ)^3109
        have hw : |(713735849/1250000000 : ℝ)|=(713735849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-179800153/1000000000 : ℝ)|^4133 ≤ (10217460648729/100000000000000 : ℝ)^3109
        have hw : |(-179800153/1000000000 : ℝ)|=(179800153/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s1_7 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4325005743/10000000000 : ℝ)*x 0 + (5082051937/10000000000 : ℝ)*x 1 + (1842229893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325005743/10000000000 : ℝ)^4133 ≤ (6563310435817/20000000000000 : ℝ)^3109 := by
    have hnat : (4325005743 : ℕ)^4133*20000000000000^3109 ≤ 6563310435817^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325005743 10000000000 6563310435817 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5082051937/10000000000 : ℝ)^4133 ≤ (40664765145741/100000000000000 : ℝ)^3109 := by
    have hnat : (5082051937 : ℕ)^4133*100000000000000^3109 ≤ 40664765145741^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082051937 10000000000 40664765145741 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1842229893/5000000000 : ℝ)^4133 ≤ (26518682665419/100000000000000 : ℝ)^3109 := by
    have hnat : (1842229893 : ℕ)^4133*100000000000000^3109 ≤ 26518682665419^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842229893 5000000000 26518682665419 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325005743/10000000000 : ℝ), (5082051937/10000000000 : ℝ), (1842229893/5000000000 : ℝ)] ![(6563310435817/20000000000000 : ℝ), (40664765145741/100000000000000 : ℝ), (26518682665419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325005743/10000000000 : ℝ)|^4133 ≤ (6563310435817/20000000000000 : ℝ)^3109
        have hw : |(4325005743/10000000000 : ℝ)|=(4325005743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5082051937/10000000000 : ℝ)|^4133 ≤ (40664765145741/100000000000000 : ℝ)^3109
        have hw : |(5082051937/10000000000 : ℝ)|=(5082051937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1842229893/5000000000 : ℝ)|^4133 ≤ (26518682665419/100000000000000 : ℝ)^3109
        have hw : |(1842229893/5000000000 : ℝ)|=(1842229893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1073_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (63/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2627/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10379/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14041/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (63/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14041/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (63/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14041/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (63/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14041/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (63/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14041/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (63/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14041/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (63/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (63/50000 : ℝ) ^ (8265/2048 : ℝ) ≤ (49666809/25000000000000000000 : ℝ) := by
    have hpowers : (63/50000 : ℝ)^8265 ≤ (49666809/25000000000000000000 : ℝ)^2048 := by
      have hnat : (63 : ℕ)^8265*25000000000000000000^2048 ≤ 49666809^2048*50000^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63 50000 49666809 25000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63/50000 : ℝ)) (X := (49666809/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14041/50000 : ℝ) ^ (8265/2048 : ℝ) ≤ (9286918663164549/1562500000000000000 : ℝ) := by
    have hpowers : (14041/50000 : ℝ)^8265 ≤ (9286918663164549/1562500000000000000 : ℝ)^2048 := by
      have hnat : (14041 : ℕ)^8265*1562500000000000000^2048 ≤ 9286918663164549^2048*50000^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14041 50000 9286918663164549 1562500000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14041/50000 : ℝ)) (X := (9286918663164549/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000000049666809/12500000000000000000 : ℝ) ≤ (5000000000004923/5000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (12500000000049666809/12500000000000000000 : ℝ)^2048 ≤ (5000000000004923/5000000000000000 : ℝ)^8265 := by
      have hnat : (12500000000049666809 : ℕ)^2048*5000000000000000^8265 ≤ 5000000000004923^8265*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000000049666809 12500000000000000000 5000000000004923 5000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000004923/5000000000000000 : ℝ)) (X := (12500000000049666809/12500000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25148590698660299593/25000000000000000000 : ℝ) ≤ (156479609674053/156250000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (25148590698660299593/25000000000000000000 : ℝ)^2048 ≤ (156479609674053/156250000000000 : ℝ)^8265 := by
      have hnat : (25148590698660299593 : ℕ)^2048*156250000000000^8265 ≤ 156479609674053^8265*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25148590698660299593 25000000000000000000 156479609674053 156250000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156479609674053/156250000000000 : ℝ)) (X := (25148590698660299593/25000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (790536918663164549/781250000000000000 : ℝ) ≤ (5014695019134469/5000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (790536918663164549/781250000000000000 : ℝ)^2048 ≤ (5014695019134469/5000000000000000 : ℝ)^8265 := by
      have hnat : (790536918663164549 : ℕ)^2048*5000000000000000^8265 ≤ 5014695019134469^8265*781250000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        790536918663164549 781250000000000000 5014695019134469 5000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014695019134469/5000000000000000 : ℝ)) (X := (790536918663164549/781250000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(49666809/25000000000000000000 : ℝ) ≤ ((8736134276732956537/8736250000000000000 : ℝ)+2*(7347509564773/1397800000000000 : ℝ)*(63/50000 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (8736134276732956537/8736250000000000000 : ℝ)+2*(7347509564773/1397800000000000 : ℝ)*(63/50000 : ℝ)=(5000000000004923/5000000000000000 : ℝ) by norm_num, show 1+2*(49666809/25000000000000000000 : ℝ)=(12500000000049666809/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9286918663164549/1562500000000000000 : ℝ)+(49666809/25000000000000000000 : ℝ) ≤ ((8736134276732956537/8736250000000000000 : ℝ)+(7347509564773/1397800000000000 : ℝ)*((14041/50000 : ℝ)+(63/50000 : ℝ)))^(8265/2048 : ℝ) := by
    rw [show (8736134276732956537/8736250000000000000 : ℝ)+(7347509564773/1397800000000000 : ℝ)*((14041/50000 : ℝ)+(63/50000 : ℝ))=(156479609674053/156250000000000 : ℝ) by norm_num, show 1+(9286918663164549/1562500000000000000 : ℝ)+(49666809/25000000000000000000 : ℝ)=(25148590698660299593/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9286918663164549/1562500000000000000 : ℝ) ≤ ((8736134276732956537/8736250000000000000 : ℝ)+2*(7347509564773/1397800000000000 : ℝ)*(14041/50000 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (8736134276732956537/8736250000000000000 : ℝ)+2*(7347509564773/1397800000000000 : ℝ)*(14041/50000 : ℝ)=(5014695019134469/5000000000000000 : ℝ) by norm_num, show 1+2*(9286918663164549/1562500000000000000 : ℝ)=(790536918663164549/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8736134276732956537/8736250000000000000 : ℝ)*(X 1 0+X 2 0)+(7347509564773/1397800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (63/50000 : ℝ)) (hi := (14041/50000 : ℝ)) (c := (8736134276732956537/8736250000000000000 : ℝ)) (alpha := (7347509564773/1397800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8736134276732956537/8736250000000000000 : ℝ)*(X 0 1+X 2 1)+(7347509564773/1397800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (63/50000 : ℝ)) (hi := (14041/50000 : ℝ)) (c := (8736134276732956537/8736250000000000000 : ℝ)) (alpha := (7347509564773/1397800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8736134276732956537/8736250000000000000 : ℝ)*(X 0 2+X 1 2)+(7347509564773/1397800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (63/50000 : ℝ)) (hi := (14041/50000 : ℝ)) (c := (8736134276732956537/8736250000000000000 : ℝ)) (alpha := (7347509564773/1397800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1061735969/5000000000 : ℝ)*X 0 0+(5720365493/10000000000 : ℝ)*X 0 1+(311718221/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5422926421/10000000000 : ℝ)*X 1 0+(-2520395123/10000000000 : ℝ)*X 1 1+(4987491839/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2711463537/5000000000 : ℝ)*X 2 0+(62343639/125000000 : ℝ)*X 2 1+(-2520395183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4323221623/10000000000 : ℝ)*X 0 0+(228993129/625000000 : ℝ)*X 0 1+(1020443161/2000000000 : ℝ)*X 0 2+(4323221623/10000000000 : ℝ)*X 1 0+(228993129/625000000 : ℝ)*X 1 1+(1020443161/2000000000 : ℝ)*X 1 2+(4323221623/10000000000 : ℝ)*X 2 0+(228993129/625000000 : ℝ)*X 2 1+(1020443161/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-106219161/500000000 : ℝ)*X 0 0+(1249440983/2500000000 : ℝ)*X 0 1+(178433831/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2617846491/5000000000 : ℝ)*X 1 0+(-224750243/1250000000 : ℝ)*X 1 1+(5709884503/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2617845459/5000000000 : ℝ)*X 2 0+(713735849/1250000000 : ℝ)*X 2 1+(-179800153/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4325005743/10000000000 : ℝ)*X 0 0+(5082051937/10000000000 : ℝ)*X 0 1+(1842229893/5000000000 : ℝ)*X 0 2+(4325005743/10000000000 : ℝ)*X 1 0+(5082051937/10000000000 : ℝ)*X 1 1+(1842229893/5000000000 : ℝ)*X 1 2+(4325005743/10000000000 : ℝ)*X 2 0+(5082051937/10000000000 : ℝ)*X 2 1+(1842229893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2987877647541658886922653337/436812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67131053/50000000000000 : ℝ)*(base1) + (730014463/50000000000000 : ℝ)*(base19) + (162433527/10000000000000 : ℝ)*(base23) + (143616029/100000000000000 : ℝ)*(upper3) + (167915239/100000000000000 : ℝ)*(upper5) + (1029882862217033/100000000000000 : ℝ)*(major0) + (1029882862217033/100000000000000 : ℝ)*(major1) + (1029882862217033/100000000000000 : ℝ)*(major2) + (682249066175031/50000000000000 : ℝ)*(sp0) + (341126081542169/25000000000000 : ℝ)*(sp1) + (1364504161862331/100000000000000 : ℝ)*(sp2) + (69525610829153/10000000000000 : ℝ)*(sp3) + (3894054823/50000000000000 : ℝ)*(sp4) + (693535341/20000000000000 : ℝ)*(sp7) + (695259710230341/100000000000000 : ℝ)*(f.failure) + (682252893098801/50000000000000 : ℝ)*(f.sum) + (48000346981301/69890000000000000000000000000 : ℝ)*base66 + (4084702551837400971/873625000000000000000000000000000 : ℝ)*base67 + (4556488574873724029/873625000000000000000000000000000 : ℝ)*base70 + (347182390967150971/873625000000000000000000000000000 : ℝ)*base71 + (224036090407779/69890000000000000000000000000 : ℝ)*base73 + (5771419205811224029/873625000000000000000000000000000 : ℝ)*base76 + (1869333388951900971/873625000000000000000000000000000 : ℝ)*base77 + (4413445820450150971/873625000000000000000000000000000 : ℝ)*base79 + (259738774938721/69890000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (54802229/10000000000000000000000 : ℝ)*base90 + (54802229/10000000000000000000000 : ℝ)*base92 + (54802229/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (449823977753254182512691189/109203125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2852997599/100000000000000 : ℝ)*(base19) + (2816524039/100000000000000 : ℝ)*(base23) + (121298429/50000000000000 : ℝ)*(upper2) + (465857743/100000000000000 : ℝ)*(upper3) + (283044421/50000000000000 : ℝ)*(upper5) + (66242947733827/6250000000000 : ℝ)*(major0) + (66242947733827/6250000000000 : ℝ)*(major1) + (66242947733827/6250000000000 : ℝ)*(major2) + (1420923997/10000000000000 : ℝ)*(sp1) + (15712225273/100000000000000 : ℝ)*(sp2) + (1404258989979597/100000000000000 : ℝ)*(sp4) + (351060481935507/25000000000000 : ℝ)*(sp5) + (702120230615143/50000000000000 : ℝ)*(sp6) + (357757600098941/50000000000000 : ℝ)*(sp7) + (357757600098941/50000000000000 : ℝ)*(f.failure) + (1404258989979597/100000000000000 : ℝ)*(f.sum) + (14412758984699/17472500000000000000000000000 : ℝ)*base65 + (139335410331244263/27300781250000000000000000000000 : ℝ)*base68 + (548225403098285401/54601562500000000000000000000000 : ℝ)*base70 + (243673313288316651/54601562500000000000000000000000 : ℝ)*base72 + (17473131057943/8736250000000000000000000000 : ℝ)*base74 + (188964881602306763/27300781250000000000000000000000 : ℝ)*base76 + (380569743837347901/54601562500000000000000000000000 : ℝ)*base78 + (62894440981079361/3412597656250000000000000000000 : ℝ)*base80 + (72644338880617/34945000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (54244371/5000000000000000000000 : ℝ)*base89 + (54244371/5000000000000000000000 : ℝ)*base91 + (54244371/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1073_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (63/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2627/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10379/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1073_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1073_s2_0 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1090249067/5000000000 : ℝ)*x 0 + (690558937/1250000000 : ℝ)*x 1 + (5147197749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090249067/5000000000 : ℝ)^4133 ≤ (13203778405761/100000000000000 : ℝ)^3109 := by
    have hnat : (1090249067 : ℕ)^4133*100000000000000^3109 ≤ 13203778405761^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090249067 5000000000 13203778405761 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (690558937/1250000000 : ℝ)^4133 ≤ (22718517118333/50000000000000 : ℝ)^3109 := by
    have hnat : (690558937 : ℕ)^4133*50000000000000^3109 ≤ 22718517118333^3109*1250000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690558937 1250000000 22718517118333 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5147197749/10000000000 : ℝ)^4133 ≤ (41359187341233/100000000000000 : ℝ)^3109 := by
    have hnat : (5147197749 : ℕ)^4133*100000000000000^3109 ≤ 41359187341233^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5147197749 10000000000 41359187341233 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1090249067/5000000000 : ℝ), (690558937/1250000000 : ℝ), (5147197749/10000000000 : ℝ)] ![(13203778405761/100000000000000 : ℝ), (22718517118333/50000000000000 : ℝ), (41359187341233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1090249067/5000000000 : ℝ)|^4133 ≤ (13203778405761/100000000000000 : ℝ)^3109
        have hw : |(-1090249067/5000000000 : ℝ)|=(1090249067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(690558937/1250000000 : ℝ)|^4133 ≤ (22718517118333/50000000000000 : ℝ)^3109
        have hw : |(690558937/1250000000 : ℝ)|=(690558937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5147197749/10000000000 : ℝ)|^4133 ≤ (41359187341233/100000000000000 : ℝ)^3109
        have hw : |(5147197749/10000000000 : ℝ)|=(5147197749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s2_1 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (43015151/80000000 : ℝ)*x 0 + (-2377190547/10000000000 : ℝ)*x 1 + (1029439739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43015151/80000000 : ℝ)^4133 ≤ (21915309062011/50000000000000 : ℝ)^3109 := by
    have hnat : (43015151 : ℕ)^4133*50000000000000^3109 ≤ 21915309062011^3109*80000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43015151 80000000 21915309062011 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2377190547/10000000000 : ℝ)^4133 ≤ (7405092206409/50000000000000 : ℝ)^3109 := by
    have hnat : (2377190547 : ℕ)^4133*50000000000000^3109 ≤ 7405092206409^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2377190547 10000000000 7405092206409 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029439739/2000000000 : ℝ)^4133 ≤ (41359197446249/100000000000000 : ℝ)^3109 := by
    have hnat : (1029439739 : ℕ)^4133*100000000000000^3109 ≤ 41359197446249^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029439739 2000000000 41359197446249 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43015151/80000000 : ℝ), (-2377190547/10000000000 : ℝ), (1029439739/2000000000 : ℝ)] ![(21915309062011/50000000000000 : ℝ), (7405092206409/50000000000000 : ℝ), (41359197446249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43015151/80000000 : ℝ)|^4133 ≤ (21915309062011/50000000000000 : ℝ)^3109
        have hw : |(43015151/80000000 : ℝ)|=(43015151/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2377190547/10000000000 : ℝ)|^4133 ≤ (7405092206409/50000000000000 : ℝ)^3109
        have hw : |(-2377190547/10000000000 : ℝ)|=(2377190547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1029439739/2000000000 : ℝ)|^4133 ≤ (41359197446249/100000000000000 : ℝ)^3109
        have hw : |(1029439739/2000000000 : ℝ)|=(1029439739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s2_2 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134422333/250000000 : ℝ)*x 0 + (1029439857/2000000000 : ℝ)*x 1 + (-148574407/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134422333/250000000 : ℝ)^4133 ≤ (2191530605487/5000000000000 : ℝ)^3109 := by
    have hnat : (134422333 : ℕ)^4133*5000000000000^3109 ≤ 2191530605487^3109*250000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134422333 250000000 2191530605487 5000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029439857/2000000000 : ℝ)^4133 ≤ (41359203748531/100000000000000 : ℝ)^3109 := by
    have hnat : (1029439857 : ℕ)^4133*100000000000000^3109 ≤ 41359203748531^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029439857 2000000000 41359203748531 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (148574407/625000000 : ℝ)^4133 ≤ (231409126921/1562500000000 : ℝ)^3109 := by
    have hnat : (148574407 : ℕ)^4133*1562500000000^3109 ≤ 231409126921^3109*625000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148574407 625000000 231409126921 1562500000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134422333/250000000 : ℝ), (1029439857/2000000000 : ℝ), (-148574407/625000000 : ℝ)] ![(2191530605487/5000000000000 : ℝ), (41359203748531/100000000000000 : ℝ), (231409126921/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134422333/250000000 : ℝ)|^4133 ≤ (2191530605487/5000000000000 : ℝ)^3109
        have hw : |(134422333/250000000 : ℝ)|=(134422333/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1029439857/2000000000 : ℝ)|^4133 ≤ (41359203748531/100000000000000 : ℝ)^3109
        have hw : |(1029439857/2000000000 : ℝ)|=(1029439857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-148574407/625000000 : ℝ)|^4133 ≤ (231409126921/1562500000000 : ℝ)^3109
        have hw : |(-148574407/625000000 : ℝ)|=(148574407/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s2_3 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2181078559/5000000000 : ℝ)*x 0 + (4007758559/10000000000 : ℝ)*x 1 + (474817779/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181078559/5000000000 : ℝ)^4133 ≤ (33191817634397/100000000000000 : ℝ)^3109 := by
    have hnat : (2181078559 : ℕ)^4133*100000000000000^3109 ≤ 33191817634397^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181078559 5000000000 33191817634397 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4007758559/10000000000 : ℝ)^4133 ≤ (14827935401821/50000000000000 : ℝ)^3109 := by
    have hnat : (4007758559 : ℕ)^4133*50000000000000^3109 ≤ 14827935401821^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4007758559 10000000000 14827935401821 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (474817779/1000000000 : ℝ)^4133 ≤ (37152311545407/100000000000000 : ℝ)^3109 := by
    have hnat : (474817779 : ℕ)^4133*100000000000000^3109 ≤ 37152311545407^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474817779 1000000000 37152311545407 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181078559/5000000000 : ℝ), (4007758559/10000000000 : ℝ), (474817779/1000000000 : ℝ)] ![(33191817634397/100000000000000 : ℝ), (14827935401821/50000000000000 : ℝ), (37152311545407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181078559/5000000000 : ℝ)|^4133 ≤ (33191817634397/100000000000000 : ℝ)^3109
        have hw : |(2181078559/5000000000 : ℝ)|=(2181078559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4007758559/10000000000 : ℝ)|^4133 ≤ (14827935401821/50000000000000 : ℝ)^3109
        have hw : |(4007758559/10000000000 : ℝ)|=(4007758559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(474817779/1000000000 : ℝ)|^4133 ≤ (37152311545407/100000000000000 : ℝ)^3109
        have hw : |(474817779/1000000000 : ℝ)|=(474817779/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s2_4 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2180621353/10000000000 : ℝ)*x 0 + (5149930859/10000000000 : ℝ)*x 1 + (86276721/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180621353/10000000000 : ℝ)^4133 ≤ (805955219/6103515625 : ℝ)^3109 := by
    have hnat : (2180621353 : ℕ)^4133*6103515625^3109 ≤ 805955219^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180621353 10000000000 805955219 6103515625 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5149930859/10000000000 : ℝ)^4133 ≤ (8277676904261/20000000000000 : ℝ)^3109 := by
    have hnat : (5149930859 : ℕ)^4133*20000000000000^3109 ≤ 8277676904261^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149930859 10000000000 8277676904261 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86276721/156250000 : ℝ)^4133 ≤ (5675855644053/12500000000000 : ℝ)^3109 := by
    have hnat : (86276721 : ℕ)^4133*12500000000000^3109 ≤ 5675855644053^3109*156250000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86276721 156250000 5675855644053 12500000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2180621353/10000000000 : ℝ), (5149930859/10000000000 : ℝ), (86276721/156250000 : ℝ)] ![(805955219/6103515625 : ℝ), (8277676904261/20000000000000 : ℝ), (5675855644053/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2180621353/10000000000 : ℝ)|^4133 ≤ (805955219/6103515625 : ℝ)^3109
        have hw : |(-2180621353/10000000000 : ℝ)|=(2180621353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5149930859/10000000000 : ℝ)|^4133 ≤ (8277676904261/20000000000000 : ℝ)^3109
        have hw : |(5149930859/10000000000 : ℝ)|=(5149930859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(86276721/156250000 : ℝ)|^4133 ≤ (5675855644053/12500000000000 : ℝ)^3109
        have hw : |(86276721/156250000 : ℝ)|=(86276721/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s2_5 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5281618293/10000000000 : ℝ)*x 0 + (-1001340731/5000000000 : ℝ)*x 1 + (2760855117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5281618293/10000000000 : ℝ)^4133 ≤ (42801184885273/100000000000000 : ℝ)^3109 := by
    have hnat : (5281618293 : ℕ)^4133*100000000000000^3109 ≤ 42801184885273^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281618293 10000000000 42801184885273 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001340731/5000000000 : ℝ)^4133 ≤ (11791968952169/100000000000000 : ℝ)^3109 := by
    have hnat : (1001340731 : ℕ)^4133*100000000000000^3109 ≤ 11791968952169^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001340731 5000000000 11791968952169 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2760855117/5000000000 : ℝ)^4133 ≤ (1418963941759/3125000000000 : ℝ)^3109 := by
    have hnat : (2760855117 : ℕ)^4133*3125000000000^3109 ≤ 1418963941759^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760855117 5000000000 1418963941759 3125000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5281618293/10000000000 : ℝ), (-1001340731/5000000000 : ℝ), (2760855117/5000000000 : ℝ)] ![(42801184885273/100000000000000 : ℝ), (11791968952169/100000000000000 : ℝ), (1418963941759/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5281618293/10000000000 : ℝ)|^4133 ≤ (42801184885273/100000000000000 : ℝ)^3109
        have hw : |(5281618293/10000000000 : ℝ)|=(5281618293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1001340731/5000000000 : ℝ)|^4133 ≤ (11791968952169/100000000000000 : ℝ)^3109
        have hw : |(-1001340731/5000000000 : ℝ)|=(1001340731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2760855117/5000000000 : ℝ)|^4133 ≤ (1418963941759/3125000000000 : ℝ)^3109
        have hw : |(2760855117/5000000000 : ℝ)|=(2760855117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s2_6 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5281618537/10000000000 : ℝ)*x 0 + (2760855037/5000000000 : ℝ)*x 1 + (-250335169/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5281618537/10000000000 : ℝ)^4133 ≤ (8560237502773/20000000000000 : ℝ)^3109 := by
    have hnat : (5281618537 : ℕ)^4133*20000000000000^3109 ≤ 8560237502773^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281618537 10000000000 8560237502773 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2760855037/5000000000 : ℝ)^4133 ≤ (45406844387197/100000000000000 : ℝ)^3109 := by
    have hnat : (2760855037 : ℕ)^4133*100000000000000^3109 ≤ 45406844387197^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760855037 5000000000 45406844387197 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250335169/1250000000 : ℝ)^4133 ≤ (11791968091151/100000000000000 : ℝ)^3109 := by
    have hnat : (250335169 : ℕ)^4133*100000000000000^3109 ≤ 11791968091151^3109*1250000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250335169 1250000000 11791968091151 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5281618537/10000000000 : ℝ), (2760855037/5000000000 : ℝ), (-250335169/1250000000 : ℝ)] ![(8560237502773/20000000000000 : ℝ), (45406844387197/100000000000000 : ℝ), (11791968091151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5281618537/10000000000 : ℝ)|^4133 ≤ (8560237502773/20000000000000 : ℝ)^3109
        have hw : |(5281618537/10000000000 : ℝ)|=(5281618537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2760855037/5000000000 : ℝ)|^4133 ≤ (45406844387197/100000000000000 : ℝ)^3109
        have hw : |(2760855037/5000000000 : ℝ)|=(2760855037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-250335169/1250000000 : ℝ)|^4133 ≤ (11791968091151/100000000000000 : ℝ)^3109
        have hw : |(-250335169/1250000000 : ℝ)|=(250335169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s2_7 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (872479207/2000000000 : ℝ)*x 0 + (474282231/1000000000 : ℝ)*x 1 + (4013173643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872479207/2000000000 : ℝ)^4133 ≤ (33194234349103/100000000000000 : ℝ)^3109 := by
    have hnat : (872479207 : ℕ)^4133*100000000000000^3109 ≤ 33194234349103^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872479207 2000000000 33194234349103 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (474282231/1000000000 : ℝ)^4133 ≤ (37096615898051/100000000000000 : ℝ)^3109 := by
    have hnat : (474282231 : ℕ)^4133*100000000000000^3109 ≤ 37096615898051^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474282231 1000000000 37096615898051 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4013173643/10000000000 : ℝ)^4133 ≤ (5941829949507/20000000000000 : ℝ)^3109 := by
    have hnat : (4013173643 : ℕ)^4133*20000000000000^3109 ≤ 5941829949507^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4013173643 10000000000 5941829949507 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872479207/2000000000 : ℝ), (474282231/1000000000 : ℝ), (4013173643/10000000000 : ℝ)] ![(33194234349103/100000000000000 : ℝ), (37096615898051/100000000000000 : ℝ), (5941829949507/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872479207/2000000000 : ℝ)|^4133 ≤ (33194234349103/100000000000000 : ℝ)^3109
        have hw : |(872479207/2000000000 : ℝ)|=(872479207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(474282231/1000000000 : ℝ)|^4133 ≤ (37096615898051/100000000000000 : ℝ)^3109
        have hw : |(474282231/1000000000 : ℝ)|=(474282231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4013173643/10000000000 : ℝ)|^4133 ≤ (5941829949507/20000000000000 : ℝ)^3109
        have hw : |(4013173643/10000000000 : ℝ)|=(4013173643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s2_8 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-100182813/10000000000 : ℝ)*x 0 + (2963543373/5000000000 : ℝ)*x 1 + (5926899523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100182813/10000000000 : ℝ)^4133 ≤ (43989777643/20000000000000 : ℝ)^3109 := by
    have hnat : (100182813 : ℕ)^4133*20000000000000^3109 ≤ 43989777643^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100182813 10000000000 43989777643 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2963543373/5000000000 : ℝ)^4133 ≤ (49891073046667/100000000000000 : ℝ)^3109 := by
    have hnat : (2963543373 : ℕ)^4133*100000000000000^3109 ≤ 49891073046667^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2963543373 5000000000 49891073046667 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5926899523/10000000000 : ℝ)^4133 ≤ (6236122256341/12500000000000 : ℝ)^3109 := by
    have hnat : (5926899523 : ℕ)^4133*12500000000000^3109 ≤ 6236122256341^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5926899523 10000000000 6236122256341 12500000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-100182813/10000000000 : ℝ), (2963543373/5000000000 : ℝ), (5926899523/10000000000 : ℝ)] ![(43989777643/20000000000000 : ℝ), (49891073046667/100000000000000 : ℝ), (6236122256341/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-100182813/10000000000 : ℝ)|^4133 ≤ (43989777643/20000000000000 : ℝ)^3109
        have hw : |(-100182813/10000000000 : ℝ)|=(100182813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2963543373/5000000000 : ℝ)|^4133 ≤ (49891073046667/100000000000000 : ℝ)^3109
        have hw : |(2963543373/5000000000 : ℝ)|=(2963543373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5926899523/10000000000 : ℝ)|^4133 ≤ (6236122256341/12500000000000 : ℝ)^3109
        have hw : |(5926899523/10000000000 : ℝ)|=(5926899523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s2_9 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (795911989/10000000000 : ℝ)*x 0 + (-2482862729/5000000000 : ℝ)*x 1 + (6561274213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (795911989/10000000000 : ℝ)^4133 ≤ (345817504553/10000000000000 : ℝ)^3109 := by
    have hnat : (795911989 : ℕ)^4133*10000000000000^3109 ≤ 345817504553^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795911989 10000000000 345817504553 10000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2482862729/5000000000 : ℝ)^4133 ≤ (19716037732353/50000000000000 : ℝ)^3109 := by
    have hnat : (2482862729 : ℕ)^4133*50000000000000^3109 ≤ 19716037732353^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2482862729 5000000000 19716037732353 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6561274213/10000000000 : ℝ)^4133 ≤ (7138718684167/12500000000000 : ℝ)^3109 := by
    have hnat : (6561274213 : ℕ)^4133*12500000000000^3109 ≤ 7138718684167^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6561274213 10000000000 7138718684167 12500000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(795911989/10000000000 : ℝ), (-2482862729/5000000000 : ℝ), (6561274213/10000000000 : ℝ)] ![(345817504553/10000000000000 : ℝ), (19716037732353/50000000000000 : ℝ), (7138718684167/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(795911989/10000000000 : ℝ)|^4133 ≤ (345817504553/10000000000000 : ℝ)^3109
        have hw : |(795911989/10000000000 : ℝ)|=(795911989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2482862729/5000000000 : ℝ)|^4133 ≤ (19716037732353/50000000000000 : ℝ)^3109
        have hw : |(-2482862729/5000000000 : ℝ)|=(2482862729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6561274213/10000000000 : ℝ)|^4133 ≤ (7138718684167/12500000000000 : ℝ)^3109
        have hw : |(6561274213/10000000000 : ℝ)|=(6561274213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s2_10 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (79454633/1000000000 : ℝ)*x 0 + (6557759931/10000000000 : ℝ)*x 1 + (-497032349/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79454633/1000000000 : ℝ)^4133 ≤ (215643077461/6250000000000 : ℝ)^3109 := by
    have hnat : (79454633 : ℕ)^4133*6250000000000^3109 ≤ 215643077461^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79454633 1000000000 215643077461 6250000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6557759931/10000000000 : ℝ)^4133 ≤ (1426727242287/2500000000000 : ℝ)^3109 := by
    have hnat : (6557759931 : ℕ)^4133*2500000000000^3109 ≤ 1426727242287^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6557759931 10000000000 1426727242287 2500000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497032349/1000000000 : ℝ)^4133 ≤ (39480621057701/100000000000000 : ℝ)^3109 := by
    have hnat : (497032349 : ℕ)^4133*100000000000000^3109 ≤ 39480621057701^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497032349 1000000000 39480621057701 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(79454633/1000000000 : ℝ), (6557759931/10000000000 : ℝ), (-497032349/1000000000 : ℝ)] ![(215643077461/6250000000000 : ℝ), (1426727242287/2500000000000 : ℝ), (39480621057701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(79454633/1000000000 : ℝ)|^4133 ≤ (215643077461/6250000000000 : ℝ)^3109
        have hw : |(79454633/1000000000 : ℝ)|=(79454633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6557759931/10000000000 : ℝ)|^4133 ≤ (1426727242287/2500000000000 : ℝ)^3109
        have hw : |(6557759931/10000000000 : ℝ)|=(6557759931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-497032349/1000000000 : ℝ)|^4133 ≤ (39480621057701/100000000000000 : ℝ)^3109
        have hw : |(-497032349/1000000000 : ℝ)|=(497032349/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s2_11 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10490887/250000000 : ℝ)*x 0 + (2934405723/5000000000 : ℝ)*x 1 + (2936343281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10490887/250000000 : ℝ)^4133 ≤ (147670122711/10000000000000 : ℝ)^3109 := by
    have hnat : (10490887 : ℕ)^4133*10000000000000^3109 ≤ 147670122711^3109*250000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10490887 250000000 147670122711 10000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2934405723/5000000000 : ℝ)^4133 ≤ (24620018195543/50000000000000 : ℝ)^3109 := by
    have hnat : (2934405723 : ℕ)^4133*50000000000000^3109 ≤ 24620018195543^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2934405723 5000000000 24620018195543 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2936343281/5000000000 : ℝ)^4133 ≤ (24641631183857/50000000000000 : ℝ)^3109 := by
    have hnat : (2936343281 : ℕ)^4133*50000000000000^3109 ≤ 24641631183857^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2936343281 5000000000 24641631183857 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10490887/250000000 : ℝ), (2934405723/5000000000 : ℝ), (2936343281/5000000000 : ℝ)] ![(147670122711/10000000000000 : ℝ), (24620018195543/50000000000000 : ℝ), (24641631183857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10490887/250000000 : ℝ)|^4133 ≤ (147670122711/10000000000000 : ℝ)^3109
        have hw : |(10490887/250000000 : ℝ)|=(10490887/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2934405723/5000000000 : ℝ)|^4133 ≤ (24620018195543/50000000000000 : ℝ)^3109
        have hw : |(2934405723/5000000000 : ℝ)|=(2934405723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2936343281/5000000000 : ℝ)|^4133 ≤ (24641631183857/50000000000000 : ℝ)^3109
        have hw : |(2936343281/5000000000 : ℝ)|=(2936343281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1073_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2627/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4373/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8359/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2627/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2627/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2627/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2627/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2627/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2627/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2627/50000 : ℝ) ^ (8265/2048 : ℝ) ≤ (686045218916271/100000000000000000000 : ℝ) := by
    have hpowers : (2627/50000 : ℝ)^8265 ≤ (686045218916271/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2627 : ℕ)^8265*100000000000000000000^2048 ≤ 686045218916271^2048*50000^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2627 50000 686045218916271 100000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2627/50000 : ℝ)) (X := (686045218916271/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10379/50000 : ℝ) ^ (8265/2048 : ℝ) ≤ (175551048606807199/100000000000000000000 : ℝ) := by
    have hpowers : (10379/50000 : ℝ)^8265 ≤ (175551048606807199/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10379 : ℕ)^8265*100000000000000000000^2048 ≤ 175551048606807199^2048*50000^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10379 50000 175551048606807199 100000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10379/50000 : ℝ)) (X := (175551048606807199/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000686045218916271/50000000000000000000 : ℝ) ≤ (10000033999113317/10000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (50000686045218916271/50000000000000000000 : ℝ)^2048 ≤ (10000033999113317/10000000000000000 : ℝ)^8265 := by
      have hnat : (50000686045218916271 : ℕ)^2048*10000000000000000^8265 ≤ 10000033999113317^8265*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000686045218916271 50000000000000000000 10000033999113317 10000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000033999113317/10000000000000000 : ℝ)) (X := (50000686045218916271/50000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10017623709382572347/10000000000000000000 : ℝ) ≤ (5002182060343427/5000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (10017623709382572347/10000000000000000000 : ℝ)^2048 ≤ (5002182060343427/5000000000000000 : ℝ)^8265 := by
      have hnat : (10017623709382572347 : ℕ)^2048*5000000000000000^8265 ≤ 5002182060343427^8265*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10017623709382572347 10000000000000000000 5002182060343427 5000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002182060343427/5000000000000000 : ℝ)) (X := (10017623709382572347/10000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50175551048606807199/50000000000000000000 : ℝ) ≤ (10008694242260391/10000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (50175551048606807199/50000000000000000000 : ℝ)^2048 ≤ (10008694242260391/10000000000000000 : ℝ)^8265 := by
      have hnat : (50175551048606807199 : ℕ)^2048*10000000000000000^8265 ≤ 10008694242260391^8265*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50175551048606807199 50000000000000000000 10008694242260391 10000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008694242260391/10000000000000000 : ℝ)) (X := (50175551048606807199/50000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(686045218916271/100000000000000000000 : ℝ) ≤ ((38748756551189534993/38760000000000000000 : ℝ)+2*(4330121573537/1550400000000000 : ℝ)*(2627/50000 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (38748756551189534993/38760000000000000000 : ℝ)+2*(4330121573537/1550400000000000 : ℝ)*(2627/50000 : ℝ)=(10000033999113317/10000000000000000 : ℝ) by norm_num, show 1+2*(686045218916271/100000000000000000000 : ℝ)=(50000686045218916271/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(175551048606807199/100000000000000000000 : ℝ)+(686045218916271/100000000000000000000 : ℝ) ≤ ((38748756551189534993/38760000000000000000 : ℝ)+(4330121573537/1550400000000000 : ℝ)*((10379/50000 : ℝ)+(2627/50000 : ℝ)))^(8265/2048 : ℝ) := by
    rw [show (38748756551189534993/38760000000000000000 : ℝ)+(4330121573537/1550400000000000 : ℝ)*((10379/50000 : ℝ)+(2627/50000 : ℝ))=(5002182060343427/5000000000000000 : ℝ) by norm_num, show 1+(175551048606807199/100000000000000000000 : ℝ)+(686045218916271/100000000000000000000 : ℝ)=(10017623709382572347/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(175551048606807199/100000000000000000000 : ℝ) ≤ ((38748756551189534993/38760000000000000000 : ℝ)+2*(4330121573537/1550400000000000 : ℝ)*(10379/50000 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (38748756551189534993/38760000000000000000 : ℝ)+2*(4330121573537/1550400000000000 : ℝ)*(10379/50000 : ℝ)=(10008694242260391/10000000000000000 : ℝ) by norm_num, show 1+2*(175551048606807199/100000000000000000000 : ℝ)=(50175551048606807199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38748756551189534993/38760000000000000000 : ℝ)*(X 1 0+X 2 0)+(4330121573537/1550400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (2627/50000 : ℝ)) (hi := (10379/50000 : ℝ)) (c := (38748756551189534993/38760000000000000000 : ℝ)) (alpha := (4330121573537/1550400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38748756551189534993/38760000000000000000 : ℝ)*(X 0 1+X 2 1)+(4330121573537/1550400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (2627/50000 : ℝ)) (hi := (10379/50000 : ℝ)) (c := (38748756551189534993/38760000000000000000 : ℝ)) (alpha := (4330121573537/1550400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38748756551189534993/38760000000000000000 : ℝ)*(X 0 2+X 1 2)+(4330121573537/1550400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (2627/50000 : ℝ)) (hi := (10379/50000 : ℝ)) (c := (38748756551189534993/38760000000000000000 : ℝ)) (alpha := (4330121573537/1550400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1090249067/5000000000 : ℝ)*X 0 0+(690558937/1250000000 : ℝ)*X 0 1+(5147197749/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((43015151/80000000 : ℝ)*X 1 0+(-2377190547/10000000000 : ℝ)*X 1 1+(1029439739/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((134422333/250000000 : ℝ)*X 2 0+(1029439857/2000000000 : ℝ)*X 2 1+(-148574407/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2181078559/5000000000 : ℝ)*X 0 0+(4007758559/10000000000 : ℝ)*X 0 1+(474817779/1000000000 : ℝ)*X 0 2+(2181078559/5000000000 : ℝ)*X 1 0+(4007758559/10000000000 : ℝ)*X 1 1+(474817779/1000000000 : ℝ)*X 1 2+(2181078559/5000000000 : ℝ)*X 2 0+(4007758559/10000000000 : ℝ)*X 2 1+(474817779/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2180621353/10000000000 : ℝ)*X 0 0+(5149930859/10000000000 : ℝ)*X 0 1+(86276721/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5281618293/10000000000 : ℝ)*X 1 0+(-1001340731/5000000000 : ℝ)*X 1 1+(2760855117/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5281618537/10000000000 : ℝ)*X 2 0+(2760855037/5000000000 : ℝ)*X 2 1+(-250335169/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872479207/2000000000 : ℝ)*X 0 0+(474282231/1000000000 : ℝ)*X 0 1+(4013173643/10000000000 : ℝ)*X 0 2+(872479207/2000000000 : ℝ)*X 1 0+(474282231/1000000000 : ℝ)*X 1 1+(4013173643/10000000000 : ℝ)*X 1 2+(872479207/2000000000 : ℝ)*X 2 0+(474282231/1000000000 : ℝ)*X 2 1+(4013173643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-100182813/10000000000 : ℝ)*X 0 0+(2963543373/5000000000 : ℝ)*X 0 1+(5926899523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s2_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((795911989/10000000000 : ℝ)*X 1 0+(-2482862729/5000000000 : ℝ)*X 1 1+(6561274213/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s2_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((79454633/1000000000 : ℝ)*X 2 0+(6557759931/10000000000 : ℝ)*X 2 1+(-497032349/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s2_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((10490887/250000000 : ℝ)*X 0 0+(2934405723/5000000000 : ℝ)*X 0 1+(2936343281/5000000000 : ℝ)*X 0 2+(10490887/250000000 : ℝ)*X 1 0+(2934405723/5000000000 : ℝ)*X 1 1+(2936343281/5000000000 : ℝ)*X 1 2+(10490887/250000000 : ℝ)*X 2 0+(2934405723/5000000000 : ℝ)*X 2 1+(2936343281/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s2_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39448606220846450185537/12920000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1000307975950241/50000000000000 : ℝ)*(major0) + (1000307975950241/50000000000000 : ℝ)*(major1) + (1000307975950241/50000000000000 : ℝ)*(major2) + (1325309404418093/50000000000000 : ℝ)*(sp0) + (2650628581767727/100000000000000 : ℝ)*(sp1) + (132531573226271/5000000000000 : ℝ)*(sp2) + (270117293820773/20000000000000 : ℝ)*(sp3) + (934800039/4000000000000 : ℝ)*(sp4) + (6670734663/50000000000000 : ℝ)*(sp5) + (167591513/1562500000000 : ℝ)*(sp6) + (1398030971/100000000000000 : ℝ)*(sp8) + (826815539/50000000000000 : ℝ)*(sp9) + (34662147/2500000000000 : ℝ)*(sp10) + (439013093/25000000000000 : ℝ)*(sp11) + (1350588225156237/100000000000000 : ℝ)*(f.failure) + (662660894217033/25000000000000 : ℝ)*(f.sum) + (61711037466337/38760000000000000000000000000 : ℝ)*base65 + (8431438843765291687/1938000000000000000000000000000000 : ℝ)*base68 + (9220036949011291687/1938000000000000000000000000000000 : ℝ)*base70 + (18574138011136708313/1938000000000000000000000000000000 : ℝ)*base71 + (160704049359503/38760000000000000000000000000 : ℝ)*base74 + (15818675731180708313/1938000000000000000000000000000000 : ℝ)*base75 + (2341134506674708313/1938000000000000000000000000000000 : ℝ)*base77 + (4111970956903291687/1938000000000000000000000000000000 : ℝ)*base80 + (59701879643183/38760000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (41663747/10000000000000000000000 : ℝ)*base89 + (41663747/10000000000000000000000 : ℝ)*base91 + (41663747/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5159439471685599484235491061/646000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2030146736721241/100000000000000 : ℝ)*(major0) + (2030146736721241/100000000000000 : ℝ)*(major1) + (2030146736721241/100000000000000 : ℝ)*(major2) + (733548539/100000000000000 : ℝ)*(sp1) + (50451363/25000000000000 : ℝ)*(sp2) + (337118533/100000000000000 : ℝ)*(sp3) + (2689768186327917/100000000000000 : ℝ)*(sp4) + (1344884006761011/50000000000000 : ℝ)*(sp5) + (537953682083013/20000000000000 : ℝ)*(sp6) + (1370523088992101/100000000000000 : ℝ)*(sp7) + (121294859/12500000000000 : ℝ)*(sp8) + (102404057/25000000000000 : ℝ)*(sp9) + (17014571/3125000000000 : ℝ)*(sp10) + (624420109/100000000000000 : ℝ)*(sp11) + (1370524050530743/100000000000000 : ℝ)*(f.failure) + (2689769156686789/100000000000000 : ℝ)*(f.sum) + (80088711197177/77520000000000000000000000000 : ℝ)*base65 + (17180574359905311313/3876000000000000000000000000000000 : ℝ)*base67 + (6694663771741311313/3876000000000000000000000000000000 : ℝ)*base69 + (23787436415929311313/3876000000000000000000000000000000 : ℝ)*base71 + (219362470284583/77520000000000000000000000000 : ℝ)*base74 + (10882487146153311313/3876000000000000000000000000000000 : ℝ)*base75 + (22543946847937311313/3876000000000000000000000000000000 : ℝ)*base77 + (14344456140133311313/3876000000000000000000000000000000 : ℝ)*base79 + (145471742496823/77520000000000000000000000000 : ℝ)*base82 + (2448633/10000000000000000000000 : ℝ)*base89 + (2448633/10000000000000000000000 : ℝ)*base91 + (2448633/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1073_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2627/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4373/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8359/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1073_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1073_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4373/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8359/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1073_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1073_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1073_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4373/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8359/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1073_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

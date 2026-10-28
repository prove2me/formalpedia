-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1283_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:23:42.284743+00:00
-- url     : https://prove2.me/submissions/4f2aab5a-415f-400c-93fe-23a25e297611

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
theorem support_rectangle_w1283_s3_0 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2093581193/10000000000 : ℝ)*x 0 + (2717717963/5000000000 : ℝ)*x 1 + (1044909347/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093581193/10000000000 : ℝ)^4243 ≤ (12730845286307/100000000000000 : ℝ)^3219 := by
    have hnat : (2093581193 : ℕ)^4243*100000000000000^3219 ≤ 12730845286307^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093581193 10000000000 12730845286307 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717717963/5000000000 : ℝ)^4243 ≤ (22386153228767/50000000000000 : ℝ)^3219 := by
    have hnat : (2717717963 : ℕ)^4243*50000000000000^3219 ≤ 22386153228767^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717717963 5000000000 22386153228767 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044909347/2000000000 : ℝ)^4243 ≤ (42496848235707/100000000000000 : ℝ)^3219 := by
    have hnat : (1044909347 : ℕ)^4243*100000000000000^3219 ≤ 42496848235707^3219*2000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044909347 2000000000 42496848235707 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2093581193/10000000000 : ℝ), (2717717963/5000000000 : ℝ), (1044909347/2000000000 : ℝ)] ![(12730845286307/100000000000000 : ℝ), (22386153228767/50000000000000 : ℝ), (42496848235707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2093581193/10000000000 : ℝ)|^4243 ≤ (12730845286307/100000000000000 : ℝ)^3219
        have hw : |(-2093581193/10000000000 : ℝ)|=(2093581193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717717963/5000000000 : ℝ)|^4243 ≤ (22386153228767/50000000000000 : ℝ)^3219
        have hw : |(2717717963/5000000000 : ℝ)|=(2717717963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1044909347/2000000000 : ℝ)|^4243 ≤ (42496848235707/100000000000000 : ℝ)^3219
        have hw : |(1044909347/2000000000 : ℝ)|=(1044909347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s3_1 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354899439/10000000000 : ℝ)*x 0 + (-110077083/500000000 : ℝ)*x 1 + (5224546799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354899439/10000000000 : ℝ)^4243 ≤ (43899954720071/100000000000000 : ℝ)^3219 := by
    have hnat : (5354899439 : ℕ)^4243*100000000000000^3219 ≤ 43899954720071^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354899439 10000000000 43899954720071 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110077083/500000000 : ℝ)^4243 ≤ (13603196339879/100000000000000 : ℝ)^3219 := by
    have hnat : (110077083 : ℕ)^4243*100000000000000^3219 ≤ 13603196339879^3219*500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110077083 500000000 13603196339879 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5224546799/10000000000 : ℝ)^4243 ≤ (4249684892189/10000000000000 : ℝ)^3219 := by
    have hnat : (5224546799 : ℕ)^4243*10000000000000^3219 ≤ 4249684892189^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224546799 10000000000 4249684892189 10000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354899439/10000000000 : ℝ), (-110077083/500000000 : ℝ), (5224546799/10000000000 : ℝ)] ![(43899954720071/100000000000000 : ℝ), (13603196339879/100000000000000 : ℝ), (4249684892189/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354899439/10000000000 : ℝ)|^4243 ≤ (43899954720071/100000000000000 : ℝ)^3219
        have hw : |(5354899439/10000000000 : ℝ)|=(5354899439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-110077083/500000000 : ℝ)|^4243 ≤ (13603196339879/100000000000000 : ℝ)^3219
        have hw : |(-110077083/500000000 : ℝ)|=(110077083/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5224546799/10000000000 : ℝ)|^4243 ≤ (4249684892189/10000000000000 : ℝ)^3219
        have hw : |(5224546799/10000000000 : ℝ)|=(5224546799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s3_2 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535489947/1000000000 : ℝ)*x 0 + (1306136653/2500000000 : ℝ)*x 1 + (-1100770933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535489947/1000000000 : ℝ)^4243 ≤ (43899955055057/100000000000000 : ℝ)^3219 := by
    have hnat : (535489947 : ℕ)^4243*100000000000000^3219 ≤ 43899955055057^3219*1000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535489947 1000000000 43899955055057 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1306136653/2500000000 : ℝ)^4243 ≤ (10624211729237/25000000000000 : ℝ)^3219 := by
    have hnat : (1306136653 : ℕ)^4243*25000000000000^3219 ≤ 10624211729237^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306136653 2500000000 10624211729237 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100770933/5000000000 : ℝ)^4243 ≤ (3400799504413/25000000000000 : ℝ)^3219 := by
    have hnat : (1100770933 : ℕ)^4243*25000000000000^3219 ≤ 3400799504413^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100770933 5000000000 3400799504413 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535489947/1000000000 : ℝ), (1306136653/2500000000 : ℝ), (-1100770933/5000000000 : ℝ)] ![(43899955055057/100000000000000 : ℝ), (10624211729237/25000000000000 : ℝ), (3400799504413/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535489947/1000000000 : ℝ)|^4243 ≤ (43899955055057/100000000000000 : ℝ)^3219
        have hw : |(535489947/1000000000 : ℝ)|=(535489947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1306136653/2500000000 : ℝ)|^4243 ≤ (10624211729237/25000000000000 : ℝ)^3219
        have hw : |(1306136653/2500000000 : ℝ)|=(1306136653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1100770933/5000000000 : ℝ)|^4243 ≤ (3400799504413/25000000000000 : ℝ)^3219
        have hw : |(-1100770933/5000000000 : ℝ)|=(1100770933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s3_3 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (271299641/625000000 : ℝ)*x 0 + (4129978127/10000000000 : ℝ)*x 1 + (2280957813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271299641/625000000 : ℝ)^4243 ≤ (16643547683721/50000000000000 : ℝ)^3219 := by
    have hnat : (271299641 : ℕ)^4243*50000000000000^3219 ≤ 16643547683721^3219*625000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271299641 625000000 16643547683721 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4129978127/10000000000 : ℝ)^4243 ≤ (31172843867023/100000000000000 : ℝ)^3219 := by
    have hnat : (4129978127 : ℕ)^4243*100000000000000^3219 ≤ 31172843867023^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129978127 10000000000 31172843867023 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2280957813/5000000000 : ℝ)^4243 ≤ (7108012150249/20000000000000 : ℝ)^3219 := by
    have hnat : (2280957813 : ℕ)^4243*20000000000000^3219 ≤ 7108012150249^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280957813 5000000000 7108012150249 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271299641/625000000 : ℝ), (4129978127/10000000000 : ℝ), (2280957813/5000000000 : ℝ)] ![(16643547683721/50000000000000 : ℝ), (31172843867023/100000000000000 : ℝ), (7108012150249/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271299641/625000000 : ℝ)|^4243 ≤ (16643547683721/50000000000000 : ℝ)^3219
        have hw : |(271299641/625000000 : ℝ)|=(271299641/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4129978127/10000000000 : ℝ)|^4243 ≤ (31172843867023/100000000000000 : ℝ)^3219
        have hw : |(4129978127/10000000000 : ℝ)|=(4129978127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2280957813/5000000000 : ℝ)|^4243 ≤ (7108012150249/20000000000000 : ℝ)^3219
        have hw : |(2280957813/5000000000 : ℝ)|=(2280957813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s3_4 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2093604439/10000000000 : ℝ)*x 0 + (1306365221/2500000000 : ℝ)*x 1 + (5434516003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093604439/10000000000 : ℝ)^4243 ≤ (6365515805087/50000000000000 : ℝ)^3219 := by
    have hnat : (2093604439 : ℕ)^4243*50000000000000^3219 ≤ 6365515805087^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093604439 10000000000 6365515805087 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1306365221/2500000000 : ℝ)^4243 ≤ (2656665603811/6250000000000 : ℝ)^3219 := by
    have hnat : (1306365221 : ℕ)^4243*6250000000000^3219 ≤ 2656665603811^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306365221 2500000000 2656665603811 6250000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434516003/10000000000 : ℝ)^4243 ≤ (44762318724441/100000000000000 : ℝ)^3219 := by
    have hnat : (5434516003 : ℕ)^4243*100000000000000^3219 ≤ 44762318724441^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434516003 10000000000 44762318724441 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2093604439/10000000000 : ℝ), (1306365221/2500000000 : ℝ), (5434516003/10000000000 : ℝ)] ![(6365515805087/50000000000000 : ℝ), (2656665603811/6250000000000 : ℝ), (44762318724441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2093604439/10000000000 : ℝ)|^4243 ≤ (6365515805087/50000000000000 : ℝ)^3219
        have hw : |(-2093604439/10000000000 : ℝ)|=(2093604439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1306365221/2500000000 : ℝ)|^4243 ≤ (2656665603811/6250000000000 : ℝ)^3219
        have hw : |(1306365221/2500000000 : ℝ)|=(1306365221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434516003/10000000000 : ℝ)|^4243 ≤ (44762318724441/100000000000000 : ℝ)^3219
        have hw : |(5434516003/10000000000 : ℝ)|=(5434516003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s3_5 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2650481787/5000000000 : ℝ)*x 0 + (-1991572289/10000000000 : ℝ)*x 1 + (271725797/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650481787/5000000000 : ℝ)^4243 ≤ (4331805984049/10000000000000 : ℝ)^3219 := by
    have hnat : (2650481787 : ℕ)^4243*10000000000000^3219 ≤ 4331805984049^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650481787 5000000000 4331805984049 10000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1991572289/10000000000 : ℝ)^4243 ≤ (11919622105329/100000000000000 : ℝ)^3219 := by
    have hnat : (1991572289 : ℕ)^4243*100000000000000^3219 ≤ 11919622105329^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991572289 10000000000 11919622105329 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271725797/500000000 : ℝ)^4243 ≤ (44762318040459/100000000000000 : ℝ)^3219 := by
    have hnat : (271725797 : ℕ)^4243*100000000000000^3219 ≤ 44762318040459^3219*500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271725797 500000000 44762318040459 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650481787/5000000000 : ℝ), (-1991572289/10000000000 : ℝ), (271725797/500000000 : ℝ)] ![(4331805984049/10000000000000 : ℝ), (11919622105329/100000000000000 : ℝ), (44762318040459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650481787/5000000000 : ℝ)|^4243 ≤ (4331805984049/10000000000000 : ℝ)^3219
        have hw : |(2650481787/5000000000 : ℝ)|=(2650481787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1991572289/10000000000 : ℝ)|^4243 ≤ (11919622105329/100000000000000 : ℝ)^3219
        have hw : |(-1991572289/10000000000 : ℝ)|=(1991572289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271725797/500000000 : ℝ)|^4243 ≤ (44762318040459/100000000000000 : ℝ)^3219
        have hw : |(271725797/500000000 : ℝ)|=(271725797/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s3_6 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20706889/39062500 : ℝ)*x 0 + (679314489/1250000000 : ℝ)*x 1 + (-1991572313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20706889/39062500 : ℝ)^4243 ≤ (43318059948203/100000000000000 : ℝ)^3219 := by
    have hnat : (20706889 : ℕ)^4243*100000000000000^3219 ≤ 43318059948203^3219*39062500^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20706889 39062500 43318059948203 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679314489/1250000000 : ℝ)^4243 ≤ (44762317736467/100000000000000 : ℝ)^3219 := by
    have hnat : (679314489 : ℕ)^4243*100000000000000^3219 ≤ 44762317736467^3219*1250000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679314489 1250000000 44762317736467 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1991572313/10000000000 : ℝ)^4243 ≤ (11919622294663/100000000000000 : ℝ)^3219 := by
    have hnat : (1991572313 : ℕ)^4243*100000000000000^3219 ≤ 11919622294663^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991572313 10000000000 11919622294663 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20706889/39062500 : ℝ), (679314489/1250000000 : ℝ), (-1991572313/10000000000 : ℝ)] ![(43318059948203/100000000000000 : ℝ), (44762317736467/100000000000000 : ℝ), (11919622294663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20706889/39062500 : ℝ)|^4243 ≤ (43318059948203/100000000000000 : ℝ)^3219
        have hw : |(20706889/39062500 : ℝ)|=(20706889/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679314489/1250000000 : ℝ)|^4243 ≤ (44762317736467/100000000000000 : ℝ)^3219
        have hw : |(679314489/1250000000 : ℝ)|=(679314489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1991572313/10000000000 : ℝ)|^4243 ≤ (11919622294663/100000000000000 : ℝ)^3219
        have hw : |(-1991572313/10000000000 : ℝ)|=(1991572313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s3_7 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (217042081/500000000 : ℝ)*x 0 + (1140010773/2500000000 : ℝ)*x 1 + (2065931239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217042081/500000000 : ℝ)^4243 ≤ (16643787058221/50000000000000 : ℝ)^3219 := by
    have hnat : (217042081 : ℕ)^4243*50000000000000^3219 ≤ 16643787058221^3219*500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217042081 500000000 16643787058221 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1140010773/2500000000 : ℝ)^4243 ≤ (17760416592271/50000000000000 : ℝ)^3219 := by
    have hnat : (1140010773 : ℕ)^4243*50000000000000^3219 ≤ 17760416592271^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140010773 2500000000 17760416592271 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2065931239/5000000000 : ℝ)^4243 ≤ (3119159269149/10000000000000 : ℝ)^3219 := by
    have hnat : (2065931239 : ℕ)^4243*10000000000000^3219 ≤ 3119159269149^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065931239 5000000000 3119159269149 10000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217042081/500000000 : ℝ), (1140010773/2500000000 : ℝ), (2065931239/5000000000 : ℝ)] ![(16643787058221/50000000000000 : ℝ), (17760416592271/50000000000000 : ℝ), (3119159269149/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217042081/500000000 : ℝ)|^4243 ≤ (16643787058221/50000000000000 : ℝ)^3219
        have hw : |(217042081/500000000 : ℝ)|=(217042081/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1140010773/2500000000 : ℝ)|^4243 ≤ (17760416592271/50000000000000 : ℝ)^3219
        have hw : |(1140010773/2500000000 : ℝ)|=(1140010773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2065931239/5000000000 : ℝ)|^4243 ≤ (3119159269149/10000000000000 : ℝ)^3219
        have hw : |(2065931239/5000000000 : ℝ)|=(2065931239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1283_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4719/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10617/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7539/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16359/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4719/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16359/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4719/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16359/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4719/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16359/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4719/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16359/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4719/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16359/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4719/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4719/50000 : ℝ) ^ (2121/512 : ℝ) ≤ (1133418237177473/20000000000000000000 : ℝ) := by
    have hpowers : (4719/50000 : ℝ)^2121 ≤ (1133418237177473/20000000000000000000 : ℝ)^512 := by
      have hnat : (4719 : ℕ)^2121*20000000000000000000^512 ≤ 1133418237177473^512*50000^2121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4719 50000 1133418237177473 20000000000000000000 2121 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4719/50000 : ℝ)) (X := (1133418237177473/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16359/100000 : ℝ) ^ (2121/512 : ℝ) ≤ (55325573131753057/100000000000000000000 : ℝ) := by
    have hpowers : (16359/100000 : ℝ)^2121 ≤ (55325573131753057/100000000000000000000 : ℝ)^512 := by
      have hnat : (16359 : ℕ)^2121*100000000000000000000^512 ≤ 55325573131753057^512*100000^2121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16359 100000 55325573131753057 100000000000000000000 2121 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16359/100000 : ℝ)) (X := (55325573131753057/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001133418237177473/10000000000000000000 : ℝ) ≤ (312508549699303/312500000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (10001133418237177473/10000000000000000000 : ℝ)^512 ≤ (312508549699303/312500000000000 : ℝ)^2121 := by
      have hnat : (10001133418237177473 : ℕ)^512*312500000000000^2121 ≤ 312508549699303^2121*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001133418237177473 10000000000000000000 312508549699303 312500000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312508549699303/312500000000000 : ℝ)) (X := (10001133418237177473/10000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50030496332158820211/50000000000000000000 : ℝ) ≤ (5000735997693701/5000000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (50030496332158820211/50000000000000000000 : ℝ)^512 ≤ (5000735997693701/5000000000000000 : ℝ)^2121 := by
      have hnat : (50030496332158820211 : ℕ)^512*5000000000000000^2121 ≤ 5000735997693701^2121*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030496332158820211 50000000000000000000 5000735997693701 5000000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000735997693701/5000000000000000 : ℝ)) (X := (50030496332158820211/50000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50055325573131753057/50000000000000000000 : ℝ) ≤ (2500667600099277/2500000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (50055325573131753057/50000000000000000000 : ℝ)^512 ≤ (2500667600099277/2500000000000000 : ℝ)^2121 := by
      have hnat : (50055325573131753057 : ℕ)^512*2500000000000000^2121 ≤ 2500667600099277^2121*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50055325573131753057 50000000000000000000 2500667600099277 2500000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500667600099277/2500000000000000 : ℝ)) (X := (50055325573131753057/50000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1133418237177473/20000000000000000000 : ℝ) ≤ ((576577270217006863/576750000000000000 : ℝ)+2*(599202504853/346050000000000 : ℝ)*(4719/50000 : ℝ))^(2121/512 : ℝ) := by
    rw [show (576577270217006863/576750000000000000 : ℝ)+2*(599202504853/346050000000000 : ℝ)*(4719/50000 : ℝ)=(312508549699303/312500000000000 : ℝ) by norm_num, show 1+2*(1133418237177473/20000000000000000000 : ℝ)=(10001133418237177473/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(55325573131753057/100000000000000000000 : ℝ)+(1133418237177473/20000000000000000000 : ℝ) ≤ ((576577270217006863/576750000000000000 : ℝ)+(599202504853/346050000000000 : ℝ)*((16359/100000 : ℝ)+(4719/50000 : ℝ)))^(2121/512 : ℝ) := by
    rw [show (576577270217006863/576750000000000000 : ℝ)+(599202504853/346050000000000 : ℝ)*((16359/100000 : ℝ)+(4719/50000 : ℝ))=(5000735997693701/5000000000000000 : ℝ) by norm_num, show 1+(55325573131753057/100000000000000000000 : ℝ)+(1133418237177473/20000000000000000000 : ℝ)=(50030496332158820211/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(55325573131753057/100000000000000000000 : ℝ) ≤ ((576577270217006863/576750000000000000 : ℝ)+2*(599202504853/346050000000000 : ℝ)*(16359/100000 : ℝ))^(2121/512 : ℝ) := by
    rw [show (576577270217006863/576750000000000000 : ℝ)+2*(599202504853/346050000000000 : ℝ)*(16359/100000 : ℝ)=(2500667600099277/2500000000000000 : ℝ) by norm_num, show 1+2*(55325573131753057/100000000000000000000 : ℝ)=(50055325573131753057/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (576577270217006863/576750000000000000 : ℝ)*(X 1 0+X 2 0)+(599202504853/346050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (4719/50000 : ℝ)) (hi := (16359/100000 : ℝ)) (c := (576577270217006863/576750000000000000 : ℝ)) (alpha := (599202504853/346050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (576577270217006863/576750000000000000 : ℝ)*(X 0 1+X 2 1)+(599202504853/346050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (4719/50000 : ℝ)) (hi := (16359/100000 : ℝ)) (c := (576577270217006863/576750000000000000 : ℝ)) (alpha := (599202504853/346050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (576577270217006863/576750000000000000 : ℝ)*(X 0 2+X 1 2)+(599202504853/346050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (4719/50000 : ℝ)) (hi := (16359/100000 : ℝ)) (c := (576577270217006863/576750000000000000 : ℝ)) (alpha := (599202504853/346050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2093581193/10000000000 : ℝ)*X 0 0+(2717717963/5000000000 : ℝ)*X 0 1+(1044909347/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354899439/10000000000 : ℝ)*X 1 0+(-110077083/500000000 : ℝ)*X 1 1+(5224546799/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535489947/1000000000 : ℝ)*X 2 0+(1306136653/2500000000 : ℝ)*X 2 1+(-1100770933/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((271299641/625000000 : ℝ)*X 0 0+(4129978127/10000000000 : ℝ)*X 0 1+(2280957813/5000000000 : ℝ)*X 0 2+(271299641/625000000 : ℝ)*X 1 0+(4129978127/10000000000 : ℝ)*X 1 1+(2280957813/5000000000 : ℝ)*X 1 2+(271299641/625000000 : ℝ)*X 2 0+(4129978127/10000000000 : ℝ)*X 2 1+(2280957813/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2093604439/10000000000 : ℝ)*X 0 0+(1306365221/2500000000 : ℝ)*X 0 1+(5434516003/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2650481787/5000000000 : ℝ)*X 1 0+(-1991572289/10000000000 : ℝ)*X 1 1+(271725797/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((20706889/39062500 : ℝ)*X 2 0+(679314489/1250000000 : ℝ)*X 2 1+(-1991572313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((217042081/500000000 : ℝ)*X 0 0+(1140010773/2500000000 : ℝ)*X 0 1+(2065931239/5000000000 : ℝ)*X 0 2+(217042081/500000000 : ℝ)*X 1 0+(1140010773/2500000000 : ℝ)*X 1 1+(2065931239/5000000000 : ℝ)*X 1 2+(217042081/500000000 : ℝ)*X 2 0+(1140010773/2500000000 : ℝ)*X 2 1+(2065931239/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (191909887375216255401509/19225000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1897541087/100000000000000 : ℝ)*(base19) + (859832553/50000000000000 : ℝ)*(base23) + (54975319/50000000000000 : ℝ)*(lower2) + (205573787/50000000000000 : ℝ)*(upper3) + (52372733/100000000000000 : ℝ)*(upper5) + (7057065542619/200000000000 : ℝ)*(major0) + (7057065542619/200000000000 : ℝ)*(major1) + (7057065542619/200000000000 : ℝ)*(major2) + (2370930149588599/50000000000000 : ℝ)*(sp0) + (4741883422552939/100000000000000 : ℝ)*(sp1) + (118547090010723/2500000000000 : ℝ)*(sp2) + (578790545539883/25000000000000 : ℝ)*(sp3) + (6255229207/25000000000000 : ℝ)*(sp4) + (17707621803/100000000000000 : ℝ)*(sp7) + (289397486222667/12500000000000 : ℝ)*(f.failure) + (2370942660047013/50000000000000 : ℝ)*(f.sum) + (4235169085789/1153500000000000000000000000 : ℝ)*base65 + (899631728280197/115350000000000000000000000000 : ℝ)*base67 + (606061463481197/115350000000000000000000000000 : ℝ)*base69 + (1944664947348647/115350000000000000000000000000 : ℝ)*base71 + (24512313451/23070000000000000000000000 : ℝ)*base74 + (2063491959239747/115350000000000000000000000000 : ℝ)*base75 + (1658392641850997/115350000000000000000000000000 : ℝ)*base77 + (2173989951471197/115350000000000000000000000000 : ℝ)*base79 + (1698017116511/1153500000000000000000000000 : ℝ)*base82 + (5060193/1250000000000000000000 : ℝ)*base89 + (5060193/1250000000000000000000 : ℝ)*base91 + (5060193/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9528459020525031225519539/3604687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (28121781/3125000000000 : ℝ)*(base19) + (179942923/20000000000000 : ℝ)*(base23) + (35133883/50000000000000 : ℝ)*(upper3) + (595117/50000000000000 : ℝ)*(lower4) + (96758341/100000000000000 : ℝ)*(upper5) + (1779722763092023/50000000000000 : ℝ)*(major0) + (1779722763092023/50000000000000 : ℝ)*(major1) + (1779722763092023/50000000000000 : ℝ)*(major2) + (57754613/390625000000 : ℝ)*(sp1) + (13659702117/100000000000000 : ℝ)*(sp2) + (4783428256357173/100000000000000 : ℝ)*(sp4) + (4783412571279253/100000000000000 : ℝ)*(sp5) + (119585342423511/2500000000000 : ℝ)*(sp6) + (233546270789917/10000000000000 : ℝ)*(sp7) + (233546270789917/10000000000000 : ℝ)*(f.failure) + (4783428256357173/100000000000000 : ℝ)*(f.sum) + (4224803545589/34605000000000000000000000000 : ℝ)*base66 + (361938201802606547/86512500000000000000000000000000 : ℝ)*base67 + (80424086544519047/86512500000000000000000000000000 : ℝ)*base69 + (335277320560918453/86512500000000000000000000000000 : ℝ)*base72 + (13533153702539/34605000000000000000000000000 : ℝ)*base74 + (643992225395356547/86512500000000000000000000000000 : ℝ)*base75 + (33050916808381547/86512500000000000000000000000000 : ℝ)*base77 + (1109965249730206547/86512500000000000000000000000000 : ℝ)*base79 + (26592165034207/17302500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2502057/1000000000000000000000 : ℝ)*base90 + (2502057/1000000000000000000000 : ℝ)*base92 + (2502057/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1283_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4719/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10617/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7539/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1283_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1283_s4_0 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-523900217/2500000000 : ℝ)*x 0 + (5419631661/10000000000 : ℝ)*x 1 + (5239027313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523900217/2500000000 : ℝ)^4243 ≤ (398344876867/3125000000000 : ℝ)^3219 := by
    have hnat : (523900217 : ℕ)^4243*3125000000000^3219 ≤ 398344876867^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523900217 2500000000 398344876867 3125000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419631661/10000000000 : ℝ)^4243 ≤ (22300396062931/50000000000000 : ℝ)^3219 := by
    have hnat : (5419631661 : ℕ)^4243*50000000000000^3219 ≤ 22300396062931^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419631661 10000000000 22300396062931 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239027313/10000000000 : ℝ)^4243 ≤ (1706086872029/4000000000000 : ℝ)^3219 := by
    have hnat : (5239027313 : ℕ)^4243*4000000000000^3219 ≤ 1706086872029^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239027313 10000000000 1706086872029 4000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-523900217/2500000000 : ℝ), (5419631661/10000000000 : ℝ), (5239027313/10000000000 : ℝ)] ![(398344876867/3125000000000 : ℝ), (22300396062931/50000000000000 : ℝ), (1706086872029/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-523900217/2500000000 : ℝ)|^4243 ≤ (398344876867/3125000000000 : ℝ)^3219
        have hw : |(-523900217/2500000000 : ℝ)|=(523900217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419631661/10000000000 : ℝ)|^4243 ≤ (22300396062931/50000000000000 : ℝ)^3219
        have hw : |(5419631661/10000000000 : ℝ)|=(5419631661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239027313/10000000000 : ℝ)|^4243 ≤ (1706086872029/4000000000000 : ℝ)^3219
        have hw : |(5239027313/10000000000 : ℝ)|=(5239027313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s4_1 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350910453/10000000000 : ℝ)*x 0 + (-2187748879/10000000000 : ℝ)*x 1 + (5239027371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350910453/10000000000 : ℝ)^4243 ≤ (43856854860893/100000000000000 : ℝ)^3219 := by
    have hnat : (5350910453 : ℕ)^4243*100000000000000^3219 ≤ 43856854860893^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350910453 10000000000 43856854860893 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2187748879/10000000000 : ℝ)^4243 ≤ (3372743175123/25000000000000 : ℝ)^3219 := by
    have hnat : (2187748879 : ℕ)^4243*25000000000000^3219 ≤ 3372743175123^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187748879 10000000000 3372743175123 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239027371/10000000000 : ℝ)^4243 ≤ (21326086211563/50000000000000 : ℝ)^3219 := by
    have hnat : (5239027371 : ℕ)^4243*50000000000000^3219 ≤ 21326086211563^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239027371 10000000000 21326086211563 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350910453/10000000000 : ℝ), (-2187748879/10000000000 : ℝ), (5239027371/10000000000 : ℝ)] ![(43856854860893/100000000000000 : ℝ), (3372743175123/25000000000000 : ℝ), (21326086211563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350910453/10000000000 : ℝ)|^4243 ≤ (43856854860893/100000000000000 : ℝ)^3219
        have hw : |(5350910453/10000000000 : ℝ)|=(5350910453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2187748879/10000000000 : ℝ)|^4243 ≤ (3372743175123/25000000000000 : ℝ)^3219
        have hw : |(-2187748879/10000000000 : ℝ)|=(2187748879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239027371/10000000000 : ℝ)|^4243 ≤ (21326086211563/50000000000000 : ℝ)^3219
        have hw : |(5239027371/10000000000 : ℝ)|=(5239027371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s4_2 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350910261/10000000000 : ℝ)*x 0 + (5239027533/10000000000 : ℝ)*x 1 + (-54693723/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350910261/10000000000 : ℝ)^4243 ≤ (21928426393317/50000000000000 : ℝ)^3219 := by
    have hnat : (5350910261 : ℕ)^4243*50000000000000^3219 ≤ 21928426393317^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350910261 10000000000 21928426393317 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239027533/10000000000 : ℝ)^4243 ≤ (21326087080779/50000000000000 : ℝ)^3219 := by
    have hnat : (5239027533 : ℕ)^4243*50000000000000^3219 ≤ 21326087080779^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239027533 10000000000 21326087080779 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54693723/250000000 : ℝ)^4243 ≤ (13490973033751/100000000000000 : ℝ)^3219 := by
    have hnat : (54693723 : ℕ)^4243*100000000000000^3219 ≤ 13490973033751^3219*250000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54693723 250000000 13490973033751 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350910261/10000000000 : ℝ), (5239027533/10000000000 : ℝ), (-54693723/250000000 : ℝ)] ![(21928426393317/50000000000000 : ℝ), (21326087080779/50000000000000 : ℝ), (13490973033751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350910261/10000000000 : ℝ)|^4243 ≤ (21928426393317/50000000000000 : ℝ)^3219
        have hw : |(5350910261/10000000000 : ℝ)|=(5350910261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239027533/10000000000 : ℝ)|^4243 ≤ (21326087080779/50000000000000 : ℝ)^3219
        have hw : |(5239027533/10000000000 : ℝ)|=(5239027533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54693723/250000000 : ℝ)|^4243 ≤ (13490973033751/100000000000000 : ℝ)^3219
        have hw : |(-54693723/250000000 : ℝ)|=(54693723/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s4_3 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4342012571/10000000000 : ℝ)*x 0 + (4160839/10000000 : ℝ)*x 1 + (2265373661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342012571/10000000000 : ℝ)^4243 ≤ (16649705230717/50000000000000 : ℝ)^3219 := by
    have hnat : (4342012571 : ℕ)^4243*50000000000000^3219 ≤ 16649705230717^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342012571 10000000000 16649705230717 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4160839/10000000 : ℝ)^4243 ≤ (7870060978041/25000000000000 : ℝ)^3219 := by
    have hnat : (4160839 : ℕ)^4243*25000000000000^3219 ≤ 7870060978041^3219*10000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4160839 10000000 7870060978041 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2265373661/5000000000 : ℝ)^4243 ≤ (35220345615049/100000000000000 : ℝ)^3219 := by
    have hnat : (2265373661 : ℕ)^4243*100000000000000^3219 ≤ 35220345615049^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265373661 5000000000 35220345615049 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342012571/10000000000 : ℝ), (4160839/10000000 : ℝ), (2265373661/5000000000 : ℝ)] ![(16649705230717/50000000000000 : ℝ), (7870060978041/25000000000000 : ℝ), (35220345615049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342012571/10000000000 : ℝ)|^4243 ≤ (16649705230717/50000000000000 : ℝ)^3219
        have hw : |(4342012571/10000000000 : ℝ)|=(4342012571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4160839/10000000 : ℝ)|^4243 ≤ (7870060978041/25000000000000 : ℝ)^3219
        have hw : |(4160839/10000000 : ℝ)|=(4160839/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2265373661/5000000000 : ℝ)|^4243 ≤ (35220345615049/100000000000000 : ℝ)^3219
        have hw : |(2265373661/5000000000 : ℝ)|=(2265373661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s4_4 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2095615491/10000000000 : ℝ)*x 0 + (5239698839/10000000000 : ℝ)*x 1 + (5418956501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095615491/10000000000 : ℝ)^4243 ≤ (12747153303483/100000000000000 : ℝ)^3219 := by
    have hnat : (2095615491 : ℕ)^4243*100000000000000^3219 ≤ 12747153303483^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095615491 10000000000 12747153303483 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239698839/10000000000 : ℝ)^4243 ≤ (42659378132093/100000000000000 : ℝ)^3219 := by
    have hnat : (5239698839 : ℕ)^4243*100000000000000^3219 ≤ 42659378132093^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239698839 10000000000 42659378132093 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418956501/10000000000 : ℝ)^4243 ≤ (22296734276939/50000000000000 : ℝ)^3219 := by
    have hnat : (5418956501 : ℕ)^4243*50000000000000^3219 ≤ 22296734276939^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418956501 10000000000 22296734276939 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2095615491/10000000000 : ℝ), (5239698839/10000000000 : ℝ), (5418956501/10000000000 : ℝ)] ![(12747153303483/100000000000000 : ℝ), (42659378132093/100000000000000 : ℝ), (22296734276939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2095615491/10000000000 : ℝ)|^4243 ≤ (12747153303483/100000000000000 : ℝ)^3219
        have hw : |(-2095615491/10000000000 : ℝ)|=(2095615491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239698839/10000000000 : ℝ)|^4243 ≤ (42659378132093/100000000000000 : ℝ)^3219
        have hw : |(5239698839/10000000000 : ℝ)|=(5239698839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418956501/10000000000 : ℝ)|^4243 ≤ (22296734276939/50000000000000 : ℝ)^3219
        have hw : |(5418956501/10000000000 : ℝ)|=(5418956501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s4_5 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663090519/1250000000 : ℝ)*x 0 + (-200781969/1000000000 : ℝ)*x 1 + (2709478161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663090519/1250000000 : ℝ)^4243 ≤ (21679285273929/50000000000000 : ℝ)^3219 := by
    have hnat : (663090519 : ℕ)^4243*50000000000000^3219 ≤ 21679285273929^3219*1250000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663090519 1250000000 21679285273929 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200781969/1000000000 : ℝ)^4243 ≤ (2409592566551/20000000000000 : ℝ)^3219 := by
    have hnat : (200781969 : ℕ)^4243*20000000000000^3219 ≤ 2409592566551^3219*1000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200781969 1000000000 2409592566551 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709478161/5000000000 : ℝ)^4243 ≤ (44593466612273/100000000000000 : ℝ)^3219 := by
    have hnat : (2709478161 : ℕ)^4243*100000000000000^3219 ≤ 44593466612273^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709478161 5000000000 44593466612273 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663090519/1250000000 : ℝ), (-200781969/1000000000 : ℝ), (2709478161/5000000000 : ℝ)] ![(21679285273929/50000000000000 : ℝ), (2409592566551/20000000000000 : ℝ), (44593466612273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663090519/1250000000 : ℝ)|^4243 ≤ (21679285273929/50000000000000 : ℝ)^3219
        have hw : |(663090519/1250000000 : ℝ)|=(663090519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-200781969/1000000000 : ℝ)|^4243 ≤ (2409592566551/20000000000000 : ℝ)^3219
        have hw : |(-200781969/1000000000 : ℝ)|=(200781969/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709478161/5000000000 : ℝ)|^4243 ≤ (44593466612273/100000000000000 : ℝ)^3219
        have hw : |(2709478161/5000000000 : ℝ)|=(2709478161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s4_6 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652362213/5000000000 : ℝ)*x 0 + (216758263/400000000 : ℝ)*x 1 + (-2007818969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652362213/5000000000 : ℝ)^4243 ≤ (43358573499847/100000000000000 : ℝ)^3219 := by
    have hnat : (2652362213 : ℕ)^4243*100000000000000^3219 ≤ 43358573499847^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652362213 5000000000 43358573499847 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216758263/400000000 : ℝ)^4243 ≤ (5574183669569/12500000000000 : ℝ)^3219 := by
    have hnat : (216758263 : ℕ)^4243*12500000000000^3219 ≤ 5574183669569^3219*400000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216758263 400000000 5574183669569 12500000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2007818969/10000000000 : ℝ)^4243 ≤ (12047957130111/100000000000000 : ℝ)^3219 := by
    have hnat : (2007818969 : ℕ)^4243*100000000000000^3219 ≤ 12047957130111^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007818969 10000000000 12047957130111 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652362213/5000000000 : ℝ), (216758263/400000000 : ℝ), (-2007818969/10000000000 : ℝ)] ![(43358573499847/100000000000000 : ℝ), (5574183669569/12500000000000 : ℝ), (12047957130111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652362213/5000000000 : ℝ)|^4243 ≤ (43358573499847/100000000000000 : ℝ)^3219
        have hw : |(2652362213/5000000000 : ℝ)|=(2652362213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216758263/400000000 : ℝ)|^4243 ≤ (5574183669569/12500000000000 : ℝ)^3219
        have hw : |(216758263/400000000 : ℝ)|=(216758263/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2007818969/10000000000 : ℝ)|^4243 ≤ (12047957130111/100000000000000 : ℝ)^3219
        have hw : |(-2007818969/10000000000 : ℝ)|=(2007818969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s4_7 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2171021141/5000000000 : ℝ)*x 0 + (4529372817/10000000000 : ℝ)*x 1 + (4162220997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171021141/5000000000 : ℝ)^4243 ≤ (16649855401439/50000000000000 : ℝ)^3219 := by
    have hnat : (2171021141 : ℕ)^4243*50000000000000^3219 ≤ 16649855401439^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171021141 5000000000 16649855401439 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4529372817/10000000000 : ℝ)^4243 ≤ (4400782802509/12500000000000 : ℝ)^3219 := by
    have hnat : (4529372817 : ℕ)^4243*12500000000000^3219 ≤ 4400782802509^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529372817 10000000000 4400782802509 12500000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4162220997/10000000000 : ℝ)^4243 ≤ (31494026769907/100000000000000 : ℝ)^3219 := by
    have hnat : (4162220997 : ℕ)^4243*100000000000000^3219 ≤ 31494026769907^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162220997 10000000000 31494026769907 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171021141/5000000000 : ℝ), (4529372817/10000000000 : ℝ), (4162220997/10000000000 : ℝ)] ![(16649855401439/50000000000000 : ℝ), (4400782802509/12500000000000 : ℝ), (31494026769907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171021141/5000000000 : ℝ)|^4243 ≤ (16649855401439/50000000000000 : ℝ)^3219
        have hw : |(2171021141/5000000000 : ℝ)|=(2171021141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4529372817/10000000000 : ℝ)|^4243 ≤ (4400782802509/12500000000000 : ℝ)^3219
        have hw : |(4529372817/10000000000 : ℝ)|=(4529372817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4162220997/10000000000 : ℝ)|^4243 ≤ (31494026769907/100000000000000 : ℝ)^3219
        have hw : |(4162220997/10000000000 : ℝ)|=(4162220997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1283_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7539/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10617/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10927/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14749/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7539/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10617/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7539/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10617/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7539/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10617/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7539/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10617/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7539/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10617/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7539/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10617/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10617/100000 : ℝ) ^ (2121/512 : ℝ) ≤ (2307153252526857/25000000000000000000 : ℝ) := by
    have hpowers : (10617/100000 : ℝ)^2121 ≤ (2307153252526857/25000000000000000000 : ℝ)^512 := by
      have hnat : (10617 : ℕ)^2121*25000000000000000000^512 ≤ 2307153252526857^512*100000^2121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10617 100000 2307153252526857 25000000000000000000 2121 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10617/100000 : ℝ)) (X := (2307153252526857/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7539/50000 : ℝ) ^ (2121/512 : ℝ) ≤ (39466148602949431/100000000000000000000 : ℝ) := by
    have hpowers : (7539/50000 : ℝ)^2121 ≤ (39466148602949431/100000000000000000000 : ℝ)^512 := by
      have hnat : (7539 : ℕ)^2121*100000000000000000000^512 ≤ 39466148602949431^512*50000^2121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7539 50000 39466148602949431 100000000000000000000 2121 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7539/50000 : ℝ)) (X := (39466148602949431/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502307153252526857/12500000000000000000 : ℝ) ≤ (10000445518067187/10000000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (12502307153252526857/12500000000000000000 : ℝ)^512 ≤ (10000445518067187/10000000000000000 : ℝ)^2121 := by
      have hnat : (12502307153252526857 : ℕ)^512*10000000000000000^2121 ≤ 10000445518067187^2121*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502307153252526857 12500000000000000000 10000445518067187 10000000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000445518067187/10000000000000000 : ℝ)) (X := (12502307153252526857/12500000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048694761613056859/100000000000000000000 : ℝ) ≤ (2500293813229183/2500000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (100048694761613056859/100000000000000000000 : ℝ)^512 ≤ (2500293813229183/2500000000000000 : ℝ)^2121 := by
      have hnat : (100048694761613056859 : ℕ)^512*2500000000000000^2121 ≤ 2500293813229183^2121*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048694761613056859 100000000000000000000 2500293813229183 2500000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500293813229183/2500000000000000 : ℝ)) (X := (100048694761613056859/100000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039466148602949431/50000000000000000000 : ℝ) ≤ (10001904987766277/10000000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (50039466148602949431/50000000000000000000 : ℝ)^512 ≤ (10001904987766277/10000000000000000 : ℝ)^2121 := by
      have hnat : (50039466148602949431 : ℕ)^512*10000000000000000^2121 ≤ 10001904987766277^2121*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039466148602949431 50000000000000000000 10001904987766277 10000000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001904987766277/10000000000000000 : ℝ)) (X := (50039466148602949431/50000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2307153252526857/25000000000000000000 : ℝ) ≤ ((14865497422100827559/14870000000000000000 : ℝ)+2*(145946969909/89220000000000 : ℝ)*(10617/100000 : ℝ))^(2121/512 : ℝ) := by
    rw [show (14865497422100827559/14870000000000000000 : ℝ)+2*(145946969909/89220000000000 : ℝ)*(10617/100000 : ℝ)=(10000445518067187/10000000000000000 : ℝ) by norm_num, show 1+2*(2307153252526857/25000000000000000000 : ℝ)=(12502307153252526857/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39466148602949431/100000000000000000000 : ℝ)+(2307153252526857/25000000000000000000 : ℝ) ≤ ((14865497422100827559/14870000000000000000 : ℝ)+(145946969909/89220000000000 : ℝ)*((7539/50000 : ℝ)+(10617/100000 : ℝ)))^(2121/512 : ℝ) := by
    rw [show (14865497422100827559/14870000000000000000 : ℝ)+(145946969909/89220000000000 : ℝ)*((7539/50000 : ℝ)+(10617/100000 : ℝ))=(2500293813229183/2500000000000000 : ℝ) by norm_num, show 1+(39466148602949431/100000000000000000000 : ℝ)+(2307153252526857/25000000000000000000 : ℝ)=(100048694761613056859/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39466148602949431/100000000000000000000 : ℝ) ≤ ((14865497422100827559/14870000000000000000 : ℝ)+2*(145946969909/89220000000000 : ℝ)*(7539/50000 : ℝ))^(2121/512 : ℝ) := by
    rw [show (14865497422100827559/14870000000000000000 : ℝ)+2*(145946969909/89220000000000 : ℝ)*(7539/50000 : ℝ)=(10001904987766277/10000000000000000 : ℝ) by norm_num, show 1+2*(39466148602949431/100000000000000000000 : ℝ)=(50039466148602949431/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14865497422100827559/14870000000000000000 : ℝ)*(X 1 0+X 2 0)+(145946969909/89220000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (10617/100000 : ℝ)) (hi := (7539/50000 : ℝ)) (c := (14865497422100827559/14870000000000000000 : ℝ)) (alpha := (145946969909/89220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14865497422100827559/14870000000000000000 : ℝ)*(X 0 1+X 2 1)+(145946969909/89220000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (10617/100000 : ℝ)) (hi := (7539/50000 : ℝ)) (c := (14865497422100827559/14870000000000000000 : ℝ)) (alpha := (145946969909/89220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14865497422100827559/14870000000000000000 : ℝ)*(X 0 2+X 1 2)+(145946969909/89220000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (10617/100000 : ℝ)) (hi := (7539/50000 : ℝ)) (c := (14865497422100827559/14870000000000000000 : ℝ)) (alpha := (145946969909/89220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-523900217/2500000000 : ℝ)*X 0 0+(5419631661/10000000000 : ℝ)*X 0 1+(5239027313/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350910453/10000000000 : ℝ)*X 1 0+(-2187748879/10000000000 : ℝ)*X 1 1+(5239027371/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350910261/10000000000 : ℝ)*X 2 0+(5239027533/10000000000 : ℝ)*X 2 1+(-54693723/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4342012571/10000000000 : ℝ)*X 0 0+(4160839/10000000 : ℝ)*X 0 1+(2265373661/5000000000 : ℝ)*X 0 2+(4342012571/10000000000 : ℝ)*X 1 0+(4160839/10000000 : ℝ)*X 1 1+(2265373661/5000000000 : ℝ)*X 1 2+(4342012571/10000000000 : ℝ)*X 2 0+(4160839/10000000 : ℝ)*X 2 1+(2265373661/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2095615491/10000000000 : ℝ)*X 0 0+(5239698839/10000000000 : ℝ)*X 0 1+(5418956501/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663090519/1250000000 : ℝ)*X 1 0+(-200781969/1000000000 : ℝ)*X 1 1+(2709478161/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652362213/5000000000 : ℝ)*X 2 0+(216758263/400000000 : ℝ)*X 2 1+(-2007818969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2171021141/5000000000 : ℝ)*X 0 0+(4529372817/10000000000 : ℝ)*X 0 1+(4162220997/10000000000 : ℝ)*X 0 2+(2171021141/5000000000 : ℝ)*X 1 0+(4529372817/10000000000 : ℝ)*X 1 1+(4162220997/10000000000 : ℝ)*X 1 2+(2171021141/5000000000 : ℝ)*X 2 0+(4529372817/10000000000 : ℝ)*X 2 1+(4162220997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (99588340065181694317948017/18587500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (220016797/50000000000000 : ℝ)*(base19) + (219930271/100000000000000 : ℝ)*(base23) + (42562973/100000000000000 : ℝ)*(lower2) + (24943149/25000000000000 : ℝ)*(upper3) + (1943611/6250000000000 : ℝ)*(lower4) + (206009142666579/5000000000000 : ℝ)*(major0) + (206009142666579/5000000000000 : ℝ)*(major1) + (206009142666579/5000000000000 : ℝ)*(major2) + (2768488884678207/50000000000000 : ℝ)*(sp0) + (692123151557949/12500000000000 : ℝ)*(sp1) + (1107397086513383/20000000000000 : ℝ)*(sp2) + (1351687900855827/50000000000000 : ℝ)*(sp3) + (1970785193/25000000000000 : ℝ)*(sp4) + (50923257/1250000000000 : ℝ)*(sp7) + (1351689937786107/50000000000000 : ℝ)*(f.failure) + (2768492826248593/50000000000000 : ℝ)*(f.sum) + (1088960842509/148700000000000000000000000 : ℝ)*base65 + (75178354946749339/74350000000000000000000000000000 : ℝ)*base68 + (21612528600250661/74350000000000000000000000000000 : ℝ)*base69 + (330256905274450661/74350000000000000000000000000000 : ℝ)*base71 + (1145045963179/371750000000000000000000000 : ℝ)*base73 + (1008706751230950661/74350000000000000000000000000000 : ℝ)*base75 + (424838459314800661/74350000000000000000000000000000 : ℝ)*base77 + (2533013449244700661/74350000000000000000000000000000 : ℝ)*base79 + (63950959893/185875000000000000000000000 : ℝ)*base81 + (26188047/5000000000000000000000 : ℝ)*base90 + (26188047/5000000000000000000000 : ℝ)*base92 + (26188047/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (304546954093353759469947851/29740000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2142188689/100000000000000 : ℝ)*(base19) + (350914257/12500000000000 : ℝ)*(base23) + (58266961/20000000000000 : ℝ)*(upper3) + (334599/781250000000 : ℝ)*(lower4) + (166044626549663/4000000000000 : ℝ)*(major0) + (166044626549663/4000000000000 : ℝ)*(major1) + (166044626549663/4000000000000 : ℝ)*(major2) + (327993383/1000000000000 : ℝ)*(sp1) + (66825177941/100000000000000 : ℝ)*(sp2) + (107937889/20000000000000 : ℝ)*(sp3) + (2789277566694937/50000000000000 : ℝ)*(sp4) + (1115704038372577/20000000000000 : ℝ)*(sp5) + (5578485500897877/100000000000000 : ℝ)*(sp6) + (272367531306001/10000000000000 : ℝ)*(sp7) + (1361837926374727/50000000000000 : ℝ)*(f.failure) + (2789277566694937/50000000000000 : ℝ)*(f.sum) + (16714229227183/2230500000000000000000000000 : ℝ)*base66 + (476891826657452149/178440000000000000000000000000000 : ℝ)*base68 + (753377054719772149/178440000000000000000000000000000 : ℝ)*base70 + (1681940842866212149/178440000000000000000000000000000 : ℝ)*base72 + (2604513756469/892200000000000000000000000 : ℝ)*base74 + (420880416062012149/178440000000000000000000000000000 : ℝ)*base76 + (135283590735267851/178440000000000000000000000000000 : ℝ)*base77 + (136266459668067851/178440000000000000000000000000000 : ℝ)*base79 + (91036699967/278812500000000000000000000 : ℝ)*base82 + (13582933/5000000000000000000000 : ℝ)*base89 + (13582933/5000000000000000000000 : ℝ)*base91 + (13582933/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1283_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7539/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10617/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10927/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1283_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1283_s5_0 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1047989591/5000000000 : ℝ)*x 0 + (1083280969/2000000000 : ℝ)*x 1 + (5242005861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047989591/5000000000 : ℝ)^4243 ≤ (49804958497/390625000000 : ℝ)^3219 := by
    have hnat : (1047989591 : ℕ)^4243*390625000000^3219 ≤ 49804958497^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047989591 5000000000 49804958497 390625000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083280969/2000000000 : ℝ)^4243 ≤ (22282896470807/50000000000000 : ℝ)^3219 := by
    have hnat : (1083280969 : ℕ)^4243*50000000000000^3219 ≤ 22282896470807^3219*2000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083280969 2000000000 22282896470807 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242005861/10000000000 : ℝ)^4243 ≤ (8536827532411/20000000000000 : ℝ)^3219 := by
    have hnat : (5242005861 : ℕ)^4243*20000000000000^3219 ≤ 8536827532411^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242005861 10000000000 8536827532411 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1047989591/5000000000 : ℝ), (1083280969/2000000000 : ℝ), (5242005861/10000000000 : ℝ)] ![(49804958497/390625000000 : ℝ), (22282896470807/50000000000000 : ℝ), (8536827532411/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1047989591/5000000000 : ℝ)|^4243 ≤ (49804958497/390625000000 : ℝ)^3219
        have hw : |(-1047989591/5000000000 : ℝ)|=(1047989591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083280969/2000000000 : ℝ)|^4243 ≤ (22282896470807/50000000000000 : ℝ)^3219
        have hw : |(1083280969/2000000000 : ℝ)|=(1083280969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242005861/10000000000 : ℝ)|^4243 ≤ (8536827532411/20000000000000 : ℝ)^3219
        have hw : |(5242005861/10000000000 : ℝ)|=(5242005861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s5_1 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42800757/80000000 : ℝ)*x 0 + (-1092449957/5000000000 : ℝ)*x 1 + (32762537/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42800757/80000000 : ℝ)^4243 ≤ (43848041330027/100000000000000 : ℝ)^3219 := by
    have hnat : (42800757 : ℕ)^4243*100000000000000^3219 ≤ 43848041330027^3219*80000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42800757 80000000 43848041330027 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092449957/5000000000 : ℝ)^4243 ≤ (2693564071241/20000000000000 : ℝ)^3219 := by
    have hnat : (1092449957 : ℕ)^4243*20000000000000^3219 ≤ 2693564071241^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092449957 5000000000 2693564071241 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32762537/62500000 : ℝ)^4243 ≤ (42684138295301/100000000000000 : ℝ)^3219 := by
    have hnat : (32762537 : ℕ)^4243*100000000000000^3219 ≤ 42684138295301^3219*62500000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32762537 62500000 42684138295301 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42800757/80000000 : ℝ), (-1092449957/5000000000 : ℝ), (32762537/62500000 : ℝ)] ![(43848041330027/100000000000000 : ℝ), (2693564071241/20000000000000 : ℝ), (42684138295301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42800757/80000000 : ℝ)|^4243 ≤ (43848041330027/100000000000000 : ℝ)^3219
        have hw : |(42800757/80000000 : ℝ)|=(42800757/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1092449957/5000000000 : ℝ)|^4243 ≤ (2693564071241/20000000000000 : ℝ)^3219
        have hw : |(-1092449957/5000000000 : ℝ)|=(1092449957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32762537/62500000 : ℝ)|^4243 ≤ (42684138295301/100000000000000 : ℝ)^3219
        have hw : |(32762537/62500000 : ℝ)|=(32762537/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s5_2 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350094741/10000000000 : ℝ)*x 0 + (209680239/400000000 : ℝ)*x 1 + (-2184899687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350094741/10000000000 : ℝ)^4243 ≤ (8769608516633/20000000000000 : ℝ)^3219 := by
    have hnat : (5350094741 : ℕ)^4243*20000000000000^3219 ≤ 8769608516633^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350094741 10000000000 8769608516633 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209680239/400000000 : ℝ)^4243 ≤ (2667758680351/6250000000000 : ℝ)^3219 := by
    have hnat : (209680239 : ℕ)^4243*6250000000000^3219 ≤ 2667758680351^3219*400000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209680239 400000000 2667758680351 6250000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2184899687/10000000000 : ℝ)^4243 ≤ (6733909255927/50000000000000 : ℝ)^3219 := by
    have hnat : (2184899687 : ℕ)^4243*50000000000000^3219 ≤ 6733909255927^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184899687 10000000000 6733909255927 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350094741/10000000000 : ℝ), (209680239/400000000 : ℝ), (-2184899687/10000000000 : ℝ)] ![(8769608516633/20000000000000 : ℝ), (2667758680351/6250000000000 : ℝ), (6733909255927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350094741/10000000000 : ℝ)|^4243 ≤ (8769608516633/20000000000000 : ℝ)^3219
        have hw : |(5350094741/10000000000 : ℝ)|=(5350094741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209680239/400000000 : ℝ)|^4243 ≤ (2667758680351/6250000000000 : ℝ)^3219
        have hw : |(209680239/400000000 : ℝ)|=(209680239/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2184899687/10000000000 : ℝ)|^4243 ≤ (6733909255927/50000000000000 : ℝ)^3219
        have hw : |(-2184899687/10000000000 : ℝ)|=(2184899687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s5_3 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1085560059/2500000000 : ℝ)*x 0 + (416716369/1000000000 : ℝ)*x 1 + (904872833/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085560059/2500000000 : ℝ)^4243 ≤ (2081356993097/6250000000000 : ℝ)^3219 := by
    have hnat : (1085560059 : ℕ)^4243*6250000000000^3219 ≤ 2081356993097^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085560059 2500000000 2081356993097 6250000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (416716369/1000000000 : ℝ)^4243 ≤ (7885833220197/25000000000000 : ℝ)^3219 := by
    have hnat : (416716369 : ℕ)^4243*25000000000000^3219 ≤ 7885833220197^3219*1000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416716369 1000000000 7885833220197 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (904872833/2000000000 : ℝ)^4243 ≤ (35154955215489/100000000000000 : ℝ)^3219 := by
    have hnat : (904872833 : ℕ)^4243*100000000000000^3219 ≤ 35154955215489^3219*2000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904872833 2000000000 35154955215489 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085560059/2500000000 : ℝ), (416716369/1000000000 : ℝ), (904872833/2000000000 : ℝ)] ![(2081356993097/6250000000000 : ℝ), (7885833220197/25000000000000 : ℝ), (35154955215489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085560059/2500000000 : ℝ)|^4243 ≤ (2081356993097/6250000000000 : ℝ)^3219
        have hw : |(1085560059/2500000000 : ℝ)|=(1085560059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(416716369/1000000000 : ℝ)|^4243 ≤ (7885833220197/25000000000000 : ℝ)^3219
        have hw : |(416716369/1000000000 : ℝ)|=(416716369/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(904872833/2000000000 : ℝ)|^4243 ≤ (35154955215489/100000000000000 : ℝ)^3219
        have hw : |(904872833/2000000000 : ℝ)|=(904872833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s5_4 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2095991797/10000000000 : ℝ)*x 0 + (5242631819/10000000000 : ℝ)*x 1 + (270788801/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095991797/10000000000 : ℝ)^4243 ≤ (12750170525097/100000000000000 : ℝ)^3219 := by
    have hnat : (2095991797 : ℕ)^4243*100000000000000^3219 ≤ 12750170525097^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095991797 10000000000 12750170525097 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242631819/10000000000 : ℝ)^4243 ≤ (4269085619587/10000000000000 : ℝ)^3219 := by
    have hnat : (5242631819 : ℕ)^4243*10000000000000^3219 ≤ 4269085619587^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242631819 10000000000 4269085619587 10000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270788801/500000000 : ℝ)^4243 ≤ (44558973255989/100000000000000 : ℝ)^3219 := by
    have hnat : (270788801 : ℕ)^4243*100000000000000^3219 ≤ 44558973255989^3219*500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270788801 500000000 44558973255989 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2095991797/10000000000 : ℝ), (5242631819/10000000000 : ℝ), (270788801/500000000 : ℝ)] ![(12750170525097/100000000000000 : ℝ), (4269085619587/10000000000000 : ℝ), (44558973255989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2095991797/10000000000 : ℝ)|^4243 ≤ (12750170525097/100000000000000 : ℝ)^3219
        have hw : |(-2095991797/10000000000 : ℝ)|=(2095991797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242631819/10000000000 : ℝ)|^4243 ≤ (4269085619587/10000000000000 : ℝ)^3219
        have hw : |(5242631819/10000000000 : ℝ)|=(5242631819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270788801/500000000 : ℝ)|^4243 ≤ (44558973255989/100000000000000 : ℝ)^3219
        have hw : |(270788801/500000000 : ℝ)|=(270788801/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s5_5 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652747659/5000000000 : ℝ)*x 0 + (-402225879/2000000000 : ℝ)*x 1 + (2707888027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652747659/5000000000 : ℝ)^4243 ≤ (43366879038227/100000000000000 : ℝ)^3219 := by
    have hnat : (2652747659 : ℕ)^4243*100000000000000^3219 ≤ 43366879038227^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652747659 5000000000 43366879038227 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402225879/2000000000 : ℝ)^4243 ≤ (6037073659607/50000000000000 : ℝ)^3219 := by
    have hnat : (402225879 : ℕ)^4243*50000000000000^3219 ≤ 6037073659607^3219*2000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402225879 2000000000 6037073659607 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707888027/5000000000 : ℝ)^4243 ≤ (11139743406179/25000000000000 : ℝ)^3219 := by
    have hnat : (2707888027 : ℕ)^4243*25000000000000^3219 ≤ 11139743406179^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707888027 5000000000 11139743406179 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652747659/5000000000 : ℝ), (-402225879/2000000000 : ℝ), (2707888027/5000000000 : ℝ)] ![(43366879038227/100000000000000 : ℝ), (6037073659607/50000000000000 : ℝ), (11139743406179/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652747659/5000000000 : ℝ)|^4243 ≤ (43366879038227/100000000000000 : ℝ)^3219
        have hw : |(2652747659/5000000000 : ℝ)|=(2652747659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-402225879/2000000000 : ℝ)|^4243 ≤ (6037073659607/50000000000000 : ℝ)^3219
        have hw : |(-402225879/2000000000 : ℝ)|=(402225879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707888027/5000000000 : ℝ)|^4243 ≤ (11139743406179/25000000000000 : ℝ)^3219
        have hw : |(2707888027/5000000000 : ℝ)|=(2707888027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s5_6 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331593459/625000000 : ℝ)*x 0 + (216631041/400000000 : ℝ)*x 1 + (-2011129399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331593459/625000000 : ℝ)^4243 ≤ (10841719829589/25000000000000 : ℝ)^3219 := by
    have hnat : (331593459 : ℕ)^4243*25000000000000^3219 ≤ 10841719829589^3219*625000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331593459 625000000 10841719829589 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216631041/400000000 : ℝ)^4243 ≤ (22279486655107/50000000000000 : ℝ)^3219 := by
    have hnat : (216631041 : ℕ)^4243*50000000000000^3219 ≤ 22279486655107^3219*400000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216631041 400000000 22279486655107 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011129399/10000000000 : ℝ)^4243 ≤ (3018536837717/25000000000000 : ℝ)^3219 := by
    have hnat : (2011129399 : ℕ)^4243*25000000000000^3219 ≤ 3018536837717^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011129399 10000000000 3018536837717 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331593459/625000000 : ℝ), (216631041/400000000 : ℝ), (-2011129399/10000000000 : ℝ)] ![(10841719829589/25000000000000 : ℝ), (22279486655107/50000000000000 : ℝ), (3018536837717/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331593459/625000000 : ℝ)|^4243 ≤ (10841719829589/25000000000000 : ℝ)^3219
        have hw : |(331593459/625000000 : ℝ)|=(331593459/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216631041/400000000 : ℝ)|^4243 ≤ (22279486655107/50000000000000 : ℝ)^3219
        have hw : |(216631041/400000000 : ℝ)|=(216631041/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2011129399/10000000000 : ℝ)|^4243 ≤ (3018536837717/25000000000000 : ℝ)^3219
        have hw : |(-2011129399/10000000000 : ℝ)|=(2011129399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s5_7 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4342266039/10000000000 : ℝ)*x 0 + (4523082287/10000000000 : ℝ)*x 1 + (4168453281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342266039/10000000000 : ℝ)^4243 ≤ (6660394546053/20000000000000 : ℝ)^3219 := by
    have hnat : (4342266039 : ℕ)^4243*20000000000000^3219 ≤ 6660394546053^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342266039 10000000000 6660394546053 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4523082287/10000000000 : ℝ)^4243 ≤ (35141826925199/100000000000000 : ℝ)^3219 := by
    have hnat : (4523082287 : ℕ)^4243*100000000000000^3219 ≤ 35141826925199^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523082287 10000000000 35141826925199 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4168453281/10000000000 : ℝ)^4243 ≤ (7889050082349/25000000000000 : ℝ)^3219 := by
    have hnat : (4168453281 : ℕ)^4243*25000000000000^3219 ≤ 7889050082349^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168453281 10000000000 7889050082349 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342266039/10000000000 : ℝ), (4523082287/10000000000 : ℝ), (4168453281/10000000000 : ℝ)] ![(6660394546053/20000000000000 : ℝ), (35141826925199/100000000000000 : ℝ), (7889050082349/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342266039/10000000000 : ℝ)|^4243 ≤ (6660394546053/20000000000000 : ℝ)^3219
        have hw : |(4342266039/10000000000 : ℝ)|=(4342266039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4523082287/10000000000 : ℝ)|^4243 ≤ (35141826925199/100000000000000 : ℝ)^3219
        have hw : |(4523082287/10000000000 : ℝ)|=(4523082287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4168453281/10000000000 : ℝ)|^4243 ≤ (7889050082349/25000000000000 : ℝ)^3219
        have hw : |(4168453281/10000000000 : ℝ)|=(4168453281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1283_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10927/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1099/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14681/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10927/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10927/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10927/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10927/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10927/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10927/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10927/100000 : ℝ) ^ (2121/512 : ℝ) ≤ (10397167476074311/100000000000000000000 : ℝ) := by
    have hpowers : (10927/100000 : ℝ)^2121 ≤ (10397167476074311/100000000000000000000 : ℝ)^512 := by
      have hnat : (10927 : ℕ)^2121*100000000000000000000^512 ≤ 10397167476074311^512*100000^2121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10927 100000 10397167476074311 100000000000000000000 2121 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10927/100000 : ℝ)) (X := (10397167476074311/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14749/100000 : ℝ) ^ (2121/512 : ℝ) ≤ (4502399651095753/12500000000000000000 : ℝ) := by
    have hpowers : (14749/100000 : ℝ)^2121 ≤ (4502399651095753/12500000000000000000 : ℝ)^512 := by
      have hnat : (14749 : ℕ)^2121*12500000000000000000^512 ≤ 4502399651095753^512*100000^2121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14749 100000 4502399651095753 12500000000000000000 2121 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14749/100000 : ℝ)) (X := (4502399651095753/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010397167476074311/50000000000000000000 : ℝ) ≤ (5000250963221517/5000000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (50010397167476074311/50000000000000000000 : ℝ)^512 ≤ (5000250963221517/5000000000000000 : ℝ)^2121 := by
      have hnat : (50010397167476074311 : ℕ)^512*5000000000000000^2121 ≤ 5000250963221517^2121*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010397167476074311 50000000000000000000 5000250963221517 5000000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000250963221517/5000000000000000 : ℝ)) (X := (50010397167476074311/50000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009283272936968067/20000000000000000000 : ℝ) ≤ (10001120273257887/10000000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (20009283272936968067/20000000000000000000 : ℝ)^512 ≤ (10001120273257887/10000000000000000 : ℝ)^2121 := by
      have hnat : (20009283272936968067 : ℕ)^512*10000000000000000^2121 ≤ 10001120273257887^2121*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009283272936968067 20000000000000000000 10001120273257887 10000000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001120273257887/10000000000000000 : ℝ)) (X := (20009283272936968067/20000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254502399651095753/6250000000000000000 : ℝ) ≤ (500086931003637/500000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (6254502399651095753/6250000000000000000 : ℝ)^512 ≤ (500086931003637/500000000000000 : ℝ)^2121 := by
      have hnat : (6254502399651095753 : ℕ)^512*500000000000000^2121 ≤ 500086931003637^2121*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254502399651095753 6250000000000000000 500086931003637 500000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500086931003637/500000000000000 : ℝ)) (X := (6254502399651095753/6250000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10397167476074311/100000000000000000000 : ℝ) ≤ ((129960561263855369/130000000000000000 : ℝ)+2*(206115604951/127400000000000 : ℝ)*(10927/100000 : ℝ))^(2121/512 : ℝ) := by
    rw [show (129960561263855369/130000000000000000 : ℝ)+2*(206115604951/127400000000000 : ℝ)*(10927/100000 : ℝ)=(5000250963221517/5000000000000000 : ℝ) by norm_num, show 1+2*(10397167476074311/100000000000000000000 : ℝ)=(50010397167476074311/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4502399651095753/12500000000000000000 : ℝ)+(10397167476074311/100000000000000000000 : ℝ) ≤ ((129960561263855369/130000000000000000 : ℝ)+(206115604951/127400000000000 : ℝ)*((14749/100000 : ℝ)+(10927/100000 : ℝ)))^(2121/512 : ℝ) := by
    rw [show (129960561263855369/130000000000000000 : ℝ)+(206115604951/127400000000000 : ℝ)*((14749/100000 : ℝ)+(10927/100000 : ℝ))=(10001120273257887/10000000000000000 : ℝ) by norm_num, show 1+(4502399651095753/12500000000000000000 : ℝ)+(10397167476074311/100000000000000000000 : ℝ)=(20009283272936968067/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4502399651095753/12500000000000000000 : ℝ) ≤ ((129960561263855369/130000000000000000 : ℝ)+2*(206115604951/127400000000000 : ℝ)*(14749/100000 : ℝ))^(2121/512 : ℝ) := by
    rw [show (129960561263855369/130000000000000000 : ℝ)+2*(206115604951/127400000000000 : ℝ)*(14749/100000 : ℝ)=(500086931003637/500000000000000 : ℝ) by norm_num, show 1+2*(4502399651095753/12500000000000000000 : ℝ)=(6254502399651095753/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (129960561263855369/130000000000000000 : ℝ)*(X 1 0+X 2 0)+(206115604951/127400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (10927/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (129960561263855369/130000000000000000 : ℝ)) (alpha := (206115604951/127400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (129960561263855369/130000000000000000 : ℝ)*(X 0 1+X 2 1)+(206115604951/127400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (10927/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (129960561263855369/130000000000000000 : ℝ)) (alpha := (206115604951/127400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (129960561263855369/130000000000000000 : ℝ)*(X 0 2+X 1 2)+(206115604951/127400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (10927/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (129960561263855369/130000000000000000 : ℝ)) (alpha := (206115604951/127400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1047989591/5000000000 : ℝ)*X 0 0+(1083280969/2000000000 : ℝ)*X 0 1+(5242005861/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((42800757/80000000 : ℝ)*X 1 0+(-1092449957/5000000000 : ℝ)*X 1 1+(32762537/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350094741/10000000000 : ℝ)*X 2 0+(209680239/400000000 : ℝ)*X 2 1+(-2184899687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1085560059/2500000000 : ℝ)*X 0 0+(416716369/1000000000 : ℝ)*X 0 1+(904872833/2000000000 : ℝ)*X 0 2+(1085560059/2500000000 : ℝ)*X 1 0+(416716369/1000000000 : ℝ)*X 1 1+(904872833/2000000000 : ℝ)*X 1 2+(1085560059/2500000000 : ℝ)*X 2 0+(416716369/1000000000 : ℝ)*X 2 1+(904872833/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2095991797/10000000000 : ℝ)*X 0 0+(5242631819/10000000000 : ℝ)*X 0 1+(270788801/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652747659/5000000000 : ℝ)*X 1 0+(-402225879/2000000000 : ℝ)*X 1 1+(2707888027/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331593459/625000000 : ℝ)*X 2 0+(216631041/400000000 : ℝ)*X 2 1+(-2011129399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4342266039/10000000000 : ℝ)*X 0 0+(4523082287/10000000000 : ℝ)*X 0 1+(4168453281/10000000000 : ℝ)*X 0 2+(4342266039/10000000000 : ℝ)*X 1 0+(4523082287/10000000000 : ℝ)*X 1 1+(4168453281/10000000000 : ℝ)*X 1 2+(4342266039/10000000000 : ℝ)*X 2 0+(4523082287/10000000000 : ℝ)*X 2 1+(4168453281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (622351857323847930004598091/79625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (518884597/25000000000000 : ℝ)*(base19) + (129908521/6250000000000 : ℝ)*(base23) + (32455477/50000000000000 : ℝ)*(lower2) + (365219459/100000000000000 : ℝ)*(upper3) + (565656109/100000000000000 : ℝ)*(upper5) + (1066704502107737/25000000000000 : ℝ)*(major0) + (1066704502107737/25000000000000 : ℝ)*(major1) + (1066704502107737/25000000000000 : ℝ)*(major2) + (5734006243679779/100000000000000 : ℝ)*(sp0) + (2867020963933047/50000000000000 : ℝ)*(sp1) + (2867020962434073/50000000000000 : ℝ)*(sp2) + (279957095052319/10000000000000 : ℝ)*(sp3) + (37759724703/100000000000000 : ℝ)*(sp4) + (20802399687/100000000000000 : ℝ)*(sp7) + (2799591752922877/100000000000000 : ℝ)*(f.failure) + (2867022001702241/50000000000000 : ℝ)*(f.sum) + (5500599557717/1592500000000000000000000000 : ℝ)*base65 + (871475771734292303/159250000000000000000000000000000 : ℝ)*base68 + (1003995164763042303/159250000000000000000000000000000 : ℝ)*base70 + (1702230665522207697/159250000000000000000000000000000 : ℝ)*base71 + (7363550772469/3185000000000000000000000000 : ℝ)*base73 + (1590205514647292303/159250000000000000000000000000000 : ℝ)*base76 + (1133036497660792303/159250000000000000000000000000000 : ℝ)*base78 + (1965257482939207697/159250000000000000000000000000000 : ℝ)*base79 + (23850895194199/3185000000000000000000000000 : ℝ)*base81 + (19838217/10000000000000000000000 : ℝ)*base90 + (19838217/10000000000000000000000 : ℝ)*base92 + (19838217/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13134013134940848123092601/2275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49509111/5000000000000 : ℝ)*(base19) + (553536599/50000000000000 : ℝ)*(base23) + (118515671/100000000000000 : ℝ)*(upper3) + (40926641/100000000000000 : ℝ)*(lower4) + (125832111/100000000000000 : ℝ)*(upper5) + (429769030492851/10000000000000 : ℝ)*(major0) + (429769030492851/10000000000000 : ℝ)*(major1) + (429769030492851/10000000000000 : ℝ)*(major2) + (20431752947/100000000000000 : ℝ)*(sp1) + (10896743161/50000000000000 : ℝ)*(sp2) + (288776619618683/5000000000000 : ℝ)*(sp4) + (2887755485219247/50000000000000 : ℝ)*(sp5) + (288775474590707/5000000000000 : ℝ)*(sp6) + (704962006260899/25000000000000 : ℝ)*(sp7) + (704962006260899/25000000000000 : ℝ)*(f.failure) + (288776619618683/5000000000000 : ℝ)*(f.sum) + (570761215659/91000000000000000000000000 : ℝ)*base65 + (36624820432219133/9100000000000000000000000000000 : ℝ)*base67 + (13995750332180867/9100000000000000000000000000000 : ℝ)*base70 + (85438625299319133/9100000000000000000000000000000 : ℝ)*base71 + (416831335919/91000000000000000000000000 : ℝ)*base73 + (48531844652219133/9100000000000000000000000000000 : ℝ)*base75 + (13781441564819133/9100000000000000000000000000000 : ℝ)*base77 + (70119373251219133/9100000000000000000000000000000 : ℝ)*base79 + (38103073461/91000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (30147479/2500000000000000000000 : ℝ)*base90 + (30147479/2500000000000000000000 : ℝ)*base92 + (30147479/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1283_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10927/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1099/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1283_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1283_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4719/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1099/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1283_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1283_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1283_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4719/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1099/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1283_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

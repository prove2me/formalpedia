-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1276_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:44.13552+00:00
-- url     : https://prove2.me/submissions/e6331bdc-5435-45a4-96f9-a42045da2946

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
theorem support_rectangle_w1276_box_0 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-192969897/1000000000 : ℝ)*x 0 + (2696332853/5000000000 : ℝ)*x 1 + (5392665741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (192969897/1000000000 : ℝ)^1059 ≤ (11420902791859/100000000000000 : ℝ)^803 := by
    have hnat : (192969897 : ℕ)^1059*100000000000000^803 ≤ 11420902791859^803*1000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192969897 1000000000 11420902791859 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696332853/5000000000 : ℝ)^1059 ≤ (44289548409197/100000000000000 : ℝ)^803 := by
    have hnat : (2696332853 : ℕ)^1059*100000000000000^803 ≤ 44289548409197^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696332853 5000000000 44289548409197 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392665741/10000000000 : ℝ)^1059 ≤ (4428954878829/10000000000000 : ℝ)^803 := by
    have hnat : (5392665741 : ℕ)^1059*10000000000000^803 ≤ 4428954878829^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392665741 10000000000 4428954878829 10000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-192969897/1000000000 : ℝ), (2696332853/5000000000 : ℝ), (5392665741/10000000000 : ℝ)] ![(11420902791859/100000000000000 : ℝ), (44289548409197/100000000000000 : ℝ), (4428954878829/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-192969897/1000000000 : ℝ)|^1059 ≤ (11420902791859/100000000000000 : ℝ)^803
        have hw : |(-192969897/1000000000 : ℝ)|=(192969897/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696332853/5000000000 : ℝ)|^1059 ≤ (44289548409197/100000000000000 : ℝ)^803
        have hw : |(2696332853/5000000000 : ℝ)|=(2696332853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392665741/10000000000 : ℝ)|^1059 ≤ (4428954878829/10000000000000 : ℝ)^803
        have hw : |(5392665741/10000000000 : ℝ)|=(5392665741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_box_1 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2642033683/5000000000 : ℝ)*x 0 + (-103906117/500000000 : ℝ)*x 1 + (5392666169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642033683/5000000000 : ℝ)^1059 ≤ (43117087025159/100000000000000 : ℝ)^803 := by
    have hnat : (2642033683 : ℕ)^1059*100000000000000^803 ≤ 43117087025159^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642033683 5000000000 43117087025159 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103906117/500000000 : ℝ)^1059 ≤ (6296679765091/50000000000000 : ℝ)^803 := by
    have hnat : (103906117 : ℕ)^1059*50000000000000^803 ≤ 6296679765091^803*500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103906117 500000000 6296679765091 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392666169/10000000000 : ℝ)^1059 ≤ (44289553424061/100000000000000 : ℝ)^803 := by
    have hnat : (5392666169 : ℕ)^1059*100000000000000^803 ≤ 44289553424061^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392666169 10000000000 44289553424061 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642033683/5000000000 : ℝ), (-103906117/500000000 : ℝ), (5392666169/10000000000 : ℝ)] ![(43117087025159/100000000000000 : ℝ), (6296679765091/50000000000000 : ℝ), (44289553424061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642033683/5000000000 : ℝ)|^1059 ≤ (43117087025159/100000000000000 : ℝ)^803
        have hw : |(2642033683/5000000000 : ℝ)|=(2642033683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103906117/500000000 : ℝ)|^1059 ≤ (6296679765091/50000000000000 : ℝ)^803
        have hw : |(-103906117/500000000 : ℝ)|=(103906117/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392666169/10000000000 : ℝ)|^1059 ≤ (44289553424061/100000000000000 : ℝ)^803
        have hw : |(5392666169/10000000000 : ℝ)|=(5392666169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_box_2 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2642033997/5000000000 : ℝ)*x 0 + (1078533141/2000000000 : ℝ)*x 1 + (-519530531/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642033997/5000000000 : ℝ)^1059 ≤ (8623418756641/20000000000000 : ℝ)^803 := by
    have hnat : (2642033997 : ℕ)^1059*20000000000000^803 ≤ 8623418756641^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642033997 5000000000 8623418756641 20000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078533141/2000000000 : ℝ)^1059 ≤ (22144774199183/50000000000000 : ℝ)^803 := by
    have hnat : (1078533141 : ℕ)^1059*50000000000000^803 ≤ 22144774199183^803*2000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078533141 2000000000 22144774199183 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519530531/2500000000 : ℝ)^1059 ≤ (12593357803929/100000000000000 : ℝ)^803 := by
    have hnat : (519530531 : ℕ)^1059*100000000000000^803 ≤ 12593357803929^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519530531 2500000000 12593357803929 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642033997/5000000000 : ℝ), (1078533141/2000000000 : ℝ), (-519530531/2500000000 : ℝ)] ![(8623418756641/20000000000000 : ℝ), (22144774199183/50000000000000 : ℝ), (12593357803929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642033997/5000000000 : ℝ)|^1059 ≤ (8623418756641/20000000000000 : ℝ)^803
        have hw : |(2642033997/5000000000 : ℝ)|=(2642033997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078533141/2000000000 : ℝ)|^1059 ≤ (22144774199183/50000000000000 : ℝ)^803
        have hw : |(1078533141/2000000000 : ℝ)|=(1078533141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-519530531/2500000000 : ℝ)|^1059 ≤ (12593357803929/100000000000000 : ℝ)^803
        have hw : |(-519530531/2500000000 : ℝ)|=(519530531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_box_3 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4494022463/10000000000 : ℝ)*x 0 + (4273303829/10000000000 : ℝ)*x 1 + (2136651989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4494022463/10000000000 : ℝ)^1059 ≤ (3482521415179/10000000000000 : ℝ)^803 := by
    have hnat : (4494022463 : ℕ)^1059*10000000000000^803 ≤ 3482521415179^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494022463 10000000000 3482521415179 10000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4273303829/10000000000 : ℝ)^1059 ≤ (1629369608431/5000000000000 : ℝ)^803 := by
    have hnat : (4273303829 : ℕ)^1059*5000000000000^803 ≤ 1629369608431^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273303829 10000000000 1629369608431 5000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2136651989/5000000000 : ℝ)^1059 ≤ (6517478733421/20000000000000 : ℝ)^803 := by
    have hnat : (2136651989 : ℕ)^1059*20000000000000^803 ≤ 6517478733421^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136651989 5000000000 6517478733421 20000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4494022463/10000000000 : ℝ), (4273303829/10000000000 : ℝ), (2136651989/5000000000 : ℝ)] ![(3482521415179/10000000000000 : ℝ), (1629369608431/5000000000000 : ℝ), (6517478733421/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4494022463/10000000000 : ℝ)|^1059 ≤ (3482521415179/10000000000000 : ℝ)^803
        have hw : |(4494022463/10000000000 : ℝ)|=(4494022463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4273303829/10000000000 : ℝ)|^1059 ≤ (1629369608431/5000000000000 : ℝ)^803
        have hw : |(4273303829/10000000000 : ℝ)|=(4273303829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2136651989/5000000000 : ℝ)|^1059 ≤ (6517478733421/20000000000000 : ℝ)^803
        have hw : |(2136651989/5000000000 : ℝ)|=(2136651989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_box_4 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-284733121/1250000000 : ℝ)*x 0 + (1315812123/2500000000 : ℝ)*x 1 + (5263247279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (284733121/1250000000 : ℝ)^1059 ≤ (7106815127353/50000000000000 : ℝ)^803 := by
    have hnat : (284733121 : ℕ)^1059*50000000000000^803 ≤ 7106815127353^803*1250000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284733121 1250000000 7106815127353 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315812123/2500000000 : ℝ)^1059 ≤ (42893191385321/100000000000000 : ℝ)^803 := by
    have hnat : (1315812123 : ℕ)^1059*100000000000000^803 ≤ 42893191385321^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315812123 2500000000 42893191385321 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263247279/10000000000 : ℝ)^1059 ≤ (2144658917419/5000000000000 : ℝ)^803 := by
    have hnat : (5263247279 : ℕ)^1059*5000000000000^803 ≤ 2144658917419^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263247279 10000000000 2144658917419 5000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-284733121/1250000000 : ℝ), (1315812123/2500000000 : ℝ), (5263247279/10000000000 : ℝ)] ![(7106815127353/50000000000000 : ℝ), (42893191385321/100000000000000 : ℝ), (2144658917419/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-284733121/1250000000 : ℝ)|^1059 ≤ (7106815127353/50000000000000 : ℝ)^803
        have hw : |(-284733121/1250000000 : ℝ)|=(284733121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315812123/2500000000 : ℝ)|^1059 ≤ (42893191385321/100000000000000 : ℝ)^803
        have hw : |(1315812123/2500000000 : ℝ)|=(1315812123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263247279/10000000000 : ℝ)|^1059 ≤ (2144658917419/5000000000000 : ℝ)^803
        have hw : |(5263247279/10000000000 : ℝ)|=(5263247279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_box_5 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2687613091/5000000000 : ℝ)*x 0 + (-1064780117/5000000000 : ℝ)*x 1 + (657905999/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687613091/5000000000 : ℝ)^1059 ≤ (11025188547169/25000000000000 : ℝ)^803 := by
    have hnat : (2687613091 : ℕ)^1059*25000000000000^803 ≤ 11025188547169^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687613091 5000000000 11025188547169 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1064780117/5000000000 : ℝ)^1059 ≤ (13006059793241/100000000000000 : ℝ)^803 := by
    have hnat : (1064780117 : ℕ)^1059*100000000000000^803 ≤ 13006059793241^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064780117 5000000000 13006059793241 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657905999/1250000000 : ℝ)^1059 ≤ (42893186011479/100000000000000 : ℝ)^803 := by
    have hnat : (657905999 : ℕ)^1059*100000000000000^803 ≤ 42893186011479^803*1250000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657905999 1250000000 42893186011479 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687613091/5000000000 : ℝ), (-1064780117/5000000000 : ℝ), (657905999/1250000000 : ℝ)] ![(11025188547169/25000000000000 : ℝ), (13006059793241/100000000000000 : ℝ), (42893186011479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687613091/5000000000 : ℝ)|^1059 ≤ (11025188547169/25000000000000 : ℝ)^803
        have hw : |(2687613091/5000000000 : ℝ)|=(2687613091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1064780117/5000000000 : ℝ)|^1059 ≤ (13006059793241/100000000000000 : ℝ)^803
        have hw : |(-1064780117/5000000000 : ℝ)|=(1064780117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657905999/1250000000 : ℝ)|^1059 ≤ (42893186011479/100000000000000 : ℝ)^803
        have hw : |(657905999/1250000000 : ℝ)|=(657905999/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_box_6 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5375224831/10000000000 : ℝ)*x 0 + (5263249067/10000000000 : ℝ)*x 1 + (-1064780307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375224831/10000000000 : ℝ)^1059 ≤ (22050369785387/50000000000000 : ℝ)^803 := by
    have hnat : (5375224831 : ℕ)^1059*50000000000000^803 ≤ 22050369785387^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375224831 10000000000 22050369785387 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263249067/10000000000 : ℝ)^1059 ≤ (1072329939131/2500000000000 : ℝ)^803 := by
    have hnat : (5263249067 : ℕ)^1059*2500000000000^803 ≤ 1072329939131^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263249067 10000000000 1072329939131 2500000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1064780307/5000000000 : ℝ)^1059 ≤ (6503031426967/50000000000000 : ℝ)^803 := by
    have hnat : (1064780307 : ℕ)^1059*50000000000000^803 ≤ 6503031426967^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064780307 5000000000 6503031426967 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375224831/10000000000 : ℝ), (5263249067/10000000000 : ℝ), (-1064780307/5000000000 : ℝ)] ![(22050369785387/50000000000000 : ℝ), (1072329939131/2500000000000 : ℝ), (6503031426967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375224831/10000000000 : ℝ)|^1059 ≤ (22050369785387/50000000000000 : ℝ)^803
        have hw : |(5375224831/10000000000 : ℝ)|=(5375224831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263249067/10000000000 : ℝ)|^1059 ≤ (1072329939131/2500000000000 : ℝ)^803
        have hw : |(5263249067/10000000000 : ℝ)|=(5263249067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1064780307/5000000000 : ℝ)|^1059 ≤ (6503031426967/50000000000000 : ℝ)^803
        have hw : |(-1064780307/5000000000 : ℝ)|=(1064780307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_box_7 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (838702767/2000000000 : ℝ)*x 0 + (2211750861/5000000000 : ℝ)*x 1 + (442350279/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838702767/2000000000 : ℝ)^1059 ≤ (7946836699283/25000000000000 : ℝ)^803 := by
    have hnat : (838702767 : ℕ)^1059*25000000000000^803 ≤ 7946836699283^803*2000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838702767 2000000000 7946836699283 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2211750861/5000000000 : ℝ)^1059 ≤ (34106321167969/100000000000000 : ℝ)^803 := by
    have hnat : (2211750861 : ℕ)^1059*100000000000000^803 ≤ 34106321167969^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211750861 5000000000 34106321167969 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442350279/1000000000 : ℝ)^1059 ≤ (8526583006933/25000000000000 : ℝ)^803 := by
    have hnat : (442350279 : ℕ)^1059*25000000000000^803 ≤ 8526583006933^803*1000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442350279 1000000000 8526583006933 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(838702767/2000000000 : ℝ), (2211750861/5000000000 : ℝ), (442350279/1000000000 : ℝ)] ![(7946836699283/25000000000000 : ℝ), (34106321167969/100000000000000 : ℝ), (8526583006933/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(838702767/2000000000 : ℝ)|^1059 ≤ (7946836699283/25000000000000 : ℝ)^803
        have hw : |(838702767/2000000000 : ℝ)|=(838702767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2211750861/5000000000 : ℝ)|^1059 ≤ (34106321167969/100000000000000 : ℝ)^803
        have hw : |(2211750861/5000000000 : ℝ)|=(2211750861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(442350279/1000000000 : ℝ)|^1059 ≤ (8526583006933/25000000000000 : ℝ)^803
        have hw : |(442350279/1000000000 : ℝ)|=(442350279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_box_8 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-220494037/1000000000 : ℝ)*x 0 + (1034895501/2000000000 : ℝ)*x 1 + (1351677111/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220494037/1000000000 : ℝ)^1059 ≤ (13616604417959/100000000000000 : ℝ)^803 := by
    have hnat : (220494037 : ℕ)^1059*100000000000000^803 ≤ 13616604417959^803*1000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220494037 1000000000 13616604417959 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034895501/2000000000 : ℝ)^1059 ≤ (41941683797381/100000000000000 : ℝ)^803 := by
    have hnat : (1034895501 : ℕ)^1059*100000000000000^803 ≤ 41941683797381^803*2000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034895501 2000000000 41941683797381 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351677111/2500000000 : ℝ)^1059 ≤ (694401746389/1562500000000 : ℝ)^803 := by
    have hnat : (1351677111 : ℕ)^1059*1562500000000^803 ≤ 694401746389^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351677111 2500000000 694401746389 1562500000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220494037/1000000000 : ℝ), (1034895501/2000000000 : ℝ), (1351677111/2500000000 : ℝ)] ![(13616604417959/100000000000000 : ℝ), (41941683797381/100000000000000 : ℝ), (694401746389/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220494037/1000000000 : ℝ)|^1059 ≤ (13616604417959/100000000000000 : ℝ)^803
        have hw : |(-220494037/1000000000 : ℝ)|=(220494037/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1034895501/2000000000 : ℝ)|^1059 ≤ (41941683797381/100000000000000 : ℝ)^803
        have hw : |(1034895501/2000000000 : ℝ)|=(1034895501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351677111/2500000000 : ℝ)|^1059 ≤ (694401746389/1562500000000 : ℝ)^803
        have hw : |(1351677111/2500000000 : ℝ)|=(1351677111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_box_9 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1054834039/2000000000 : ℝ)*x 0 + (-1036202023/5000000000 : ℝ)*x 1 + (2703354017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054834039/2000000000 : ℝ)^1059 ≤ (43010613209933/100000000000000 : ℝ)^803 := by
    have hnat : (1054834039 : ℕ)^1059*100000000000000^803 ≤ 43010613209933^803*2000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054834039 2000000000 43010613209933 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036202023/5000000000 : ℝ)^1059 ≤ (2509535892587/20000000000000 : ℝ)^803 := by
    have hnat : (1036202023 : ℕ)^1059*20000000000000^803 ≤ 2509535892587^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036202023 5000000000 2509535892587 20000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703354017/5000000000 : ℝ)^1059 ≤ (11110426831101/25000000000000 : ℝ)^803 := by
    have hnat : (2703354017 : ℕ)^1059*25000000000000^803 ≤ 11110426831101^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703354017 5000000000 11110426831101 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054834039/2000000000 : ℝ), (-1036202023/5000000000 : ℝ), (2703354017/5000000000 : ℝ)] ![(43010613209933/100000000000000 : ℝ), (2509535892587/20000000000000 : ℝ), (11110426831101/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054834039/2000000000 : ℝ)|^1059 ≤ (43010613209933/100000000000000 : ℝ)^803
        have hw : |(1054834039/2000000000 : ℝ)|=(1054834039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1036202023/5000000000 : ℝ)|^1059 ≤ (2509535892587/20000000000000 : ℝ)^803
        have hw : |(-1036202023/5000000000 : ℝ)|=(1036202023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703354017/5000000000 : ℝ)|^1059 ≤ (11110426831101/25000000000000 : ℝ)^803
        have hw : |(2703354017/5000000000 : ℝ)|=(2703354017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_box_10 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1054833967/2000000000 : ℝ)*x 0 + (2703354301/5000000000 : ℝ)*x 1 + (-1036201879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054833967/2000000000 : ℝ)^1059 ≤ (43010609338209/100000000000000 : ℝ)^803 := by
    have hnat : (1054833967 : ℕ)^1059*100000000000000^803 ≤ 43010609338209^803*2000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054833967 2000000000 43010609338209 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703354301/5000000000 : ℝ)^1059 ≤ (44441713481651/100000000000000 : ℝ)^803 := by
    have hnat : (2703354301 : ℕ)^1059*100000000000000^803 ≤ 44441713481651^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703354301 5000000000 44441713481651 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036201879/5000000000 : ℝ)^1059 ≤ (2509535432657/20000000000000 : ℝ)^803 := by
    have hnat : (1036201879 : ℕ)^1059*20000000000000^803 ≤ 2509535432657^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036201879 5000000000 2509535432657 20000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054833967/2000000000 : ℝ), (2703354301/5000000000 : ℝ), (-1036201879/5000000000 : ℝ)] ![(43010609338209/100000000000000 : ℝ), (44441713481651/100000000000000 : ℝ), (2509535432657/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054833967/2000000000 : ℝ)|^1059 ≤ (43010609338209/100000000000000 : ℝ)^803
        have hw : |(1054833967/2000000000 : ℝ)|=(1054833967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703354301/5000000000 : ℝ)|^1059 ≤ (44441713481651/100000000000000 : ℝ)^803
        have hw : |(2703354301/5000000000 : ℝ)|=(2703354301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1036201879/5000000000 : ℝ)|^1059 ≤ (2509535432657/20000000000000 : ℝ)^803
        have hw : |(-1036201879/5000000000 : ℝ)|=(1036201879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_box_11 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (565758373/1250000000 : ℝ)*x 0 + (2128497469/5000000000 : ℝ)*x 1 + (4256992897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (565758373/1250000000 : ℝ)^1059 ≤ (35153071789029/100000000000000 : ℝ)^803 := by
    have hnat : (565758373 : ℕ)^1059*100000000000000^803 ≤ 35153071789029^803*1250000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565758373 1250000000 35153071789029 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2128497469/5000000000 : ℝ)^1059 ≤ (32423474349883/100000000000000 : ℝ)^803 := by
    have hnat : (2128497469 : ℕ)^1059*100000000000000^803 ≤ 32423474349883^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128497469 5000000000 32423474349883 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4256992897/10000000000 : ℝ)^1059 ≤ (16211726924329/50000000000000 : ℝ)^803 := by
    have hnat : (4256992897 : ℕ)^1059*50000000000000^803 ≤ 16211726924329^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256992897 10000000000 16211726924329 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(565758373/1250000000 : ℝ), (2128497469/5000000000 : ℝ), (4256992897/10000000000 : ℝ)] ![(35153071789029/100000000000000 : ℝ), (32423474349883/100000000000000 : ℝ), (16211726924329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(565758373/1250000000 : ℝ)|^1059 ≤ (35153071789029/100000000000000 : ℝ)^803
        have hw : |(565758373/1250000000 : ℝ)|=(565758373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2128497469/5000000000 : ℝ)|^1059 ≤ (32423474349883/100000000000000 : ℝ)^803
        have hw : |(2128497469/5000000000 : ℝ)|=(2128497469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4256992897/10000000000 : ℝ)|^1059 ≤ (16211726924329/50000000000000 : ℝ)^803
        have hw : |(4256992897/10000000000 : ℝ)|=(4256992897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_box_12 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-62596753/312500000 : ℝ)*x 0 + (5479072563/10000000000 : ℝ)*x 1 + (1050448483/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (62596753/312500000 : ℝ)^1059 ≤ (5998617734733/50000000000000 : ℝ)^803 := by
    have hnat : (62596753 : ℕ)^1059*50000000000000^803 ≤ 5998617734733^803*312500000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62596753 312500000 5998617734733 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5479072563/10000000000 : ℝ)^1059 ≤ (9045564704859/20000000000000 : ℝ)^803 := by
    have hnat : (5479072563 : ℕ)^1059*20000000000000^803 ≤ 9045564704859^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479072563 10000000000 9045564704859 20000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050448483/2000000000 : ℝ)^1059 ≤ (21387470496349/50000000000000 : ℝ)^803 := by
    have hnat : (1050448483 : ℕ)^1059*50000000000000^803 ≤ 21387470496349^803*2000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050448483 2000000000 21387470496349 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-62596753/312500000 : ℝ), (5479072563/10000000000 : ℝ), (1050448483/2000000000 : ℝ)] ![(5998617734733/50000000000000 : ℝ), (9045564704859/20000000000000 : ℝ), (21387470496349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-62596753/312500000 : ℝ)|^1059 ≤ (5998617734733/50000000000000 : ℝ)^803
        have hw : |(-62596753/312500000 : ℝ)|=(62596753/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5479072563/10000000000 : ℝ)|^1059 ≤ (9045564704859/20000000000000 : ℝ)^803
        have hw : |(5479072563/10000000000 : ℝ)|=(5479072563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050448483/2000000000 : ℝ)|^1059 ≤ (21387470496349/50000000000000 : ℝ)^803
        have hw : |(1050448483/2000000000 : ℝ)|=(1050448483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_box_13 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1345743789/2500000000 : ℝ)*x 0 + (-533456931/2500000000 : ℝ)*x 1 + (5252242237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345743789/2500000000 : ℝ)^1059 ≤ (44184617816717/100000000000000 : ℝ)^803 := by
    have hnat : (1345743789 : ℕ)^1059*100000000000000^803 ≤ 44184617816717^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345743789 2500000000 44184617816717 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (533456931/2500000000 : ℝ)^1059 ≤ (3260110769947/25000000000000 : ℝ)^803 := by
    have hnat : (533456931 : ℕ)^1059*25000000000000^803 ≤ 3260110769947^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533456931 2500000000 3260110769947 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252242237/10000000000 : ℝ)^1059 ≤ (42774939080887/100000000000000 : ℝ)^803 := by
    have hnat : (5252242237 : ℕ)^1059*100000000000000^803 ≤ 42774939080887^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252242237 10000000000 42774939080887 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345743789/2500000000 : ℝ), (-533456931/2500000000 : ℝ), (5252242237/10000000000 : ℝ)] ![(44184617816717/100000000000000 : ℝ), (3260110769947/25000000000000 : ℝ), (42774939080887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345743789/2500000000 : ℝ)|^1059 ≤ (44184617816717/100000000000000 : ℝ)^803
        have hw : |(1345743789/2500000000 : ℝ)|=(1345743789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-533456931/2500000000 : ℝ)|^1059 ≤ (3260110769947/25000000000000 : ℝ)^803
        have hw : |(-533456931/2500000000 : ℝ)|=(533456931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252242237/10000000000 : ℝ)|^1059 ≤ (42774939080887/100000000000000 : ℝ)^803
        have hw : |(5252242237/10000000000 : ℝ)|=(5252242237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_box_14 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (215318999/400000000 : ℝ)*x 0 + (5252242651/10000000000 : ℝ)*x 1 + (-266728427/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215318999/400000000 : ℝ)^1059 ≤ (44184615857387/100000000000000 : ℝ)^803 := by
    have hnat : (215318999 : ℕ)^1059*100000000000000^803 ≤ 44184615857387^803*400000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215318999 400000000 44184615857387 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252242651/10000000000 : ℝ)^1059 ≤ (2138747176373/5000000000000 : ℝ)^803 := by
    have hnat : (5252242651 : ℕ)^1059*5000000000000^803 ≤ 2138747176373^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252242651 10000000000 2138747176373 5000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266728427/1250000000 : ℝ)^1059 ≤ (1630055074679/12500000000000 : ℝ)^803 := by
    have hnat : (266728427 : ℕ)^1059*12500000000000^803 ≤ 1630055074679^803*1250000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266728427 1250000000 1630055074679 12500000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215318999/400000000 : ℝ), (5252242651/10000000000 : ℝ), (-266728427/1250000000 : ℝ)] ![(44184615857387/100000000000000 : ℝ), (2138747176373/5000000000000 : ℝ), (1630055074679/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215318999/400000000 : ℝ)|^1059 ≤ (44184615857387/100000000000000 : ℝ)^803
        have hw : |(215318999/400000000 : ℝ)|=(215318999/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252242651/10000000000 : ℝ)|^1059 ≤ (2138747176373/5000000000000 : ℝ)^803
        have hw : |(5252242651/10000000000 : ℝ)|=(5252242651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-266728427/1250000000 : ℝ)|^1059 ≤ (1630055074679/12500000000000 : ℝ)^803
        have hw : |(-266728427/1250000000 : ℝ)|=(266728427/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_box_15 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1041878103/2500000000 : ℝ)*x 0 + (1109066373/2500000000 : ℝ)*x 1 + (4436264563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041878103/2500000000 : ℝ)^1059 ≤ (3940959457861/12500000000000 : ℝ)^803 := by
    have hnat : (1041878103 : ℕ)^1059*12500000000000^803 ≤ 3940959457861^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041878103 2500000000 3940959457861 12500000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1109066373/2500000000 : ℝ)^1059 ≤ (34236166887343/100000000000000 : ℝ)^803 := by
    have hnat : (1109066373 : ℕ)^1059*100000000000000^803 ≤ 34236166887343^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109066373 2500000000 34236166887343 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4436264563/10000000000 : ℝ)^1059 ≤ (6847231486459/20000000000000 : ℝ)^803 := by
    have hnat : (4436264563 : ℕ)^1059*20000000000000^803 ≤ 6847231486459^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4436264563 10000000000 6847231486459 20000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1041878103/2500000000 : ℝ), (1109066373/2500000000 : ℝ), (4436264563/10000000000 : ℝ)] ![(3940959457861/12500000000000 : ℝ), (34236166887343/100000000000000 : ℝ), (6847231486459/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1041878103/2500000000 : ℝ)|^1059 ≤ (3940959457861/12500000000000 : ℝ)^803
        have hw : |(1041878103/2500000000 : ℝ)|=(1041878103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1109066373/2500000000 : ℝ)|^1059 ≤ (34236166887343/100000000000000 : ℝ)^803
        have hw : |(1109066373/2500000000 : ℝ)|=(1109066373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4436264563/10000000000 : ℝ)|^1059 ≤ (6847231486459/20000000000000 : ℝ)^803
        have hw : |(4436264563/10000000000 : ℝ)|=(4436264563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1276_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (733/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15709/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11763/20000 : ℝ) ∧ (79559/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84091/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (733/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10987/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (733/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10987/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (733/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10987/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (733/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10987/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (733/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10987/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (733/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10987/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10987/100000 : ℝ) ^ (4235/1024 : ℝ) ≤ (2699375743555713/25000000000000000000 : ℝ) := by
    have hpowers : (10987/100000 : ℝ)^4235 ≤ (2699375743555713/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10987 : ℕ)^4235*25000000000000000000^1024 ≤ 2699375743555713^1024*100000^4235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10987 100000 2699375743555713 25000000000000000000 4235 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10987/100000 : ℝ)) (X := (2699375743555713/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (733/5000 : ℝ) ^ (4235/1024 : ℝ) ≤ (1112231277670583/3125000000000000000 : ℝ) := by
    have hpowers : (733/5000 : ℝ)^4235 ≤ (1112231277670583/3125000000000000000 : ℝ)^1024 := by
      have hnat : (733 : ℕ)^4235*3125000000000000000^1024 ≤ 1112231277670583^1024*5000^4235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        733 5000 1112231277670583 3125000000000000000 4235 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (733/5000 : ℝ)) (X := (1112231277670583/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502699375743555713/12500000000000000000 : ℝ) ≤ (10000522112773703/10000000000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (12502699375743555713/12500000000000000000 : ℝ)^1024 ≤ (10000522112773703/10000000000000000 : ℝ)^4235 := by
      have hnat : (12502699375743555713 : ℕ)^1024*10000000000000000^4235 ≤ 10000522112773703^4235*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502699375743555713 12500000000000000000 10000522112773703 10000000000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000522112773703/10000000000000000 : ℝ)) (X := (12502699375743555713/12500000000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011597225964920377/25000000000000000000 : ℝ) ≤ (2000224292259757/2000000000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (25011597225964920377/25000000000000000000 : ℝ)^1024 ≤ (2000224292259757/2000000000000000 : ℝ)^4235 := by
      have hnat : (25011597225964920377 : ℕ)^1024*2000000000000000^4235 ≤ 2000224292259757^4235*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011597225964920377 25000000000000000000 2000224292259757 2000000000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000224292259757/2000000000000000 : ℝ)) (X := (25011597225964920377/25000000000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563612231277670583/1562500000000000000 : ℝ) ≤ (10001720809823867/10000000000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (1563612231277670583/1562500000000000000 : ℝ)^1024 ≤ (10001720809823867/10000000000000000 : ℝ)^4235 := by
      have hnat : (1563612231277670583 : ℕ)^1024*10000000000000000^4235 ≤ 10001720809823867^4235*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563612231277670583 1562500000000000000 10001720809823867 10000000000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001720809823867/10000000000000000 : ℝ)) (X := (1563612231277670583/1562500000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2699375743555713/25000000000000000000 : ℝ) ≤ ((36718747635727659251/36730000000000000000 : ℝ)+2*(299674262541/183650000000000 : ℝ)*(10987/100000 : ℝ))^(4235/1024 : ℝ) := by
    rw [show (36718747635727659251/36730000000000000000 : ℝ)+2*(299674262541/183650000000000 : ℝ)*(10987/100000 : ℝ)=(10000522112773703/10000000000000000 : ℝ) by norm_num, show 1+2*(2699375743555713/25000000000000000000 : ℝ)=(12502699375743555713/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1112231277670583/3125000000000000000 : ℝ)+(2699375743555713/25000000000000000000 : ℝ) ≤ ((36718747635727659251/36730000000000000000 : ℝ)+(299674262541/183650000000000 : ℝ)*((733/5000 : ℝ)+(10987/100000 : ℝ)))^(4235/1024 : ℝ) := by
    rw [show (36718747635727659251/36730000000000000000 : ℝ)+(299674262541/183650000000000 : ℝ)*((733/5000 : ℝ)+(10987/100000 : ℝ))=(2000224292259757/2000000000000000 : ℝ) by norm_num, show 1+(1112231277670583/3125000000000000000 : ℝ)+(2699375743555713/25000000000000000000 : ℝ)=(25011597225964920377/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1112231277670583/3125000000000000000 : ℝ) ≤ ((36718747635727659251/36730000000000000000 : ℝ)+2*(299674262541/183650000000000 : ℝ)*(733/5000 : ℝ))^(4235/1024 : ℝ) := by
    rw [show (36718747635727659251/36730000000000000000 : ℝ)+2*(299674262541/183650000000000 : ℝ)*(733/5000 : ℝ)=(10001720809823867/10000000000000000 : ℝ) by norm_num, show 1+2*(1112231277670583/3125000000000000000 : ℝ)=(1563612231277670583/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36718747635727659251/36730000000000000000 : ℝ)*(X 1 0+X 2 0)+(299674262541/183650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (10987/100000 : ℝ)) (hi := (733/5000 : ℝ)) (c := (36718747635727659251/36730000000000000000 : ℝ)) (alpha := (299674262541/183650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36718747635727659251/36730000000000000000 : ℝ)*(X 0 1+X 2 1)+(299674262541/183650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (10987/100000 : ℝ)) (hi := (733/5000 : ℝ)) (c := (36718747635727659251/36730000000000000000 : ℝ)) (alpha := (299674262541/183650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36718747635727659251/36730000000000000000 : ℝ)*(X 0 2+X 1 2)+(299674262541/183650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (10987/100000 : ℝ)) (hi := (733/5000 : ℝ)) (c := (36718747635727659251/36730000000000000000 : ℝ)) (alpha := (299674262541/183650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-192969897/1000000000 : ℝ)*X 0 0+(2696332853/5000000000 : ℝ)*X 0 1+(5392665741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642033683/5000000000 : ℝ)*X 1 0+(-103906117/500000000 : ℝ)*X 1 1+(5392666169/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642033997/5000000000 : ℝ)*X 2 0+(1078533141/2000000000 : ℝ)*X 2 1+(-519530531/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4494022463/10000000000 : ℝ)*X 0 0+(4273303829/10000000000 : ℝ)*X 0 1+(2136651989/5000000000 : ℝ)*X 0 2+(4494022463/10000000000 : ℝ)*X 1 0+(4273303829/10000000000 : ℝ)*X 1 1+(2136651989/5000000000 : ℝ)*X 1 2+(4494022463/10000000000 : ℝ)*X 2 0+(4273303829/10000000000 : ℝ)*X 2 1+(2136651989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-284733121/1250000000 : ℝ)*X 0 0+(1315812123/2500000000 : ℝ)*X 0 1+(5263247279/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2687613091/5000000000 : ℝ)*X 1 0+(-1064780117/5000000000 : ℝ)*X 1 1+(657905999/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5375224831/10000000000 : ℝ)*X 2 0+(5263249067/10000000000 : ℝ)*X 2 1+(-1064780307/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((838702767/2000000000 : ℝ)*X 0 0+(2211750861/5000000000 : ℝ)*X 0 1+(442350279/1000000000 : ℝ)*X 0 2+(838702767/2000000000 : ℝ)*X 1 0+(2211750861/5000000000 : ℝ)*X 1 1+(442350279/1000000000 : ℝ)*X 1 2+(838702767/2000000000 : ℝ)*X 2 0+(2211750861/5000000000 : ℝ)*X 2 1+(442350279/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-220494037/1000000000 : ℝ)*X 0 0+(1034895501/2000000000 : ℝ)*X 0 1+(1351677111/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1054834039/2000000000 : ℝ)*X 1 0+(-1036202023/5000000000 : ℝ)*X 1 1+(2703354017/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1054833967/2000000000 : ℝ)*X 2 0+(2703354301/5000000000 : ℝ)*X 2 1+(-1036201879/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((565758373/1250000000 : ℝ)*X 0 0+(2128497469/5000000000 : ℝ)*X 0 1+(4256992897/10000000000 : ℝ)*X 0 2+(565758373/1250000000 : ℝ)*X 1 0+(2128497469/5000000000 : ℝ)*X 1 1+(4256992897/10000000000 : ℝ)*X 1 2+(565758373/1250000000 : ℝ)*X 2 0+(2128497469/5000000000 : ℝ)*X 2 1+(4256992897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-62596753/312500000 : ℝ)*X 0 0+(5479072563/10000000000 : ℝ)*X 0 1+(1050448483/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1345743789/2500000000 : ℝ)*X 1 0+(-533456931/2500000000 : ℝ)*X 1 1+(5252242237/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((215318999/400000000 : ℝ)*X 2 0+(5252242651/10000000000 : ℝ)*X 2 1+(-266728427/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1041878103/2500000000 : ℝ)*X 0 0+(1109066373/2500000000 : ℝ)*X 0 1+(4436264563/10000000000 : ℝ)*X 0 2+(1041878103/2500000000 : ℝ)*X 1 0+(1109066373/2500000000 : ℝ)*X 1 1+(4436264563/10000000000 : ℝ)*X 1 2+(1041878103/2500000000 : ℝ)*X 2 0+(1109066373/2500000000 : ℝ)*X 2 1+(4436264563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15709/25000 : ℝ) ≤ (-576965185068294655348965409254963/918250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15187309/12500000000000 : ℝ)*(upper0) + (173691431/100000000000000 : ℝ)*(upper3) + (81634391/25000000000000 : ℝ)*(lower4) + (1422906826871143/50000000000000 : ℝ)*(major0) + (1422906826871143/50000000000000 : ℝ)*(major1) + (1422906826871143/50000000000000 : ℝ)*(major2) + (490813119/12500000000000 : ℝ)*(sp3) + (3841973137579251/100000000000000 : ℝ)*(sp4) + (1920950462617013/50000000000000 : ℝ)*(sp5) + (960413134209691/25000000000000 : ℝ)*(sp6) + (1870593274556777/100000000000000 : ℝ)*(sp7) + (1344379233/100000000000000 : ℝ)*(sp8) + (73556724459/100000000000000 : ℝ)*(sp13) + (8048627993/2500000000000 : ℝ)*(sp14) + (1870597201061729/100000000000000 : ℝ)*(f.failure) + (960493620489621/25000000000000 : ℝ)*(f.sum) + (110098653985007/18365000000000000000000000000 : ℝ)*base65 + (7856304136842006107/1836500000000000000000000000000000 : ℝ)*base68 + (21550596142534006107/1836500000000000000000000000000000 : ℝ)*base70 + (13646846574744006107/1836500000000000000000000000000000 : ℝ)*base72 + (55651003383139/9182500000000000000000000000 : ℝ)*base74 + (25101283578665006107/1836500000000000000000000000000000 : ℝ)*base76 + (17444997710146006107/1836500000000000000000000000000000 : ℝ)*base78 + (11040276786553506107/1836500000000000000000000000000000 : ℝ)*base80 + (24533480235549/9182500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (40402027/10000000000000000000000 : ℝ)*base89 + (40402027/10000000000000000000000 : ℝ)*base91 + (40402027/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (11763/20000 : ℝ) ≤ (540089803425061989960757862117859/918250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4520623/20000000000000 : ℝ)*(lower0) + (71925067/50000000000000 : ℝ)*(lower1) + (16257781/12500000000000 : ℝ)*(lower2) + (4837743/12500000000000 : ℝ)*(lower3) + (4440281/6250000000000 : ℝ)*(upper4) + (22992193/100000000000000 : ℝ)*(lower5) + (2912324046228203/100000000000000 : ℝ)*(major0) + (2912324046228203/100000000000000 : ℝ)*(major1) + (2912324046228203/100000000000000 : ℝ)*(major2) + (3890726820016909/100000000000000 : ℝ)*(sp0) + (778144415529023/20000000000000 : ℝ)*(sp1) + (3890726820016909/100000000000000 : ℝ)*(sp2) + (957157753863351/50000000000000 : ℝ)*(sp3) + (2371185897/50000000000000 : ℝ)*(sp5) + (957157753863351/50000000000000 : ℝ)*(f.failure) + (3890726820016909/100000000000000 : ℝ)*(f.sum) + (7792165771697/9182500000000000000000000000 : ℝ)*base66 + (6138829649841344047/3673000000000000000000000000000000 : ℝ)*base68 + (53574046776790344047/3673000000000000000000000000000000 : ℝ)*base70 + (16926986263382655953/3673000000000000000000000000000000 : ℝ)*base71 + (87232256087249/1147812500000000000000000000 : ℝ)*base74 + (298678984065712344047/3673000000000000000000000000000000 : ℝ)*base76 + (2164470504621344047/3673000000000000000000000000000000 : ℝ)*base78 + (201468907543084344047/3673000000000000000000000000000000 : ℝ)*base80 + (23672565368023/9182500000000000000000000000 : ℝ)*base81 + (1909987/5000000000000000000000 : ℝ)*base90 + (1909987/5000000000000000000000 : ℝ)*base92 + (1909987/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79559/100000 : ℝ) ≤ (730572765031058472890144718263631/918250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83766349/25000000000000 : ℝ)*(upper1) + (43251249/50000000000000 : ℝ)*(upper4) + (7083109/6250000000000 : ℝ)*(lower5) + (201676761170391/6250000000000 : ℝ)*(major0) + (201676761170391/6250000000000 : ℝ)*(major1) + (1613414089363129/50000000000000 : ℝ)*(major2) + (157213641697/50000000000000 : ℝ)*(sp1) + (558402695891/100000000000000 : ℝ)*(sp2) + (12341521179/25000000000000 : ℝ)*(sp3) + (4931629429/25000000000000 : ℝ)*(sp4) + (2153036116273671/50000000000000 : ℝ)*(sp8) + (4305777531781663/100000000000000 : ℝ)*(sp9) + (2152766778184583/50000000000000 : ℝ)*(sp10) + (2120994558029887/100000000000000 : ℝ)*(sp11) + (1060521962057301/50000000000000 : ℝ)*(f.failure) + (4306091959065057/100000000000000 : ℝ)*(f.sum) + (11675466951477/9182500000000000000000000000 : ℝ)*base65 + (4679320282537837859/229562500000000000000000000000000 : ℝ)*base68 + (3629925968251256379/1836500000000000000000000000000000 : ℝ)*base69 + (5751024837179650359/229562500000000000000000000000000 : ℝ)*base72 + (32065185943097/9182500000000000000000000000 : ℝ)*base73 + (6252764735117256379/1836500000000000000000000000000000 : ℝ)*base75 + (4353241993216612859/229562500000000000000000000000000 : ℝ)*base78 + (5023134540330425359/229562500000000000000000000000000 : ℝ)*base80 + (17185639416883/18365000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (34213863/5000000000000000000000 : ℝ)*base89 + (34213863/5000000000000000000000 : ℝ)*base91 + (65786137/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-84091/100000 : ℝ) ≤ (-1544281781507594632293679758926241/1836500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51047487/20000000000000 : ℝ)*(lower0) + (100202063/100000000000000 : ℝ)*(lower1) + (21623593/25000000000000 : ℝ)*(lower2) + (815635702776437/25000000000000 : ℝ)*(major0) + (815635702776437/25000000000000 : ℝ)*(major1) + (3262542811105749/100000000000000 : ℝ)*(major2) + (2438033579/12500000000000 : ℝ)*(sp0) + (411203490839/100000000000000 : ℝ)*(sp5) + (196577725803/100000000000000 : ℝ)*(sp6) + (53218563913/100000000000000 : ℝ)*(sp7) + (4408575851287597/100000000000000 : ℝ)*(sp12) + (440818415206539/10000000000000 : ℝ)*(sp13) + (2204199388915213/50000000000000 : ℝ)*(sp14) + (214446648418369/10000000000000 : ℝ)*(sp15) + (2144519702747603/100000000000000 : ℝ)*(f.failure) + (4408595355556229/100000000000000 : ℝ)*(f.sum) + (34663488423291/9182500000000000000000000000 : ℝ)*base65 + (1751743759894068687/918250000000000000000000000000000 : ℝ)*base67 + (50517626670821733999/3673000000000000000000000000000000 : ℝ)*base69 + (1133558621178931313/918250000000000000000000000000000 : ℝ)*base72 + (259668288526177/18365000000000000000000000000 : ℝ)*base73 + (52255471172698733999/3673000000000000000000000000000000 : ℝ)*base75 + (964161659777768687/918250000000000000000000000000000 : ℝ)*base77 + (2690417928379018687/918250000000000000000000000000000 : ℝ)*base79 + (22964396819703/9182500000000000000000000000 : ℝ)*base81 + (33140689/10000000000000000000000 : ℝ)*base89 + (33140689/10000000000000000000000 : ℝ)*base91 + (66859311/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1276_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (733/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15709/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(11763/20000 : ℝ) else (79559/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84091/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1276_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1276_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (733/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15709/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(11763/20000 : ℝ) else (79559/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84091/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1276_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (733/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15709/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(11763/20000 : ℝ) else (79559/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84091/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1276_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

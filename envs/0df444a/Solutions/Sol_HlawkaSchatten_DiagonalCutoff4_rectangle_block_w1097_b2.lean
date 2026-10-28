-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1097_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:59:30.26583+00:00
-- url     : https://prove2.me/submissions/11712fe3-2138-46c8-8210-dc7a132bc891

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
theorem support_rectangle_w1097_s6_0 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2188552789/10000000000 : ℝ)*x 0 + (5394291073/10000000000 : ℝ)*x 1 + (5264556949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188552789/10000000000 : ℝ)^4145 ≤ (1661776377217/12500000000000 : ℝ)^3121 := by
    have hnat : (2188552789 : ℕ)^4145*12500000000000^3121 ≤ 1661776377217^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188552789 10000000000 1661776377217 12500000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394291073/10000000000 : ℝ)^4145 ≤ (44053665993943/100000000000000 : ℝ)^3121 := by
    have hnat : (5394291073 : ℕ)^4145*100000000000000^3121 ≤ 44053665993943^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394291073 10000000000 44053665993943 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264556949/10000000000 : ℝ)^4145 ≤ (21326061487291/50000000000000 : ℝ)^3121 := by
    have hnat : (5264556949 : ℕ)^4145*50000000000000^3121 ≤ 21326061487291^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264556949 10000000000 21326061487291 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2188552789/10000000000 : ℝ), (5394291073/10000000000 : ℝ), (5264556949/10000000000 : ℝ)] ![(1661776377217/12500000000000 : ℝ), (44053665993943/100000000000000 : ℝ), (21326061487291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2188552789/10000000000 : ℝ)|^4145 ≤ (1661776377217/12500000000000 : ℝ)^3121
        have hw : |(-2188552789/10000000000 : ℝ)|=(2188552789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394291073/10000000000 : ℝ)|^4145 ≤ (44053665993943/100000000000000 : ℝ)^3121
        have hw : |(5394291073/10000000000 : ℝ)|=(5394291073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264556949/10000000000 : ℝ)|^4145 ≤ (21326061487291/50000000000000 : ℝ)^3121
        have hw : |(5264556949/10000000000 : ℝ)|=(5264556949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s6_1 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069003773/2000000000 : ℝ)*x 0 + (-563593591/2500000000 : ℝ)*x 1 + (5264556949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069003773/2000000000 : ℝ)^4145 ≤ (43520051188369/100000000000000 : ℝ)^3121 := by
    have hnat : (1069003773 : ℕ)^4145*100000000000000^3121 ≤ 43520051188369^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069003773 2000000000 43520051188369 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563593591/2500000000 : ℝ)^4145 ≤ (3456956457163/25000000000000 : ℝ)^3121 := by
    have hnat : (563593591 : ℕ)^4145*25000000000000^3121 ≤ 3456956457163^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563593591 2500000000 3456956457163 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264556949/10000000000 : ℝ)^4145 ≤ (21326061487291/50000000000000 : ℝ)^3121 := by
    have hnat : (5264556949 : ℕ)^4145*50000000000000^3121 ≤ 21326061487291^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264556949 10000000000 21326061487291 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069003773/2000000000 : ℝ), (-563593591/2500000000 : ℝ), (5264556949/10000000000 : ℝ)] ![(43520051188369/100000000000000 : ℝ), (3456956457163/25000000000000 : ℝ), (21326061487291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069003773/2000000000 : ℝ)|^4145 ≤ (43520051188369/100000000000000 : ℝ)^3121
        have hw : |(1069003773/2000000000 : ℝ)|=(1069003773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-563593591/2500000000 : ℝ)|^4145 ≤ (3456956457163/25000000000000 : ℝ)^3121
        have hw : |(-563593591/2500000000 : ℝ)|=(563593591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264556949/10000000000 : ℝ)|^4145 ≤ (21326061487291/50000000000000 : ℝ)^3121
        have hw : |(5264556949/10000000000 : ℝ)|=(5264556949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s6_2 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069003773/2000000000 : ℝ)*x 0 + (5264556949/10000000000 : ℝ)*x 1 + (-563593591/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069003773/2000000000 : ℝ)^4145 ≤ (43520051188369/100000000000000 : ℝ)^3121 := by
    have hnat : (1069003773 : ℕ)^4145*100000000000000^3121 ≤ 43520051188369^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069003773 2000000000 43520051188369 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264556949/10000000000 : ℝ)^4145 ≤ (21326061487291/50000000000000 : ℝ)^3121 := by
    have hnat : (5264556949 : ℕ)^4145*50000000000000^3121 ≤ 21326061487291^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264556949 10000000000 21326061487291 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563593591/2500000000 : ℝ)^4145 ≤ (3456956457163/25000000000000 : ℝ)^3121 := by
    have hnat : (563593591 : ℕ)^4145*25000000000000^3121 ≤ 3456956457163^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563593591 2500000000 3456956457163 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069003773/2000000000 : ℝ), (5264556949/10000000000 : ℝ), (-563593591/2500000000 : ℝ)] ![(43520051188369/100000000000000 : ℝ), (21326061487291/50000000000000 : ℝ), (3456956457163/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069003773/2000000000 : ℝ)|^4145 ≤ (43520051188369/100000000000000 : ℝ)^3121
        have hw : |(1069003773/2000000000 : ℝ)|=(1069003773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264556949/10000000000 : ℝ)|^4145 ≤ (21326061487291/50000000000000 : ℝ)^3121
        have hw : |(5264556949/10000000000 : ℝ)|=(5264556949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-563593591/2500000000 : ℝ)|^4145 ≤ (3456956457163/25000000000000 : ℝ)^3121
        have hw : |(-563593591/2500000000 : ℝ)|=(563593591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s6_3 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4371028923/10000000000 : ℝ)*x 0 + (4244997893/10000000000 : ℝ)*x 1 + (900164883/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371028923/10000000000 : ℝ)^4145 ≤ (2082280415929/6250000000000 : ℝ)^3121 := by
    have hnat : (4371028923 : ℕ)^4145*6250000000000^3121 ≤ 2082280415929^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371028923 10000000000 2082280415929 6250000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4244997893/10000000000 : ℝ)^4145 ≤ (1602337866767/5000000000000 : ℝ)^3121 := by
    have hnat : (4244997893 : ℕ)^4145*5000000000000^3121 ≤ 1602337866767^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244997893 10000000000 1602337866767 5000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900164883/2000000000 : ℝ)^4145 ≤ (34636755997719/100000000000000 : ℝ)^3121 := by
    have hnat : (900164883 : ℕ)^4145*100000000000000^3121 ≤ 34636755997719^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900164883 2000000000 34636755997719 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371028923/10000000000 : ℝ), (4244997893/10000000000 : ℝ), (900164883/2000000000 : ℝ)] ![(2082280415929/6250000000000 : ℝ), (1602337866767/5000000000000 : ℝ), (34636755997719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371028923/10000000000 : ℝ)|^4145 ≤ (2082280415929/6250000000000 : ℝ)^3121
        have hw : |(4371028923/10000000000 : ℝ)|=(4371028923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4244997893/10000000000 : ℝ)|^4145 ≤ (1602337866767/5000000000000 : ℝ)^3121
        have hw : |(4244997893/10000000000 : ℝ)|=(4244997893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900164883/2000000000 : ℝ)|^4145 ≤ (34636755997719/100000000000000 : ℝ)^3121
        have hw : |(900164883/2000000000 : ℝ)|=(900164883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s6_4 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2188557937/10000000000 : ℝ)*x 0 + (5264884549/10000000000 : ℝ)*x 1 + (5393962243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188557937/10000000000 : ℝ)^4145 ≤ (13294252548987/100000000000000 : ℝ)^3121 := by
    have hnat : (2188557937 : ℕ)^4145*100000000000000^3121 ≤ 13294252548987^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188557937 10000000000 13294252548987 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264884549/10000000000 : ℝ)^4145 ≤ (4265564796481/10000000000000 : ℝ)^3121 := by
    have hnat : (5264884549 : ℕ)^4145*10000000000000^3121 ≤ 4265564796481^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264884549 10000000000 4265564796481 10000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393962243/10000000000 : ℝ)^4145 ≤ (22025049733401/50000000000000 : ℝ)^3121 := by
    have hnat : (5393962243 : ℕ)^4145*50000000000000^3121 ≤ 22025049733401^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393962243 10000000000 22025049733401 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2188557937/10000000000 : ℝ), (5264884549/10000000000 : ℝ), (5393962243/10000000000 : ℝ)] ![(13294252548987/100000000000000 : ℝ), (4265564796481/10000000000000 : ℝ), (22025049733401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2188557937/10000000000 : ℝ)|^4145 ≤ (13294252548987/100000000000000 : ℝ)^3121
        have hw : |(-2188557937/10000000000 : ℝ)|=(2188557937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264884549/10000000000 : ℝ)|^4145 ≤ (4265564796481/10000000000000 : ℝ)^3121
        have hw : |(5264884549/10000000000 : ℝ)|=(5264884549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393962243/10000000000 : ℝ)|^4145 ≤ (22025049733401/50000000000000 : ℝ)^3121
        have hw : |(5393962243/10000000000 : ℝ)|=(5393962243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s6_5 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062452399/2000000000 : ℝ)*x 0 + (-2124969033/10000000000 : ℝ)*x 1 + (5393962221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062452399/2000000000 : ℝ)^4145 ≤ (2697886725501/6250000000000 : ℝ)^3121 := by
    have hnat : (1062452399 : ℕ)^4145*6250000000000^3121 ≤ 2697886725501^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062452399 2000000000 2697886725501 6250000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2124969033/10000000000 : ℝ)^4145 ≤ (2556742629041/20000000000000 : ℝ)^3121 := by
    have hnat : (2124969033 : ℕ)^4145*20000000000000^3121 ≤ 2556742629041^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124969033 10000000000 2556742629041 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393962221/10000000000 : ℝ)^4145 ≤ (4405009922819/10000000000000 : ℝ)^3121 := by
    have hnat : (5393962221 : ℕ)^4145*10000000000000^3121 ≤ 4405009922819^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393962221 10000000000 4405009922819 10000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062452399/2000000000 : ℝ), (-2124969033/10000000000 : ℝ), (5393962221/10000000000 : ℝ)] ![(2697886725501/6250000000000 : ℝ), (2556742629041/20000000000000 : ℝ), (4405009922819/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062452399/2000000000 : ℝ)|^4145 ≤ (2697886725501/6250000000000 : ℝ)^3121
        have hw : |(1062452399/2000000000 : ℝ)|=(1062452399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2124969033/10000000000 : ℝ)|^4145 ≤ (2556742629041/20000000000000 : ℝ)^3121
        have hw : |(-2124969033/10000000000 : ℝ)|=(2124969033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393962221/10000000000 : ℝ)|^4145 ≤ (4405009922819/10000000000000 : ℝ)^3121
        have hw : |(5393962221/10000000000 : ℝ)|=(5393962221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s6_6 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312261989/10000000000 : ℝ)*x 0 + (5393962211/10000000000 : ℝ)*x 1 + (-424993811/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312261989/10000000000 : ℝ)^4145 ≤ (8633237508653/20000000000000 : ℝ)^3121 := by
    have hnat : (5312261989 : ℕ)^4145*20000000000000^3121 ≤ 8633237508653^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312261989 10000000000 8633237508653 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393962211/10000000000 : ℝ)^4145 ≤ (4405009911973/10000000000000 : ℝ)^3121 := by
    have hnat : (5393962211 : ℕ)^4145*10000000000000^3121 ≤ 4405009911973^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393962211 10000000000 4405009911973 10000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424993811/2000000000 : ℝ)^4145 ≤ (12783713320981/100000000000000 : ℝ)^3121 := by
    have hnat : (424993811 : ℕ)^4145*100000000000000^3121 ≤ 12783713320981^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424993811 2000000000 12783713320981 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312261989/10000000000 : ℝ), (5393962211/10000000000 : ℝ), (-424993811/2000000000 : ℝ)] ![(8633237508653/20000000000000 : ℝ), (4405009911973/10000000000000 : ℝ), (12783713320981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312261989/10000000000 : ℝ)|^4145 ≤ (8633237508653/20000000000000 : ℝ)^3121
        have hw : |(5312261989/10000000000 : ℝ)|=(5312261989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393962211/10000000000 : ℝ)|^4145 ≤ (4405009911973/10000000000000 : ℝ)^3121
        have hw : |(5393962211/10000000000 : ℝ)|=(5393962211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-424993811/2000000000 : ℝ)|^4145 ≤ (12783713320981/100000000000000 : ℝ)^3121
        have hw : |(-424993811/2000000000 : ℝ)|=(424993811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s6_7 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4371038993/10000000000 : ℝ)*x 0 + (2250089157/5000000000 : ℝ)*x 1 + (53070579/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371038993/10000000000 : ℝ)^4145 ≤ (1665829429641/5000000000000 : ℝ)^3121 := by
    have hnat : (4371038993 : ℕ)^4145*5000000000000^3121 ≤ 1665829429641^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371038993 10000000000 1665829429641 5000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250089157/5000000000 : ℝ)^4145 ≤ (6926030524149/20000000000000 : ℝ)^3121 := by
    have hnat : (2250089157 : ℕ)^4145*20000000000000^3121 ≤ 6926030524149^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250089157 5000000000 6926030524149 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53070579/125000000 : ℝ)^4145 ≤ (8013314693059/25000000000000 : ℝ)^3121 := by
    have hnat : (53070579 : ℕ)^4145*25000000000000^3121 ≤ 8013314693059^3121*125000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53070579 125000000 8013314693059 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371038993/10000000000 : ℝ), (2250089157/5000000000 : ℝ), (53070579/125000000 : ℝ)] ![(1665829429641/5000000000000 : ℝ), (6926030524149/20000000000000 : ℝ), (8013314693059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371038993/10000000000 : ℝ)|^4145 ≤ (1665829429641/5000000000000 : ℝ)^3121
        have hw : |(4371038993/10000000000 : ℝ)|=(4371038993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2250089157/5000000000 : ℝ)|^4145 ≤ (6926030524149/20000000000000 : ℝ)^3121
        have hw : |(2250089157/5000000000 : ℝ)|=(2250089157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53070579/125000000 : ℝ)|^4145 ≤ (8013314693059/25000000000000 : ℝ)^3121
        have hw : |(53070579/125000000 : ℝ)|=(53070579/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1097_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2821/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (877/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11247/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11247/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11247/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11247/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11247/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11247/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11247/100000 : ℝ) ^ (8289/2048 : ℝ) ≤ (1803477704286441/12500000000000000000 : ℝ) := by
    have hpowers : (11247/100000 : ℝ)^8289 ≤ (1803477704286441/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11247 : ℕ)^8289*12500000000000000000^2048 ≤ 1803477704286441^2048*100000^8289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11247 100000 1803477704286441 12500000000000000000 8289 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11247/100000 : ℝ)) (X := (1803477704286441/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14071/100000 : ℝ) ^ (8289/2048 : ℝ) ≤ (17862067745460921/50000000000000000000 : ℝ) := by
    have hpowers : (14071/100000 : ℝ)^8289 ≤ (17862067745460921/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14071 : ℕ)^8289*50000000000000000000^2048 ≤ 17862067745460921^2048*100000^8289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14071 100000 17862067745460921 50000000000000000000 8289 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14071/100000 : ℝ)) (X := (17862067745460921/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251803477704286441/6250000000000000000 : ℝ) ≤ (5000356435871723/5000000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (6251803477704286441/6250000000000000000 : ℝ)^2048 ≤ (5000356435871723/5000000000000000 : ℝ)^8289 := by
      have hnat : (6251803477704286441 : ℕ)^2048*5000000000000000^8289 ≤ 5000356435871723^8289*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251803477704286441 6250000000000000000 5000356435871723 5000000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000356435871723/5000000000000000 : ℝ)) (X := (6251803477704286441/6250000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005015195712521337/10000000000000000000 : ℝ) ≤ (5000619446384621/5000000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (10005015195712521337/10000000000000000000 : ℝ)^2048 ≤ (5000619446384621/5000000000000000 : ℝ)^8289 := by
      have hnat : (10005015195712521337 : ℕ)^2048*5000000000000000^8289 ≤ 5000619446384621^8289*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005015195712521337 10000000000000000000 5000619446384621 5000000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000619446384621/5000000000000000 : ℝ)) (X := (10005015195712521337/10000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017862067745460921/25000000000000000000 : ℝ) ≤ (5000882456897519/5000000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (25017862067745460921/25000000000000000000 : ℝ)^2048 ≤ (5000882456897519/5000000000000000 : ℝ)^8289 := by
      have hnat : (25017862067745460921 : ℕ)^2048*5000000000000000^8289 ≤ 5000882456897519^8289*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017862067745460921 25000000000000000000 5000882456897519 5000000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000882456897519/5000000000000000 : ℝ)) (X := (25017862067745460921/25000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1803477704286441/12500000000000000000 : ℝ) ≤ ((705754520821230907/706000000000000000 : ℝ)+2*(131505256449/70600000000000 : ℝ)*(11247/100000 : ℝ))^(8289/2048 : ℝ) := by
    rw [show (705754520821230907/706000000000000000 : ℝ)+2*(131505256449/70600000000000 : ℝ)*(11247/100000 : ℝ)=(5000356435871723/5000000000000000 : ℝ) by norm_num, show 1+2*(1803477704286441/12500000000000000000 : ℝ)=(6251803477704286441/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17862067745460921/50000000000000000000 : ℝ)+(1803477704286441/12500000000000000000 : ℝ) ≤ ((705754520821230907/706000000000000000 : ℝ)+(131505256449/70600000000000 : ℝ)*((14071/100000 : ℝ)+(11247/100000 : ℝ)))^(8289/2048 : ℝ) := by
    rw [show (705754520821230907/706000000000000000 : ℝ)+(131505256449/70600000000000 : ℝ)*((14071/100000 : ℝ)+(11247/100000 : ℝ))=(5000619446384621/5000000000000000 : ℝ) by norm_num, show 1+(17862067745460921/50000000000000000000 : ℝ)+(1803477704286441/12500000000000000000 : ℝ)=(10005015195712521337/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17862067745460921/50000000000000000000 : ℝ) ≤ ((705754520821230907/706000000000000000 : ℝ)+2*(131505256449/70600000000000 : ℝ)*(14071/100000 : ℝ))^(8289/2048 : ℝ) := by
    rw [show (705754520821230907/706000000000000000 : ℝ)+2*(131505256449/70600000000000 : ℝ)*(14071/100000 : ℝ)=(5000882456897519/5000000000000000 : ℝ) by norm_num, show 1+2*(17862067745460921/50000000000000000000 : ℝ)=(25017862067745460921/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (705754520821230907/706000000000000000 : ℝ)*(X 1 0+X 2 0)+(131505256449/70600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (11247/100000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (705754520821230907/706000000000000000 : ℝ)) (alpha := (131505256449/70600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (705754520821230907/706000000000000000 : ℝ)*(X 0 1+X 2 1)+(131505256449/70600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (11247/100000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (705754520821230907/706000000000000000 : ℝ)) (alpha := (131505256449/70600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (705754520821230907/706000000000000000 : ℝ)*(X 0 2+X 1 2)+(131505256449/70600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (11247/100000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (705754520821230907/706000000000000000 : ℝ)) (alpha := (131505256449/70600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2188552789/10000000000 : ℝ)*X 0 0+(5394291073/10000000000 : ℝ)*X 0 1+(5264556949/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069003773/2000000000 : ℝ)*X 1 0+(-563593591/2500000000 : ℝ)*X 1 1+(5264556949/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069003773/2000000000 : ℝ)*X 2 0+(5264556949/10000000000 : ℝ)*X 2 1+(-563593591/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4371028923/10000000000 : ℝ)*X 0 0+(4244997893/10000000000 : ℝ)*X 0 1+(900164883/2000000000 : ℝ)*X 0 2+(4371028923/10000000000 : ℝ)*X 1 0+(4244997893/10000000000 : ℝ)*X 1 1+(900164883/2000000000 : ℝ)*X 1 2+(4371028923/10000000000 : ℝ)*X 2 0+(4244997893/10000000000 : ℝ)*X 2 1+(900164883/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2188557937/10000000000 : ℝ)*X 0 0+(5264884549/10000000000 : ℝ)*X 0 1+(5393962243/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062452399/2000000000 : ℝ)*X 1 0+(-2124969033/10000000000 : ℝ)*X 1 1+(5393962221/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312261989/10000000000 : ℝ)*X 2 0+(5393962211/10000000000 : ℝ)*X 2 1+(-424993811/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4371038993/10000000000 : ℝ)*X 0 0+(2250089157/5000000000 : ℝ)*X 0 1+(53070579/125000000 : ℝ)*X 0 2+(4371038993/10000000000 : ℝ)*X 1 0+(2250089157/5000000000 : ℝ)*X 1 1+(53070579/125000000 : ℝ)*X 1 2+(4371038993/10000000000 : ℝ)*X 2 0+(2250089157/5000000000 : ℝ)*X 2 1+(53070579/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57340339463526278037457923/7060000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1620915717/100000000000000 : ℝ)*(base19) + (1509553351/100000000000000 : ℝ)*(base23) + (11904679/20000000000000 : ℝ)*(lower2) + (103010973/50000000000000 : ℝ)*(upper3) + (4929043/4000000000000 : ℝ)*(upper5) + (1161710549825521/20000000000000 : ℝ)*(major0) + (1161710549825521/20000000000000 : ℝ)*(major1) + (1161710549825521/20000000000000 : ℝ)*(major2) + (3854058867068037/50000000000000 : ℝ)*(sp0) + (7708159508157557/100000000000000 : ℝ)*(sp1) + (7708159619519923/100000000000000 : ℝ)*(sp2) + (488615036382479/12500000000000 : ℝ)*(sp3) + (43394937199/100000000000000 : ℝ)*(sp4) + (23807393389/100000000000000 : ℝ)*(sp7) + (195447204922661/5000000000000 : ℝ)*(f.failure) + (3854080564536637/50000000000000 : ℝ)*(f.sum) + (847470579211/141200000000000000000000000 : ℝ)*base66 + (178296079891132453/14120000000000000000000000000000 : ℝ)*base68 + (1259895031292453/14120000000000000000000000000000 : ℝ)*base70 + (314056282722292453/14120000000000000000000000000000 : ℝ)*base72 + (704760023023/141200000000000000000000000 : ℝ)*base74 + (103499398132492453/14120000000000000000000000000000 : ℝ)*base76 + (273405291133092453/14120000000000000000000000000000 : ℝ)*base78 + (58102252440012453/14120000000000000000000000000000 : ℝ)*base80 + (3696834653399/706000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (401327/100000000000000000000 : ℝ)*base90 + (401327/100000000000000000000 : ℝ)*base92 + (401327/100000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15599029931763634713717/3530000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57615431/5000000000000 : ℝ)*(base19) + (564273381/50000000000000 : ℝ)*(base23) + (9951069/10000000000000 : ℝ)*(upper3) + (493691/100000000000000 : ℝ)*(lower4) + (129845721/100000000000000 : ℝ)*(upper5) + (5838025879153633/100000000000000 : ℝ)*(major0) + (5838025879153633/100000000000000 : ℝ)*(major1) + (5838025879153633/100000000000000 : ℝ)*(major2) + (16004101173/50000000000000 : ℝ)*(sp1) + (29423014039/100000000000000 : ℝ)*(sp2) + (7747273171255631/100000000000000 : ℝ)*(sp4) + (1549448002148933/20000000000000 : ℝ)*(sp5) + (7747242619694831/100000000000000 : ℝ)*(sp6) + (982194609938001/25000000000000 : ℝ)*(sp7) + (982194609938001/25000000000000 : ℝ)*(f.failure) + (7747273171255631/100000000000000 : ℝ)*(f.sum) + (928002529967/3530000000000000000000000000 : ℝ)*base65 + (266336338541894869/70600000000000000000000000000000 : ℝ)*base68 + (1171222348435305131/70600000000000000000000000000000 : ℝ)*base69 + (672192388439094869/70600000000000000000000000000000 : ℝ)*base72 + (8891945013707/3530000000000000000000000000 : ℝ)*base73 + (1439180201623705131/70600000000000000000000000000000 : ℝ)*base75 + (494291728846494869/70600000000000000000000000000000 : ℝ)*base78 + (458945020388305131/70600000000000000000000000000000 : ℝ)*base79 + (9081682471347/3530000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1446707/500000000000000000000 : ℝ)*base90 + (1446707/500000000000000000000 : ℝ)*base92 + (1446707/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1097_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (877/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1097_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1097_s7_0 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-437717707/2000000000 : ℝ)*x 0 + (5393888427/10000000000 : ℝ)*x 1 + (5264936013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437717707/2000000000 : ℝ)^4145 ≤ (13294499397593/100000000000000 : ℝ)^3121 := by
    have hnat : (437717707 : ℕ)^4145*100000000000000^3121 ≤ 13294499397593^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437717707 2000000000 13294499397593 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393888427/10000000000 : ℝ)^4145 ≤ (22024649429987/50000000000000 : ℝ)^3121 := by
    have hnat : (5393888427 : ℕ)^4145*50000000000000^3121 ≤ 22024649429987^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393888427 10000000000 22024649429987 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264936013/10000000000 : ℝ)^4145 ≤ (21328100863113/50000000000000 : ℝ)^3121 := by
    have hnat : (5264936013 : ℕ)^4145*50000000000000^3121 ≤ 21328100863113^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264936013 10000000000 21328100863113 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-437717707/2000000000 : ℝ), (5393888427/10000000000 : ℝ), (5264936013/10000000000 : ℝ)] ![(13294499397593/100000000000000 : ℝ), (22024649429987/50000000000000 : ℝ), (21328100863113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-437717707/2000000000 : ℝ)|^4145 ≤ (13294499397593/100000000000000 : ℝ)^3121
        have hw : |(-437717707/2000000000 : ℝ)|=(437717707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393888427/10000000000 : ℝ)|^4145 ≤ (22024649429987/50000000000000 : ℝ)^3121
        have hw : |(5393888427/10000000000 : ℝ)|=(5393888427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264936013/10000000000 : ℝ)|^4145 ≤ (21328100863113/50000000000000 : ℝ)^3121
        have hw : |(5264936013/10000000000 : ℝ)|=(5264936013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s7_1 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336229417/2500000000 : ℝ)*x 0 + (-11270039/50000000 : ℝ)*x 1 + (5264936161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336229417/2500000000 : ℝ)^4145 ≤ (1740758275453/4000000000000 : ℝ)^3121 := by
    have hnat : (1336229417 : ℕ)^4145*4000000000000^3121 ≤ 1740758275453^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336229417 2500000000 1740758275453 4000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11270039/50000000 : ℝ)^4145 ≤ (2764967956033/20000000000000 : ℝ)^3121 := by
    have hnat : (11270039 : ℕ)^4145*20000000000000^3121 ≤ 2764967956033^3121*50000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11270039 50000000 2764967956033 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264936161/10000000000 : ℝ)^4145 ≤ (42656203318733/100000000000000 : ℝ)^3121 := by
    have hnat : (5264936161 : ℕ)^4145*100000000000000^3121 ≤ 42656203318733^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264936161 10000000000 42656203318733 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336229417/2500000000 : ℝ), (-11270039/50000000 : ℝ), (5264936161/10000000000 : ℝ)] ![(1740758275453/4000000000000 : ℝ), (2764967956033/20000000000000 : ℝ), (42656203318733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336229417/2500000000 : ℝ)|^4145 ≤ (1740758275453/4000000000000 : ℝ)^3121
        have hw : |(1336229417/2500000000 : ℝ)|=(1336229417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11270039/50000000 : ℝ)|^4145 ≤ (2764967956033/20000000000000 : ℝ)^3121
        have hw : |(-11270039/50000000 : ℝ)|=(11270039/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264936161/10000000000 : ℝ)|^4145 ≤ (42656203318733/100000000000000 : ℝ)^3121
        have hw : |(5264936161/10000000000 : ℝ)|=(5264936161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s7_2 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672459011/5000000000 : ℝ)*x 0 + (5264935919/10000000000 : ℝ)*x 1 + (-45080153/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672459011/5000000000 : ℝ)^4145 ≤ (43518960714321/100000000000000 : ℝ)^3121 := by
    have hnat : (2672459011 : ℕ)^4145*100000000000000^3121 ≤ 43518960714321^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672459011 5000000000 43518960714321 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264935919/10000000000 : ℝ)^4145 ≤ (2666012544673/6250000000000 : ℝ)^3121 := by
    have hnat : (5264935919 : ℕ)^4145*6250000000000^3121 ≤ 2666012544673^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264935919 10000000000 2666012544673 6250000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45080153/200000000 : ℝ)^4145 ≤ (1382483855829/10000000000000 : ℝ)^3121 := by
    have hnat : (45080153 : ℕ)^4145*10000000000000^3121 ≤ 1382483855829^3121*200000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45080153 200000000 1382483855829 10000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672459011/5000000000 : ℝ), (5264935919/10000000000 : ℝ), (-45080153/200000000 : ℝ)] ![(43518960714321/100000000000000 : ℝ), (2666012544673/6250000000000 : ℝ), (1382483855829/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672459011/5000000000 : ℝ)|^4145 ≤ (43518960714321/100000000000000 : ℝ)^3121
        have hw : |(2672459011/5000000000 : ℝ)|=(2672459011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264935919/10000000000 : ℝ)|^4145 ≤ (2666012544673/6250000000000 : ℝ)^3121
        have hw : |(5264935919/10000000000 : ℝ)|=(5264935919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-45080153/200000000 : ℝ)|^4145 ≤ (1382483855829/10000000000000 : ℝ)^3121
        have hw : |(-45080153/200000000 : ℝ)|=(45080153/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s7_3 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4371049021/10000000000 : ℝ)*x 0 + (2122883117/5000000000 : ℝ)*x 1 + (900010147/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371049021/10000000000 : ℝ)^4145 ≤ (4164586263211/12500000000000 : ℝ)^3121 := by
    have hnat : (4371049021 : ℕ)^4145*12500000000000^3121 ≤ 4164586263211^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371049021 10000000000 4164586263211 12500000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122883117/5000000000 : ℝ)^4145 ≤ (16027230561309/50000000000000 : ℝ)^3121 := by
    have hnat : (2122883117 : ℕ)^4145*50000000000000^3121 ≤ 16027230561309^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122883117 5000000000 16027230561309 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900010147/2000000000 : ℝ)^4145 ≤ (34628848755759/100000000000000 : ℝ)^3121 := by
    have hnat : (900010147 : ℕ)^4145*100000000000000^3121 ≤ 34628848755759^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900010147 2000000000 34628848755759 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371049021/10000000000 : ℝ), (2122883117/5000000000 : ℝ), (900010147/2000000000 : ℝ)] ![(4164586263211/12500000000000 : ℝ), (16027230561309/50000000000000 : ℝ), (34628848755759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371049021/10000000000 : ℝ)|^4145 ≤ (4164586263211/12500000000000 : ℝ)^3121
        have hw : |(4371049021/10000000000 : ℝ)|=(4371049021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2122883117/5000000000 : ℝ)|^4145 ≤ (16027230561309/50000000000000 : ℝ)^3121
        have hw : |(2122883117/5000000000 : ℝ)|=(2122883117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900010147/2000000000 : ℝ)|^4145 ≤ (34628848755759/100000000000000 : ℝ)^3121
        have hw : |(900010147/2000000000 : ℝ)|=(900010147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s7_4 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-547148421/2500000000 : ℝ)*x 0 + (5265259793/10000000000 : ℝ)*x 1 + (5393563371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547148421/2500000000 : ℝ)^4145 ≤ (6647270468567/50000000000000 : ℝ)^3121 := by
    have hnat : (547148421 : ℕ)^4145*50000000000000^3121 ≤ 6647270468567^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547148421 2500000000 6647270468567 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265259793/10000000000 : ℝ)^4145 ≤ (42659685694973/100000000000000 : ℝ)^3121 := by
    have hnat : (5265259793 : ℕ)^4145*100000000000000^3121 ≤ 42659685694973^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265259793 10000000000 42659685694973 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393563371/10000000000 : ℝ)^4145 ≤ (8809154670401/20000000000000 : ℝ)^3121 := by
    have hnat : (5393563371 : ℕ)^4145*20000000000000^3121 ≤ 8809154670401^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393563371 10000000000 8809154670401 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-547148421/2500000000 : ℝ), (5265259793/10000000000 : ℝ), (5393563371/10000000000 : ℝ)] ![(6647270468567/50000000000000 : ℝ), (42659685694973/100000000000000 : ℝ), (8809154670401/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-547148421/2500000000 : ℝ)|^4145 ≤ (6647270468567/50000000000000 : ℝ)^3121
        have hw : |(-547148421/2500000000 : ℝ)|=(547148421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265259793/10000000000 : ℝ)|^4145 ≤ (42659685694973/100000000000000 : ℝ)^3121
        have hw : |(5265259793/10000000000 : ℝ)|=(5265259793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393563371/10000000000 : ℝ)|^4145 ≤ (8809154670401/20000000000000 : ℝ)^3121
        have hw : |(5393563371/10000000000 : ℝ)|=(5393563371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s7_5 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312358179/10000000000 : ℝ)*x 0 + (-531345133/2500000000 : ℝ)*x 1 + (5393563369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312358179/10000000000 : ℝ)^4145 ≤ (21583612806093/50000000000000 : ℝ)^3121 := by
    have hnat : (5312358179 : ℕ)^4145*50000000000000^3121 ≤ 21583612806093^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312358179 10000000000 21583612806093 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531345133/2500000000 : ℝ)^4145 ≤ (12787001038827/100000000000000 : ℝ)^3121 := by
    have hnat : (531345133 : ℕ)^4145*100000000000000^3121 ≤ 12787001038827^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531345133 2500000000 12787001038827 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393563369/10000000000 : ℝ)^4145 ≤ (44045773330313/100000000000000 : ℝ)^3121 := by
    have hnat : (5393563369 : ℕ)^4145*100000000000000^3121 ≤ 44045773330313^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393563369 10000000000 44045773330313 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312358179/10000000000 : ℝ), (-531345133/2500000000 : ℝ), (5393563369/10000000000 : ℝ)] ![(21583612806093/50000000000000 : ℝ), (12787001038827/100000000000000 : ℝ), (44045773330313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312358179/10000000000 : ℝ)|^4145 ≤ (21583612806093/50000000000000 : ℝ)^3121
        have hw : |(5312358179/10000000000 : ℝ)|=(5312358179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-531345133/2500000000 : ℝ)|^4145 ≤ (12787001038827/100000000000000 : ℝ)^3121
        have hw : |(-531345133/2500000000 : ℝ)|=(531345133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393563369/10000000000 : ℝ)|^4145 ≤ (44045773330313/100000000000000 : ℝ)^3121
        have hw : |(5393563369/10000000000 : ℝ)|=(5393563369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s7_6 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656179091/5000000000 : ℝ)*x 0 + (5393563367/10000000000 : ℝ)*x 1 + (-2125380531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656179091/5000000000 : ℝ)^4145 ≤ (21583612822281/50000000000000 : ℝ)^3121 := by
    have hnat : (2656179091 : ℕ)^4145*50000000000000^3121 ≤ 21583612822281^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656179091 5000000000 21583612822281 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393563367/10000000000 : ℝ)^4145 ≤ (22022886654311/50000000000000 : ℝ)^3121 := by
    have hnat : (5393563367 : ℕ)^4145*50000000000000^3121 ≤ 22022886654311^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393563367 10000000000 22022886654311 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125380531/10000000000 : ℝ)^4145 ≤ (12787001030837/100000000000000 : ℝ)^3121 := by
    have hnat : (2125380531 : ℕ)^4145*100000000000000^3121 ≤ 12787001030837^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125380531 10000000000 12787001030837 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656179091/5000000000 : ℝ), (5393563367/10000000000 : ℝ), (-2125380531/10000000000 : ℝ)] ![(21583612822281/50000000000000 : ℝ), (22022886654311/50000000000000 : ℝ), (12787001030837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656179091/5000000000 : ℝ)|^4145 ≤ (21583612822281/50000000000000 : ℝ)^3121
        have hw : |(2656179091/5000000000 : ℝ)|=(2656179091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393563367/10000000000 : ℝ)|^4145 ≤ (22022886654311/50000000000000 : ℝ)^3121
        have hw : |(5393563367/10000000000 : ℝ)|=(5393563367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2125380531/10000000000 : ℝ)|^4145 ≤ (12787001030837/100000000000000 : ℝ)^3121
        have hw : |(-2125380531/10000000000 : ℝ)|=(2125380531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s7_7 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (546382347/1250000000 : ℝ)*x 0 + (899882497/2000000000 : ℝ)*x 1 + (2123203451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546382347/1250000000 : ℝ)^4145 ≤ (33316788855067/100000000000000 : ℝ)^3121 := by
    have hnat : (546382347 : ℕ)^4145*100000000000000^3121 ≤ 33316788855067^3121*1250000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546382347 1250000000 33316788855067 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899882497/2000000000 : ℝ)^4145 ≤ (17311162992409/50000000000000 : ℝ)^3121 := by
    have hnat : (899882497 : ℕ)^4145*50000000000000^3121 ≤ 17311162992409^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899882497 2000000000 17311162992409 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123203451/5000000000 : ℝ)^4145 ≤ (32060885143593/100000000000000 : ℝ)^3121 := by
    have hnat : (2123203451 : ℕ)^4145*100000000000000^3121 ≤ 32060885143593^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123203451 5000000000 32060885143593 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546382347/1250000000 : ℝ), (899882497/2000000000 : ℝ), (2123203451/5000000000 : ℝ)] ![(33316788855067/100000000000000 : ℝ), (17311162992409/50000000000000 : ℝ), (32060885143593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546382347/1250000000 : ℝ)|^4145 ≤ (33316788855067/100000000000000 : ℝ)^3121
        have hw : |(546382347/1250000000 : ℝ)|=(546382347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899882497/2000000000 : ℝ)|^4145 ≤ (17311162992409/50000000000000 : ℝ)^3121
        have hw : |(899882497/2000000000 : ℝ)|=(899882497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123203451/5000000000 : ℝ)|^4145 ≤ (32060885143593/100000000000000 : ℝ)^3121
        have hw : |(2123203451/5000000000 : ℝ)|=(2123203451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1097_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (877/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2823/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1753/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (877/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2821/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (877/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2821/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (877/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2821/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (877/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2821/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (877/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2821/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (877/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2821/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2821/25000 : ℝ) ^ (8289/2048 : ℝ) ≤ (14620891429480631/100000000000000000000 : ℝ) := by
    have hpowers : (2821/25000 : ℝ)^8289 ≤ (14620891429480631/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2821 : ℕ)^8289*100000000000000000000^2048 ≤ 14620891429480631^2048*25000^8289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2821 25000 14620891429480631 100000000000000000000 8289 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2821/25000 : ℝ)) (X := (14620891429480631/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (877/6250 : ℝ) ^ (8289/2048 : ℝ) ≤ (1413002987329953/4000000000000000000 : ℝ) := by
    have hpowers : (877/6250 : ℝ)^8289 ≤ (1413002987329953/4000000000000000000 : ℝ)^2048 := by
      have hnat : (877 : ℕ)^8289*4000000000000000000^2048 ≤ 1413002987329953^2048*6250^8289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        877 6250 1413002987329953 4000000000000000000 8289 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (877/6250 : ℝ)) (X := (1413002987329953/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014620891429480631/50000000000000000000 : ℝ) ≤ (10000722410179471/10000000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (50014620891429480631/50000000000000000000 : ℝ)^2048 ≤ (10000722410179471/10000000000000000 : ℝ)^8289 := by
      have hnat : (50014620891429480631 : ℕ)^2048*10000000000000000^8289 ≤ 10000722410179471^8289*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014620891429480631 50000000000000000000 10000722410179471 10000000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000722410179471/10000000000000000 : ℝ)) (X := (50014620891429480631/50000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253121622882045591/6250000000000000000 : ℝ) ≤ (5000616902587483/5000000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (6253121622882045591/6250000000000000000 : ℝ)^2048 ≤ (5000616902587483/5000000000000000 : ℝ)^8289 := by
      have hnat : (6253121622882045591 : ℕ)^2048*5000000000000000^8289 ≤ 5000616902587483^8289*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253121622882045591 6250000000000000000 5000616902587483 5000000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000616902587483/5000000000000000 : ℝ)) (X := (6253121622882045591/6250000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001413002987329953/2000000000000000000 : ℝ) ≤ (10001745200170461/10000000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (2001413002987329953/2000000000000000000 : ℝ)^2048 ≤ (10001745200170461/10000000000000000 : ℝ)^8289 := by
      have hnat : (2001413002987329953 : ℕ)^2048*10000000000000000^8289 ≤ 10001745200170461^8289*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001413002987329953 2000000000000000000 10001745200170461 10000000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001745200170461/10000000000000000 : ℝ)) (X := (2001413002987329953/2000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14620891429480631/100000000000000000000 : ℝ) ≤ ((6867611005228713787/6870000000000000000 : ℝ)+2*(102278999099/54960000000000 : ℝ)*(2821/25000 : ℝ))^(8289/2048 : ℝ) := by
    rw [show (6867611005228713787/6870000000000000000 : ℝ)+2*(102278999099/54960000000000 : ℝ)*(2821/25000 : ℝ)=(10000722410179471/10000000000000000 : ℝ) by norm_num, show 1+2*(14620891429480631/100000000000000000000 : ℝ)=(50014620891429480631/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1413002987329953/4000000000000000000 : ℝ)+(14620891429480631/100000000000000000000 : ℝ) ≤ ((6867611005228713787/6870000000000000000 : ℝ)+(102278999099/54960000000000 : ℝ)*((877/6250 : ℝ)+(2821/25000 : ℝ)))^(8289/2048 : ℝ) := by
    rw [show (6867611005228713787/6870000000000000000 : ℝ)+(102278999099/54960000000000 : ℝ)*((877/6250 : ℝ)+(2821/25000 : ℝ))=(5000616902587483/5000000000000000 : ℝ) by norm_num, show 1+(1413002987329953/4000000000000000000 : ℝ)+(14620891429480631/100000000000000000000 : ℝ)=(6253121622882045591/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1413002987329953/4000000000000000000 : ℝ) ≤ ((6867611005228713787/6870000000000000000 : ℝ)+2*(102278999099/54960000000000 : ℝ)*(877/6250 : ℝ))^(8289/2048 : ℝ) := by
    rw [show (6867611005228713787/6870000000000000000 : ℝ)+2*(102278999099/54960000000000 : ℝ)*(877/6250 : ℝ)=(10001745200170461/10000000000000000 : ℝ) by norm_num, show 1+2*(1413002987329953/4000000000000000000 : ℝ)=(2001413002987329953/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6867611005228713787/6870000000000000000 : ℝ)*(X 1 0+X 2 0)+(102278999099/54960000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (2821/25000 : ℝ)) (hi := (877/6250 : ℝ)) (c := (6867611005228713787/6870000000000000000 : ℝ)) (alpha := (102278999099/54960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6867611005228713787/6870000000000000000 : ℝ)*(X 0 1+X 2 1)+(102278999099/54960000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (2821/25000 : ℝ)) (hi := (877/6250 : ℝ)) (c := (6867611005228713787/6870000000000000000 : ℝ)) (alpha := (102278999099/54960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6867611005228713787/6870000000000000000 : ℝ)*(X 0 2+X 1 2)+(102278999099/54960000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (2821/25000 : ℝ)) (hi := (877/6250 : ℝ)) (c := (6867611005228713787/6870000000000000000 : ℝ)) (alpha := (102278999099/54960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-437717707/2000000000 : ℝ)*X 0 0+(5393888427/10000000000 : ℝ)*X 0 1+(5264936013/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336229417/2500000000 : ℝ)*X 1 0+(-11270039/50000000 : ℝ)*X 1 1+(5264936161/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672459011/5000000000 : ℝ)*X 2 0+(5264935919/10000000000 : ℝ)*X 2 1+(-45080153/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4371049021/10000000000 : ℝ)*X 0 0+(2122883117/5000000000 : ℝ)*X 0 1+(900010147/2000000000 : ℝ)*X 0 2+(4371049021/10000000000 : ℝ)*X 1 0+(2122883117/5000000000 : ℝ)*X 1 1+(900010147/2000000000 : ℝ)*X 1 2+(4371049021/10000000000 : ℝ)*X 2 0+(2122883117/5000000000 : ℝ)*X 2 1+(900010147/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-547148421/2500000000 : ℝ)*X 0 0+(5265259793/10000000000 : ℝ)*X 0 1+(5393563371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312358179/10000000000 : ℝ)*X 1 0+(-531345133/2500000000 : ℝ)*X 1 1+(5393563369/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656179091/5000000000 : ℝ)*X 2 0+(5393563367/10000000000 : ℝ)*X 2 1+(-2125380531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((546382347/1250000000 : ℝ)*X 0 0+(899882497/2000000000 : ℝ)*X 0 1+(2123203451/5000000000 : ℝ)*X 0 2+(546382347/1250000000 : ℝ)*X 1 0+(899882497/2000000000 : ℝ)*X 1 1+(2123203451/5000000000 : ℝ)*X 1 2+(546382347/1250000000 : ℝ)*X 2 0+(899882497/2000000000 : ℝ)*X 2 1+(2123203451/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (765793536888511207983/91600000000000000000000000 : ℝ) := by norm_num
    linear_combination (445928147/25000000000000 : ℝ)*(base19) + (1886742079/100000000000000 : ℝ)*(base23) + (109727767/50000000000000 : ℝ)*(lower2) + (119954957/100000000000000 : ℝ)*(upper3) + (149531317/100000000000000 : ℝ)*(upper5) + (2921892547936327/50000000000000 : ℝ)*(major0) + (2921892547936327/50000000000000 : ℝ)*(major1) + (2921892547936327/50000000000000 : ℝ)*(major2) + (7754850470962469/100000000000000 : ℝ)*(sp0) + (7754913946857639/100000000000000 : ℝ)*(sp1) + (7754913843828147/100000000000000 : ℝ)*(sp2) + (1966313187858961/50000000000000 : ℝ)*(sp3) + (32629803879/50000000000000 : ℝ)*(sp4) + (27806784101/100000000000000 : ℝ)*(sp7) + (1966327091251011/50000000000000 : ℝ)*(f.failure) + (7754915730570227/100000000000000 : ℝ)*(f.sum) + (7651045806901/1374000000000000000000000000 : ℝ)*base66 + (976695517860334651/343500000000000000000000000000000 : ℝ)*base68 + (1496513723329834651/343500000000000000000000000000000 : ℝ)*base70 + (3042813184889665349/343500000000000000000000000000000 : ℝ)*base71 + (7762176550969/1374000000000000000000000000 : ℝ)*base74 + (2425494209563834651/343500000000000000000000000000000 : ℝ)*base76 + (88953847172665349/343500000000000000000000000000000 : ℝ)*base77 + (1989498520823665349/343500000000000000000000000000000 : ℝ)*base79 + (2282345519531/274800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (7544777/1000000000000000000000 : ℝ)*base90 + (7544777/1000000000000000000000 : ℝ)*base92 + (7544777/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1060988928296860569093217177/114500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1696314263/100000000000000 : ℝ)*(base19) + (926844573/50000000000000 : ℝ)*(base23) + (18376747/10000000000000 : ℝ)*(upper3) + (69379169/100000000000000 : ℝ)*(lower4) + (46941289/25000000000000 : ℝ)*(upper5) + (5873247475259029/100000000000000 : ℝ)*(major0) + (5873247475259029/100000000000000 : ℝ)*(major1) + (5873247475259029/100000000000000 : ℝ)*(major2) + (1853636267/4000000000000 : ℝ)*(sp1) + (9998171049/20000000000000 : ℝ)*(sp2) + (3897006676314787/50000000000000 : ℝ)*(sp4) + (1948491328852159/25000000000000 : ℝ)*(sp5) + (3896980754042591/50000000000000 : ℝ)*(sp6) + (1976240644506257/50000000000000 : ℝ)*(sp7) + (1976240644506257/50000000000000 : ℝ)*(f.failure) + (3897006676314787/50000000000000 : ℝ)*(f.sum) + (15170785042633/2748000000000000000000000000 : ℝ)*base66 + (2827795856076592177/687000000000000000000000000000000 : ℝ)*base68 + (4895217618353407823/687000000000000000000000000000000 : ℝ)*base69 + (3176953394508592177/687000000000000000000000000000000 : ℝ)*base72 + (10955863318753/2748000000000000000000000000 : ℝ)*base74 + (11578425475118407823/687000000000000000000000000000000 : ℝ)*base75 + (10964311784501407823/687000000000000000000000000000000 : ℝ)*base77 + (6738091918994407823/687000000000000000000000000000000 : ℝ)*base79 + (9079687747657/2748000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2116301/1000000000000000000000 : ℝ)*base89 + (2116301/1000000000000000000000 : ℝ)*base91 + (2116301/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1097_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (877/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1097_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1097_s8_0 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2188594721/10000000000 : ℝ)*x 0 + (5393805229/10000000000 : ℝ)*x 1 + (1316253809/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188594721/10000000000 : ℝ)^4145 ≤ (3323637325783/25000000000000 : ℝ)^3121 := by
    have hnat : (2188594721 : ℕ)^4145*25000000000000^3121 ≤ 3323637325783^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188594721 10000000000 3323637325783 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393805229/10000000000 : ℝ)^4145 ≤ (22024198250237/50000000000000 : ℝ)^3121 := by
    have hnat : (5393805229 : ℕ)^4145*50000000000000^3121 ≤ 22024198250237^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393805229 10000000000 22024198250237 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316253809/2500000000 : ℝ)^4145 ≤ (21328527091343/50000000000000 : ℝ)^3121 := by
    have hnat : (1316253809 : ℕ)^4145*50000000000000^3121 ≤ 21328527091343^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316253809 2500000000 21328527091343 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2188594721/10000000000 : ℝ), (5393805229/10000000000 : ℝ), (1316253809/2500000000 : ℝ)] ![(3323637325783/25000000000000 : ℝ), (22024198250237/50000000000000 : ℝ), (21328527091343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2188594721/10000000000 : ℝ)|^4145 ≤ (3323637325783/25000000000000 : ℝ)^3121
        have hw : |(-2188594721/10000000000 : ℝ)|=(2188594721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393805229/10000000000 : ℝ)|^4145 ≤ (22024198250237/50000000000000 : ℝ)^3121
        have hw : |(5393805229/10000000000 : ℝ)|=(5393805229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316253809/2500000000 : ℝ)|^4145 ≤ (21328527091343/50000000000000 : ℝ)^3121
        have hw : |(1316253809/2500000000 : ℝ)|=(1316253809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s8_1 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344897303/10000000000 : ℝ)*x 0 + (-563482599/2500000000 : ℝ)*x 1 + (210600609/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344897303/10000000000 : ℝ)^4145 ≤ (5439842083569/12500000000000 : ℝ)^3121 := by
    have hnat : (5344897303 : ℕ)^4145*12500000000000^3121 ≤ 5439842083569^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344897303 10000000000 5439842083569 12500000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563482599/2500000000 : ℝ)^4145 ≤ (13824209263723/100000000000000 : ℝ)^3121 := by
    have hnat : (563482599 : ℕ)^4145*100000000000000^3121 ≤ 13824209263723^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563482599 2500000000 13824209263723 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210600609/400000000 : ℝ)^4145 ≤ (10664263516081/25000000000000 : ℝ)^3121 := by
    have hnat : (210600609 : ℕ)^4145*25000000000000^3121 ≤ 10664263516081^3121*400000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210600609 400000000 10664263516081 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344897303/10000000000 : ℝ), (-563482599/2500000000 : ℝ), (210600609/400000000 : ℝ)] ![(5439842083569/12500000000000 : ℝ), (13824209263723/100000000000000 : ℝ), (10664263516081/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344897303/10000000000 : ℝ)|^4145 ≤ (5439842083569/12500000000000 : ℝ)^3121
        have hw : |(5344897303/10000000000 : ℝ)|=(5344897303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-563482599/2500000000 : ℝ)|^4145 ≤ (13824209263723/100000000000000 : ℝ)^3121
        have hw : |(-563482599/2500000000 : ℝ)|=(563482599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210600609/400000000 : ℝ)|^4145 ≤ (10664263516081/25000000000000 : ℝ)^3121
        have hw : |(210600609/400000000 : ℝ)|=(210600609/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s8_2 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344897303/10000000000 : ℝ)*x 0 + (1316253801/2500000000 : ℝ)*x 1 + (-1126965211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344897303/10000000000 : ℝ)^4145 ≤ (5439842083569/12500000000000 : ℝ)^3121 := by
    have hnat : (5344897303 : ℕ)^4145*12500000000000^3121 ≤ 5439842083569^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344897303 10000000000 5439842083569 12500000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316253801/2500000000 : ℝ)^4145 ≤ (42657053838359/100000000000000 : ℝ)^3121 := by
    have hnat : (1316253801 : ℕ)^4145*100000000000000^3121 ≤ 42657053838359^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316253801 2500000000 42657053838359 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126965211/5000000000 : ℝ)^4145 ≤ (13824209475513/100000000000000 : ℝ)^3121 := by
    have hnat : (1126965211 : ℕ)^4145*100000000000000^3121 ≤ 13824209475513^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126965211 5000000000 13824209475513 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344897303/10000000000 : ℝ), (1316253801/2500000000 : ℝ), (-1126965211/5000000000 : ℝ)] ![(5439842083569/12500000000000 : ℝ), (42657053838359/100000000000000 : ℝ), (13824209475513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344897303/10000000000 : ℝ)|^4145 ≤ (5439842083569/12500000000000 : ℝ)^3121
        have hw : |(5344897303/10000000000 : ℝ)|=(5344897303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316253801/2500000000 : ℝ)|^4145 ≤ (42657053838359/100000000000000 : ℝ)^3121
        have hw : |(1316253801/2500000000 : ℝ)|=(1316253801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1126965211/5000000000 : ℝ)|^4145 ≤ (13824209475513/100000000000000 : ℝ)^3121
        have hw : |(-1126965211/5000000000 : ℝ)|=(1126965211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s8_3 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (546381631/1250000000 : ℝ)*x 0 + (4245925597/10000000000 : ℝ)*x 1 + (2249945197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546381631/1250000000 : ℝ)^4145 ≤ (33316730870799/100000000000000 : ℝ)^3121 := by
    have hnat : (546381631 : ℕ)^4145*100000000000000^3121 ≤ 33316730870799^3121*1250000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546381631 1250000000 33316730870799 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4245925597/10000000000 : ℝ)^4145 ≤ (6411211807277/20000000000000 : ℝ)^3121 := by
    have hnat : (4245925597 : ℕ)^4145*20000000000000^3121 ≤ 6411211807277^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245925597 10000000000 6411211807277 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249945197/5000000000 : ℝ)^4145 ≤ (34627210078379/100000000000000 : ℝ)^3121 := by
    have hnat : (2249945197 : ℕ)^4145*100000000000000^3121 ≤ 34627210078379^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249945197 5000000000 34627210078379 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546381631/1250000000 : ℝ), (4245925597/10000000000 : ℝ), (2249945197/5000000000 : ℝ)] ![(33316730870799/100000000000000 : ℝ), (6411211807277/20000000000000 : ℝ), (34627210078379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546381631/1250000000 : ℝ)|^4145 ≤ (33316730870799/100000000000000 : ℝ)^3121
        have hw : |(546381631/1250000000 : ℝ)|=(546381631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4245925597/10000000000 : ℝ)|^4145 ≤ (6411211807277/20000000000000 : ℝ)^3121
        have hw : |(4245925597/10000000000 : ℝ)|=(4245925597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249945197/5000000000 : ℝ)|^4145 ≤ (34627210078379/100000000000000 : ℝ)^3121
        have hw : |(2249945197/5000000000 : ℝ)|=(2249945197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s8_4 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2188599741/10000000000 : ℝ)*x 0 + (41135453/78125000 : ℝ)*x 1 + (5393481289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188599741/10000000000 : ℝ)^4145 ≤ (3323647450501/25000000000000 : ℝ)^3121 := by
    have hnat : (2188599741 : ℕ)^4145*25000000000000^3121 ≤ 3323647450501^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188599741 10000000000 3323647450501 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41135453/78125000 : ℝ)^4145 ≤ (42660527063841/100000000000000 : ℝ)^3121 := by
    have hnat : (41135453 : ℕ)^4145*100000000000000^3121 ≤ 42660527063841^3121*78125000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41135453 78125000 42660527063841 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393481289/10000000000 : ℝ)^4145 ≤ (44044883114133/100000000000000 : ℝ)^3121 := by
    have hnat : (5393481289 : ℕ)^4145*100000000000000^3121 ≤ 44044883114133^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393481289 10000000000 44044883114133 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2188599741/10000000000 : ℝ), (41135453/78125000 : ℝ), (5393481289/10000000000 : ℝ)] ![(3323647450501/25000000000000 : ℝ), (42660527063841/100000000000000 : ℝ), (44044883114133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2188599741/10000000000 : ℝ)|^4145 ≤ (3323647450501/25000000000000 : ℝ)^3121
        have hw : |(-2188599741/10000000000 : ℝ)|=(2188599741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41135453/78125000 : ℝ)|^4145 ≤ (42660527063841/100000000000000 : ℝ)^3121
        have hw : |(41135453/78125000 : ℝ)|=(41135453/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393481289/10000000000 : ℝ)|^4145 ≤ (44044883114133/100000000000000 : ℝ)^3121
        have hw : |(5393481289/10000000000 : ℝ)|=(5393481289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s8_5 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312378793/10000000000 : ℝ)*x 0 + (-1062732009/5000000000 : ℝ)*x 1 + (5393481351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312378793/10000000000 : ℝ)^4145 ≤ (43167448076371/100000000000000 : ℝ)^3121 := by
    have hnat : (5312378793 : ℕ)^4145*100000000000000^3121 ≤ 43167448076371^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312378793 10000000000 43167448076371 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062732009/5000000000 : ℝ)^4145 ≤ (511506724833/4000000000000 : ℝ)^3121 := by
    have hnat : (1062732009 : ℕ)^4145*4000000000000^3121 ≤ 511506724833^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062732009 5000000000 511506724833 4000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393481351/10000000000 : ℝ)^4145 ≤ (22022441893283/50000000000000 : ℝ)^3121 := by
    have hnat : (5393481351 : ℕ)^4145*50000000000000^3121 ≤ 22022441893283^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393481351 10000000000 22022441893283 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312378793/10000000000 : ℝ), (-1062732009/5000000000 : ℝ), (5393481351/10000000000 : ℝ)] ![(43167448076371/100000000000000 : ℝ), (511506724833/4000000000000 : ℝ), (22022441893283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312378793/10000000000 : ℝ)|^4145 ≤ (43167448076371/100000000000000 : ℝ)^3121
        have hw : |(5312378793/10000000000 : ℝ)|=(5312378793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1062732009/5000000000 : ℝ)|^4145 ≤ (511506724833/4000000000000 : ℝ)^3121
        have hw : |(-1062732009/5000000000 : ℝ)|=(1062732009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393481351/10000000000 : ℝ)|^4145 ≤ (22022441893283/50000000000000 : ℝ)^3121
        have hw : |(5393481351/10000000000 : ℝ)|=(5393481351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s8_6 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26561891/50000000 : ℝ)*x 0 + (1078696251/2000000000 : ℝ)*x 1 + (-42509299/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26561891/50000000 : ℝ)^4145 ≤ (10791860419193/25000000000000 : ℝ)^3121 := by
    have hnat : (26561891 : ℕ)^4145*25000000000000^3121 ≤ 10791860419193^3121*50000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26561891 50000000 10791860419193 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078696251/2000000000 : ℝ)^4145 ≤ (2202244137269/5000000000000 : ℝ)^3121 := by
    have hnat : (1078696251 : ℕ)^4145*5000000000000^3121 ≤ 2202244137269^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078696251 2000000000 2202244137269 5000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42509299/200000000 : ℝ)^4145 ≤ (102301404543/800000000000 : ℝ)^3121 := by
    have hnat : (42509299 : ℕ)^4145*800000000000^3121 ≤ 102301404543^3121*200000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42509299 200000000 102301404543 800000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26561891/50000000 : ℝ), (1078696251/2000000000 : ℝ), (-42509299/200000000 : ℝ)] ![(10791860419193/25000000000000 : ℝ), (2202244137269/5000000000000 : ℝ), (102301404543/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26561891/50000000 : ℝ)|^4145 ≤ (10791860419193/25000000000000 : ℝ)^3121
        have hw : |(26561891/50000000 : ℝ)|=(26561891/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078696251/2000000000 : ℝ)|^4145 ≤ (2202244137269/5000000000000 : ℝ)^3121
        have hw : |(1078696251/2000000000 : ℝ)|=(1078696251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-42509299/200000000 : ℝ)|^4145 ≤ (102301404543/800000000000 : ℝ)^3121
        have hw : |(-42509299/200000000 : ℝ)|=(42509299/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s8_7 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4371062337/10000000000 : ℝ)*x 0 + (4499253771/10000000000 : ℝ)*x 1 + (2123282531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371062337/10000000000 : ℝ)^4145 ≤ (3331682490291/10000000000000 : ℝ)^3121 := by
    have hnat : (4371062337 : ℕ)^4145*10000000000000^3121 ≤ 3331682490291^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371062337 10000000000 3331682490291 10000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4499253771/10000000000 : ℝ)^4145 ≤ (8655176002673/25000000000000 : ℝ)^3121 := by
    have hnat : (4499253771 : ℕ)^4145*25000000000000^3121 ≤ 8655176002673^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499253771 10000000000 8655176002673 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123282531/5000000000 : ℝ)^4145 ≤ (32062471073457/100000000000000 : ℝ)^3121 := by
    have hnat : (2123282531 : ℕ)^4145*100000000000000^3121 ≤ 32062471073457^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123282531 5000000000 32062471073457 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371062337/10000000000 : ℝ), (4499253771/10000000000 : ℝ), (2123282531/5000000000 : ℝ)] ![(3331682490291/10000000000000 : ℝ), (8655176002673/25000000000000 : ℝ), (32062471073457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371062337/10000000000 : ℝ)|^4145 ≤ (3331682490291/10000000000000 : ℝ)^3121
        have hw : |(4371062337/10000000000 : ℝ)|=(4371062337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4499253771/10000000000 : ℝ)|^4145 ≤ (8655176002673/25000000000000 : ℝ)^3121
        have hw : |(4499253771/10000000000 : ℝ)|=(4499253771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123282531/5000000000 : ℝ)|^4145 ≤ (32062471073457/100000000000000 : ℝ)^3121
        have hw : |(2123282531/5000000000 : ℝ)|=(2123282531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1097_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5647/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7011/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1753/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2823/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1753/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2823/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1753/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2823/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1753/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2823/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1753/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2823/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1753/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2823/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2823/25000 : ℝ) ^ (8289/2048 : ℝ) ≤ (7331445365404163/50000000000000000000 : ℝ) := by
    have hpowers : (2823/25000 : ℝ)^8289 ≤ (7331445365404163/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2823 : ℕ)^8289*50000000000000000000^2048 ≤ 7331445365404163^2048*25000^8289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2823 25000 7331445365404163 50000000000000000000 8289 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2823/25000 : ℝ)) (X := (7331445365404163/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1753/12500 : ℝ) ^ (8289/2048 : ℝ) ≤ (35243632688393579/100000000000000000000 : ℝ) := by
    have hpowers : (1753/12500 : ℝ)^8289 ≤ (35243632688393579/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1753 : ℕ)^8289*100000000000000000000^2048 ≤ 35243632688393579^2048*12500^8289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1753 12500 35243632688393579 100000000000000000000 8289 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1753/12500 : ℝ)) (X := (35243632688393579/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007331445365404163/25000000000000000000 : ℝ) ≤ (10000724485112733/10000000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (25007331445365404163/25000000000000000000 : ℝ)^2048 ≤ (10000724485112733/10000000000000000 : ℝ)^8289 := by
      have hnat : (25007331445365404163 : ℕ)^2048*10000000000000000^8289 ≤ 10000724485112733^8289*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007331445365404163 25000000000000000000 10000724485112733 10000000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000724485112733/10000000000000000 : ℝ)) (X := (25007331445365404163/25000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009981304683840381/20000000000000000000 : ℝ) ≤ (2500308207753253/2500000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (20009981304683840381/20000000000000000000 : ℝ)^2048 ≤ (2500308207753253/2500000000000000 : ℝ)^8289 := by
      have hnat : (20009981304683840381 : ℕ)^2048*2500000000000000^8289 ≤ 2500308207753253^8289*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009981304683840381 20000000000000000000 2500308207753253 2500000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500308207753253/2500000000000000 : ℝ)) (X := (20009981304683840381/20000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035243632688393579/50000000000000000000 : ℝ) ≤ (10001741176913291/10000000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (50035243632688393579/50000000000000000000 : ℝ)^2048 ≤ (10001741176913291/10000000000000000 : ℝ)^8289 := by
      have hnat : (50035243632688393579 : ℕ)^2048*10000000000000000^8289 ≤ 10001741176913291^8289*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035243632688393579 50000000000000000000 10001741176913291 10000000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001741176913291/10000000000000000 : ℝ)) (X := (50035243632688393579/50000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7331445365404163/50000000000000000000 : ℝ) ≤ ((1365524940475804281/1366000000000000000 : ℝ)+2*(508345900279/273200000000000 : ℝ)*(2823/25000 : ℝ))^(8289/2048 : ℝ) := by
    rw [show (1365524940475804281/1366000000000000000 : ℝ)+2*(508345900279/273200000000000 : ℝ)*(2823/25000 : ℝ)=(10000724485112733/10000000000000000 : ℝ) by norm_num, show 1+2*(7331445365404163/50000000000000000000 : ℝ)=(25007331445365404163/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35243632688393579/100000000000000000000 : ℝ)+(7331445365404163/50000000000000000000 : ℝ) ≤ ((1365524940475804281/1366000000000000000 : ℝ)+(508345900279/273200000000000 : ℝ)*((1753/12500 : ℝ)+(2823/25000 : ℝ)))^(8289/2048 : ℝ) := by
    rw [show (1365524940475804281/1366000000000000000 : ℝ)+(508345900279/273200000000000 : ℝ)*((1753/12500 : ℝ)+(2823/25000 : ℝ))=(2500308207753253/2500000000000000 : ℝ) by norm_num, show 1+(35243632688393579/100000000000000000000 : ℝ)+(7331445365404163/50000000000000000000 : ℝ)=(20009981304683840381/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35243632688393579/100000000000000000000 : ℝ) ≤ ((1365524940475804281/1366000000000000000 : ℝ)+2*(508345900279/273200000000000 : ℝ)*(1753/12500 : ℝ))^(8289/2048 : ℝ) := by
    rw [show (1365524940475804281/1366000000000000000 : ℝ)+2*(508345900279/273200000000000 : ℝ)*(1753/12500 : ℝ)=(10001741176913291/10000000000000000 : ℝ) by norm_num, show 1+2*(35243632688393579/100000000000000000000 : ℝ)=(50035243632688393579/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1365524940475804281/1366000000000000000 : ℝ)*(X 1 0+X 2 0)+(508345900279/273200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (2823/25000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (1365524940475804281/1366000000000000000 : ℝ)) (alpha := (508345900279/273200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1365524940475804281/1366000000000000000 : ℝ)*(X 0 1+X 2 1)+(508345900279/273200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (2823/25000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (1365524940475804281/1366000000000000000 : ℝ)) (alpha := (508345900279/273200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1365524940475804281/1366000000000000000 : ℝ)*(X 0 2+X 1 2)+(508345900279/273200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (2823/25000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (1365524940475804281/1366000000000000000 : ℝ)) (alpha := (508345900279/273200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2188594721/10000000000 : ℝ)*X 0 0+(5393805229/10000000000 : ℝ)*X 0 1+(1316253809/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344897303/10000000000 : ℝ)*X 1 0+(-563482599/2500000000 : ℝ)*X 1 1+(210600609/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344897303/10000000000 : ℝ)*X 2 0+(1316253801/2500000000 : ℝ)*X 2 1+(-1126965211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((546381631/1250000000 : ℝ)*X 0 0+(4245925597/10000000000 : ℝ)*X 0 1+(2249945197/5000000000 : ℝ)*X 0 2+(546381631/1250000000 : ℝ)*X 1 0+(4245925597/10000000000 : ℝ)*X 1 1+(2249945197/5000000000 : ℝ)*X 1 2+(546381631/1250000000 : ℝ)*X 2 0+(4245925597/10000000000 : ℝ)*X 2 1+(2249945197/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2188599741/10000000000 : ℝ)*X 0 0+(41135453/78125000 : ℝ)*X 0 1+(5393481289/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312378793/10000000000 : ℝ)*X 1 0+(-1062732009/5000000000 : ℝ)*X 1 1+(5393481351/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((26561891/50000000 : ℝ)*X 2 0+(1078696251/2000000000 : ℝ)*X 2 1+(-42509299/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4371062337/10000000000 : ℝ)*X 0 0+(4499253771/10000000000 : ℝ)*X 0 1+(2123282531/5000000000 : ℝ)*X 0 2+(4371062337/10000000000 : ℝ)*X 1 0+(4499253771/10000000000 : ℝ)*X 1 1+(2123282531/5000000000 : ℝ)*X 1 2+(4371062337/10000000000 : ℝ)*X 2 0+(4499253771/10000000000 : ℝ)*X 2 1+(2123282531/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49933576679570314238166831/8537500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7618971/625000000000 : ℝ)*(base19) + (1128918983/100000000000000 : ℝ)*(base23) + (48166281/100000000000000 : ℝ)*(lower2) + (86858761/50000000000000 : ℝ)*(upper3) + (64342281/100000000000000 : ℝ)*(upper5) + (1462778900555483/25000000000000 : ℝ)*(major0) + (1462778900555483/25000000000000 : ℝ)*(major1) + (1462778900555483/25000000000000 : ℝ)*(major2) + (3882306459944923/50000000000000 : ℝ)*(sp0) + (485290152787477/6250000000000 : ℝ)*(sp1) + (7764642534716009/100000000000000 : ℝ)*(sp2) + (393756906962403/10000000000000 : ℝ)*(sp3) + (6148749029/20000000000000 : ℝ)*(sp4) + (2284528373/12500000000000 : ℝ)*(sp7) + (1968793672925507/50000000000000 : ℝ)*(f.failure) + (485290228977187/6250000000000 : ℝ)*(f.sum) + (13186853552799/1707500000000000000000000000 : ℝ)*base66 + (885336504148007723/34150000000000000000000000000000 : ℝ)*base67 + (363816780303857723/34150000000000000000000000000000 : ℝ)*base69 + (402463156639392277/34150000000000000000000000000000 : ℝ)*base72 + (18891763878427/3415000000000000000000000000 : ℝ)*base73 + (994375642832007723/34150000000000000000000000000000 : ℝ)*base75 + (608942666821957723/34150000000000000000000000000000 : ℝ)*base77 + (428945371536707723/34150000000000000000000000000000 : ℝ)*base79 + (3193166547693/3415000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (10293449/1000000000000000000000 : ℝ)*base90 + (10293449/1000000000000000000000 : ℝ)*base92 + (10293449/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7385045442964851647530671/853750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (637127549/50000000000000 : ℝ)*(base19) + (95572853/25000000000000 : ℝ)*(base23) + (34560227/20000000000000 : ℝ)*(upper2) + (65978753/100000000000000 : ℝ)*(upper3) + (48078803/50000000000000 : ℝ)*(upper5) + (147015014770603/2500000000000 : ℝ)*(major0) + (147015014770603/2500000000000 : ℝ)*(major1) + (147015014770603/2500000000000 : ℝ)*(major2) + (1222461463/10000000000000 : ℝ)*(sp0) + (1130940017/2000000000000 : ℝ)*(sp1) + (1950939750289277/25000000000000 : ℝ)*(sp4) + (7803713404515791/100000000000000 : ℝ)*(sp5) + (3901885421740163/50000000000000 : ℝ)*(sp6) + (1978714833769471/50000000000000 : ℝ)*(sp7) + (1978714833769471/50000000000000 : ℝ)*(f.failure) + (7803771225771739/100000000000000 : ℝ)*(f.sum) + (9983054193697/341500000000000000000000000 : ℝ)*base66 + (27709112717576443/3415000000000000000000000000000 : ℝ)*base67 + (89747510535696443/3415000000000000000000000000000 : ℝ)*base69 + (22297464605268557/3415000000000000000000000000000 : ℝ)*base72 + (249598789111/341500000000000000000000000 : ℝ)*base73 + (25697136539111443/3415000000000000000000000000000 : ℝ)*base75 + (6642729598126443/3415000000000000000000000000000 : ℝ)*base77 + (18371141539556443/3415000000000000000000000000000 : ℝ)*base79 + (1087173552821/341500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (3104003/1000000000000000000000 : ℝ)*base89 + (3104003/1000000000000000000000 : ℝ)*base91 + (3104003/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1097_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7011/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1097_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1097_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7011/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1097_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1097_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1097_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7011/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1097_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

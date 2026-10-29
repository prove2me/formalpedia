-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1377_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:22:43.599987+00:00
-- url     : https://prove2.me/submissions/82d3aa3b-998f-43f4-9ec9-1a1198236748

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
theorem support_rectangle_w1377_s6_0 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2014115537/10000000000 : ℝ)*x 0 + (5410907671/10000000000 : ℝ)*x 1 + (5245614657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014115537/10000000000 : ℝ)^4337 ≤ (12274025100893/100000000000000 : ℝ)^3313 := by
    have hnat : (2014115537 : ℕ)^4337*100000000000000^3313 ≤ 12274025100893^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014115537 10000000000 12274025100893 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410907671/10000000000 : ℝ)^4337 ≤ (22376791307523/50000000000000 : ℝ)^3313 := by
    have hnat : (5410907671 : ℕ)^4337*50000000000000^3313 ≤ 22376791307523^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410907671 10000000000 22376791307523 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245614657/10000000000 : ℝ)^4337 ≤ (42972392274851/100000000000000 : ℝ)^3313 := by
    have hnat : (5245614657 : ℕ)^4337*100000000000000^3313 ≤ 42972392274851^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245614657 10000000000 42972392274851 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2014115537/10000000000 : ℝ), (5410907671/10000000000 : ℝ), (5245614657/10000000000 : ℝ)] ![(12274025100893/100000000000000 : ℝ), (22376791307523/50000000000000 : ℝ), (42972392274851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2014115537/10000000000 : ℝ)|^4337 ≤ (12274025100893/100000000000000 : ℝ)^3313
        have hw : |(-2014115537/10000000000 : ℝ)|=(2014115537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410907671/10000000000 : ℝ)|^4337 ≤ (22376791307523/50000000000000 : ℝ)^3313
        have hw : |(5410907671/10000000000 : ℝ)|=(5410907671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245614657/10000000000 : ℝ)|^4337 ≤ (42972392274851/100000000000000 : ℝ)^3313
        have hw : |(5245614657/10000000000 : ℝ)|=(5245614657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s6_1 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348367401/10000000000 : ℝ)*x 0 + (-524576553/2500000000 : ℝ)*x 1 + (1311403743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348367401/10000000000 : ℝ)^4337 ≤ (11019411139829/25000000000000 : ℝ)^3313 := by
    have hnat : (5348367401 : ℕ)^4337*25000000000000^3313 ≤ 11019411139829^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348367401 10000000000 11019411139829 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524576553/2500000000 : ℝ)^4337 ≤ (6474979886787/50000000000000 : ℝ)^3313 := by
    have hnat : (524576553 : ℕ)^4337*50000000000000^3313 ≤ 6474979886787^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524576553 2500000000 6474979886787 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311403743/2500000000 : ℝ)^4337 ≤ (8594479130589/20000000000000 : ℝ)^3313 := by
    have hnat : (1311403743 : ℕ)^4337*20000000000000^3313 ≤ 8594479130589^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311403743 2500000000 8594479130589 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348367401/10000000000 : ℝ), (-524576553/2500000000 : ℝ), (1311403743/2500000000 : ℝ)] ![(11019411139829/25000000000000 : ℝ), (6474979886787/50000000000000 : ℝ), (8594479130589/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348367401/10000000000 : ℝ)|^4337 ≤ (11019411139829/25000000000000 : ℝ)^3313
        have hw : |(5348367401/10000000000 : ℝ)|=(5348367401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-524576553/2500000000 : ℝ)|^4337 ≤ (6474979886787/50000000000000 : ℝ)^3313
        have hw : |(-524576553/2500000000 : ℝ)|=(524576553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311403743/2500000000 : ℝ)|^4337 ≤ (8594479130589/20000000000000 : ℝ)^3313
        have hw : |(1311403743/2500000000 : ℝ)|=(1311403743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s6_2 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674183757/5000000000 : ℝ)*x 0 + (5245614721/10000000000 : ℝ)*x 1 + (-1049153197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674183757/5000000000 : ℝ)^4337 ≤ (11019411444607/25000000000000 : ℝ)^3313 := by
    have hnat : (2674183757 : ℕ)^4337*25000000000000^3313 ≤ 11019411444607^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674183757 5000000000 11019411444607 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245614721/10000000000 : ℝ)^4337 ≤ (21486196480597/50000000000000 : ℝ)^3313 := by
    have hnat : (5245614721 : ℕ)^4337*50000000000000^3313 ≤ 21486196480597^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245614721 10000000000 21486196480597 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049153197/5000000000 : ℝ)^4337 ≤ (6474980621993/50000000000000 : ℝ)^3313 := by
    have hnat : (1049153197 : ℕ)^4337*50000000000000^3313 ≤ 6474980621993^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049153197 5000000000 6474980621993 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674183757/5000000000 : ℝ), (5245614721/10000000000 : ℝ), (-1049153197/5000000000 : ℝ)] ![(11019411444607/25000000000000 : ℝ), (21486196480597/50000000000000 : ℝ), (6474980621993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674183757/5000000000 : ℝ)|^4337 ≤ (11019411444607/25000000000000 : ℝ)^3313
        have hw : |(2674183757/5000000000 : ℝ)|=(2674183757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245614721/10000000000 : ℝ)|^4337 ≤ (21486196480597/50000000000000 : ℝ)^3313
        have hw : |(5245614721/10000000000 : ℝ)|=(5245614721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1049153197/5000000000 : ℝ)|^4337 ≤ (6474980621993/50000000000000 : ℝ)^3313
        have hw : |(-1049153197/5000000000 : ℝ)|=(1049153197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s6_3 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (863509879/2000000000 : ℝ)*x 0 + (2072718359/5000000000 : ℝ)*x 1 + (4496218257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863509879/2000000000 : ℝ)^4337 ≤ (33303853439729/100000000000000 : ℝ)^3313 := by
    have hnat : (863509879 : ℕ)^4337*100000000000000^3313 ≤ 33303853439729^3313*2000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863509879 2000000000 33303853439729 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2072718359/5000000000 : ℝ)^4337 ≤ (15788353664047/50000000000000 : ℝ)^3313 := by
    have hnat : (2072718359 : ℕ)^4337*50000000000000^3313 ≤ 15788353664047^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072718359 5000000000 15788353664047 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4496218257/10000000000 : ℝ)^4337 ≤ (8779859803439/25000000000000 : ℝ)^3313 := by
    have hnat : (4496218257 : ℕ)^4337*25000000000000^3313 ≤ 8779859803439^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496218257 10000000000 8779859803439 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863509879/2000000000 : ℝ), (2072718359/5000000000 : ℝ), (4496218257/10000000000 : ℝ)] ![(33303853439729/100000000000000 : ℝ), (15788353664047/50000000000000 : ℝ), (8779859803439/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863509879/2000000000 : ℝ)|^4337 ≤ (33303853439729/100000000000000 : ℝ)^3313
        have hw : |(863509879/2000000000 : ℝ)|=(863509879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2072718359/5000000000 : ℝ)|^4337 ≤ (15788353664047/50000000000000 : ℝ)^3313
        have hw : |(2072718359/5000000000 : ℝ)|=(2072718359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4496218257/10000000000 : ℝ)|^4337 ≤ (8779859803439/25000000000000 : ℝ)^3313
        have hw : |(4496218257/10000000000 : ℝ)|=(4496218257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s6_4 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2014127649/10000000000 : ℝ)*x 0 + (5246208261/10000000000 : ℝ)*x 1 + (5410310787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014127649/10000000000 : ℝ)^4337 ≤ (12274121725309/100000000000000 : ℝ)^3313 := by
    have hnat : (2014127649 : ℕ)^4337*100000000000000^3313 ≤ 12274121725309^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014127649 10000000000 12274121725309 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246208261/10000000000 : ℝ)^4337 ≤ (21489379129459/50000000000000 : ℝ)^3313 := by
    have hnat : (5246208261 : ℕ)^4337*50000000000000^3313 ≤ 21489379129459^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246208261 10000000000 21489379129459 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410310787/10000000000 : ℝ)^4337 ≤ (44747120001249/100000000000000 : ℝ)^3313 := by
    have hnat : (5410310787 : ℕ)^4337*100000000000000^3313 ≤ 44747120001249^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410310787 10000000000 44747120001249 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2014127649/10000000000 : ℝ), (5246208261/10000000000 : ℝ), (5410310787/10000000000 : ℝ)] ![(12274121725309/100000000000000 : ℝ), (21489379129459/50000000000000 : ℝ), (44747120001249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2014127649/10000000000 : ℝ)|^4337 ≤ (12274121725309/100000000000000 : ℝ)^3313
        have hw : |(-2014127649/10000000000 : ℝ)|=(2014127649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246208261/10000000000 : ℝ)|^4337 ≤ (21489379129459/50000000000000 : ℝ)^3313
        have hw : |(5246208261/10000000000 : ℝ)|=(5246208261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410310787/10000000000 : ℝ)|^4337 ≤ (44747120001249/100000000000000 : ℝ)^3313
        have hw : |(5410310787/10000000000 : ℝ)|=(5410310787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s6_5 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305625413/10000000000 : ℝ)*x 0 + (-3867221/20000000 : ℝ)*x 1 + (5410310441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305625413/10000000000 : ℝ)^4337 ≤ (10904272216817/25000000000000 : ℝ)^3313 := by
    have hnat : (5305625413 : ℕ)^4337*25000000000000^3313 ≤ 10904272216817^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305625413 10000000000 10904272216817 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3867221/20000000 : ℝ)^4337 ≤ (11635794868037/100000000000000 : ℝ)^3313 := by
    have hnat : (3867221 : ℕ)^4337*100000000000000^3313 ≤ 11635794868037^3313*20000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3867221 20000000 11635794868037 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410310441/10000000000 : ℝ)^4337 ≤ (11186779063771/25000000000000 : ℝ)^3313 := by
    have hnat : (5410310441 : ℕ)^4337*25000000000000^3313 ≤ 11186779063771^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410310441 10000000000 11186779063771 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305625413/10000000000 : ℝ), (-3867221/20000000 : ℝ), (5410310441/10000000000 : ℝ)] ![(10904272216817/25000000000000 : ℝ), (11635794868037/100000000000000 : ℝ), (11186779063771/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305625413/10000000000 : ℝ)|^4337 ≤ (10904272216817/25000000000000 : ℝ)^3313
        have hw : |(5305625413/10000000000 : ℝ)|=(5305625413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3867221/20000000 : ℝ)|^4337 ≤ (11635794868037/100000000000000 : ℝ)^3313
        have hw : |(-3867221/20000000 : ℝ)|=(3867221/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410310441/10000000000 : ℝ)|^4337 ≤ (11186779063771/25000000000000 : ℝ)^3313
        have hw : |(5410310441/10000000000 : ℝ)|=(5410310441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s6_6 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305625449/10000000000 : ℝ)*x 0 + (1352577617/2500000000 : ℝ)*x 1 + (-1933610413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305625449/10000000000 : ℝ)^4337 ≤ (8723417850939/20000000000000 : ℝ)^3313 := by
    have hnat : (5305625449 : ℕ)^4337*20000000000000^3313 ≤ 8723417850939^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305625449 10000000000 8723417850939 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352577617/2500000000 : ℝ)^4337 ≤ (8949423309483/20000000000000 : ℝ)^3313 := by
    have hnat : (1352577617 : ℕ)^4337*20000000000000^3313 ≤ 8949423309483^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352577617 2500000000 8949423309483 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1933610413/10000000000 : ℝ)^4337 ≤ (2908948545671/25000000000000 : ℝ)^3313 := by
    have hnat : (1933610413 : ℕ)^4337*25000000000000^3313 ≤ 2908948545671^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933610413 10000000000 2908948545671 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305625449/10000000000 : ℝ), (1352577617/2500000000 : ℝ), (-1933610413/10000000000 : ℝ)] ![(8723417850939/20000000000000 : ℝ), (8949423309483/20000000000000 : ℝ), (2908948545671/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305625449/10000000000 : ℝ)|^4337 ≤ (8723417850939/20000000000000 : ℝ)^3313
        have hw : |(5305625449/10000000000 : ℝ)|=(5305625449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352577617/2500000000 : ℝ)|^4337 ≤ (8949423309483/20000000000000 : ℝ)^3313
        have hw : |(1352577617/2500000000 : ℝ)|=(1352577617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1933610413/10000000000 : ℝ)|^4337 ≤ (2908948545671/25000000000000 : ℝ)^3313
        have hw : |(-1933610413/10000000000 : ℝ)|=(1933610413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s6_7 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4317574307/10000000000 : ℝ)*x 0 + (2247479473/5000000000 : ℝ)*x 1 + (4146702703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317574307/10000000000 : ℝ)^4337 ≤ (4163013124427/12500000000000 : ℝ)^3313 := by
    have hnat : (4317574307 : ℕ)^4337*12500000000000^3313 ≤ 4163013124427^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317574307 10000000000 4163013124427 12500000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247479473/5000000000 : ℝ)^4337 ≤ (109708009913/312500000000 : ℝ)^3313 := by
    have hnat : (2247479473 : ℕ)^4337*312500000000^3313 ≤ 109708009913^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247479473 5000000000 109708009913 312500000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4146702703/10000000000 : ℝ)^4337 ≤ (31589331810847/100000000000000 : ℝ)^3313 := by
    have hnat : (4146702703 : ℕ)^4337*100000000000000^3313 ≤ 31589331810847^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146702703 10000000000 31589331810847 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317574307/10000000000 : ℝ), (2247479473/5000000000 : ℝ), (4146702703/10000000000 : ℝ)] ![(4163013124427/12500000000000 : ℝ), (109708009913/312500000000 : ℝ), (31589331810847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317574307/10000000000 : ℝ)|^4337 ≤ (4163013124427/12500000000000 : ℝ)^3313
        have hw : |(4317574307/10000000000 : ℝ)|=(4317574307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247479473/5000000000 : ℝ)|^4337 ≤ (109708009913/312500000000 : ℝ)^3313
        have hw : |(2247479473/5000000000 : ℝ)|=(2247479473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4146702703/10000000000 : ℝ)|^4337 ≤ (31589331810847/100000000000000 : ℝ)^3313
        have hw : |(4146702703/10000000000 : ℝ)|=(4146702703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1377_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11229/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14729/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7367/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7367/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7367/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7367/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7367/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7367/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11223/100000 : ℝ) ^ (271/64 : ℝ) ≤ (190035674001321/2000000000000000000 : ℝ) := by
    have hpowers : (11223/100000 : ℝ)^271 ≤ (190035674001321/2000000000000000000 : ℝ)^64 := by
      have hnat : (11223 : ℕ)^271*2000000000000000000^64 ≤ 190035674001321^64*100000^271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11223 100000 190035674001321 2000000000000000000 271 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11223/100000 : ℝ)) (X := (190035674001321/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hpowhi : (7367/50000 : ℝ) ^ (271/64 : ℝ) ≤ (30085540490774943/100000000000000000000 : ℝ) := by
    have hpowers : (7367/50000 : ℝ)^271 ≤ (30085540490774943/100000000000000000000 : ℝ)^64 := by
      have hnat : (7367 : ℕ)^271*100000000000000000000^64 ≤ 30085540490774943^64*50000^271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7367 50000 30085540490774943 100000000000000000000 271 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7367/50000 : ℝ)) (X := (30085540490774943/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000190035674001321/1000000000000000000 : ℝ) ≤ (10000448760166719/10000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (1000190035674001321/1000000000000000000 : ℝ)^64 ≤ (10000448760166719/10000000000000000 : ℝ)^271 := by
      have hnat : (1000190035674001321 : ℕ)^64*10000000000000000^271 ≤ 10000448760166719^271*1000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000190035674001321 1000000000000000000 10000448760166719 10000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000448760166719/10000000000000000 : ℝ)) (X := (1000190035674001321/1000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039587324190840993/100000000000000000000 : ℝ) ≤ (2500233690570149/2500000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (100039587324190840993/100000000000000000000 : ℝ)^64 ≤ (2500233690570149/2500000000000000 : ℝ)^271 := by
      have hnat : (100039587324190840993 : ℕ)^64*2500000000000000^271 ≤ 2500233690570149^271*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039587324190840993 100000000000000000000 2500233690570149 2500000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500233690570149/2500000000000000 : ℝ)) (X := (100039587324190840993/100000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030085540490774943/50000000000000000000 : ℝ) ≤ (10001420764394473/10000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (50030085540490774943/50000000000000000000 : ℝ)^64 ≤ (10001420764394473/10000000000000000 : ℝ)^271 := by
      have hnat : (50030085540490774943 : ℕ)^64*10000000000000000^271 ≤ 10001420764394473^271*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030085540490774943 50000000000000000000 10001420764394473 10000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001420764394473/10000000000000000 : ℝ)) (X := (50030085540490774943/50000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(190035674001321/2000000000000000000 : ℝ) ≤ ((35100666793497267267/35110000000000000000 : ℝ)+2*(486002113877/351100000000000 : ℝ)*(11223/100000 : ℝ))^(271/64 : ℝ) := by
    rw [show (35100666793497267267/35110000000000000000 : ℝ)+2*(486002113877/351100000000000 : ℝ)*(11223/100000 : ℝ)=(10000448760166719/10000000000000000 : ℝ) by norm_num, show 1+2*(190035674001321/2000000000000000000 : ℝ)=(1000190035674001321/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30085540490774943/100000000000000000000 : ℝ)+(190035674001321/2000000000000000000 : ℝ) ≤ ((35100666793497267267/35110000000000000000 : ℝ)+(486002113877/351100000000000 : ℝ)*((7367/50000 : ℝ)+(11223/100000 : ℝ)))^(271/64 : ℝ) := by
    rw [show (35100666793497267267/35110000000000000000 : ℝ)+(486002113877/351100000000000 : ℝ)*((7367/50000 : ℝ)+(11223/100000 : ℝ))=(2500233690570149/2500000000000000 : ℝ) by norm_num, show 1+(30085540490774943/100000000000000000000 : ℝ)+(190035674001321/2000000000000000000 : ℝ)=(100039587324190840993/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30085540490774943/100000000000000000000 : ℝ) ≤ ((35100666793497267267/35110000000000000000 : ℝ)+2*(486002113877/351100000000000 : ℝ)*(7367/50000 : ℝ))^(271/64 : ℝ) := by
    rw [show (35100666793497267267/35110000000000000000 : ℝ)+2*(486002113877/351100000000000 : ℝ)*(7367/50000 : ℝ)=(10001420764394473/10000000000000000 : ℝ) by norm_num, show 1+2*(30085540490774943/100000000000000000000 : ℝ)=(50030085540490774943/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35100666793497267267/35110000000000000000 : ℝ)*(X 1 0+X 2 0)+(486002113877/351100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (7367/50000 : ℝ)) (c := (35100666793497267267/35110000000000000000 : ℝ)) (alpha := (486002113877/351100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35100666793497267267/35110000000000000000 : ℝ)*(X 0 1+X 2 1)+(486002113877/351100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (7367/50000 : ℝ)) (c := (35100666793497267267/35110000000000000000 : ℝ)) (alpha := (486002113877/351100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35100666793497267267/35110000000000000000 : ℝ)*(X 0 2+X 1 2)+(486002113877/351100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (7367/50000 : ℝ)) (c := (35100666793497267267/35110000000000000000 : ℝ)) (alpha := (486002113877/351100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2014115537/10000000000 : ℝ)*X 0 0+(5410907671/10000000000 : ℝ)*X 0 1+(5245614657/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348367401/10000000000 : ℝ)*X 1 0+(-524576553/2500000000 : ℝ)*X 1 1+(1311403743/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674183757/5000000000 : ℝ)*X 2 0+(5245614721/10000000000 : ℝ)*X 2 1+(-1049153197/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((863509879/2000000000 : ℝ)*X 0 0+(2072718359/5000000000 : ℝ)*X 0 1+(4496218257/10000000000 : ℝ)*X 0 2+(863509879/2000000000 : ℝ)*X 1 0+(2072718359/5000000000 : ℝ)*X 1 1+(4496218257/10000000000 : ℝ)*X 1 2+(863509879/2000000000 : ℝ)*X 2 0+(2072718359/5000000000 : ℝ)*X 2 1+(4496218257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2014127649/10000000000 : ℝ)*X 0 0+(5246208261/10000000000 : ℝ)*X 0 1+(5410310787/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305625413/10000000000 : ℝ)*X 1 0+(-3867221/20000000 : ℝ)*X 1 1+(5410310441/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305625449/10000000000 : ℝ)*X 2 0+(1352577617/2500000000 : ℝ)*X 2 1+(-1933610413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4317574307/10000000000 : ℝ)*X 0 0+(2247479473/5000000000 : ℝ)*X 0 1+(4146702703/10000000000 : ℝ)*X 0 2+(4317574307/10000000000 : ℝ)*X 1 0+(2247479473/5000000000 : ℝ)*X 1 1+(4146702703/10000000000 : ℝ)*X 1 2+(4317574307/10000000000 : ℝ)*X 2 0+(2247479473/5000000000 : ℝ)*X 2 1+(4146702703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56557831812262392138908787/17555000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (249212527/25000000000000 : ℝ)*(base19) + (591017473/50000000000000 : ℝ)*(base23) + (115747389/100000000000000 : ℝ)*(upper3) + (8980403/25000000000000 : ℝ)*(lower4) + (44503668277813/1000000000000 : ℝ)*(major0) + (44503668277813/1000000000000 : ℝ)*(major1) + (44503668277813/1000000000000 : ℝ)*(major2) + (3024949951184489/50000000000000 : ℝ)*(sp0) + (3024966112726793/50000000000000 : ℝ)*(sp1) + (6049930813798433/100000000000000 : ℝ)*(sp2) + (2850787776266717/100000000000000 : ℝ)*(sp3) + (6663986943/20000000000000 : ℝ)*(sp4) + (245294063/20000000000000 : ℝ)*(sp6) + (12549600497/100000000000000 : ℝ)*(sp7) + (1425400162933607/50000000000000 : ℝ)*(f.failure) + (3024966611151847/50000000000000 : ℝ)*(f.sum) + (1908216938217/3511000000000000000000000000 : ℝ)*base65 + (128138246632037071/35110000000000000000000000000000 : ℝ)*base67 + (12252246422137071/35110000000000000000000000000000 : ℝ)*base69 + (100698203121547071/35110000000000000000000000000000 : ℝ)*base71 + (1328709384519/877750000000000000000000000 : ℝ)*base74 + (321064831430372929/35110000000000000000000000000000 : ℝ)*base76 + (457810681484662929/35110000000000000000000000000000 : ℝ)*base78 + (55777282368437071/35110000000000000000000000000000 : ℝ)*base79 + (20179972174927/3511000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2708511/625000000000000000000 : ℝ)*base89 + (2708511/625000000000000000000 : ℝ)*base91 + (2708511/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (297316413173028808797064131/43887500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2409787909/100000000000000 : ℝ)*(base19) + (2835944407/100000000000000 : ℝ)*(base23) + (167513797/100000000000000 : ℝ)*(upper2) + (173302861/100000000000000 : ℝ)*(upper3) + (220599763/100000000000000 : ℝ)*(upper5) + (112064969569169/2500000000000 : ℝ)*(major0) + (112064969569169/2500000000000 : ℝ)*(major1) + (112064969569169/2500000000000 : ℝ)*(major2) + (21915333673/50000000000000 : ℝ)*(sp1) + (26202802139/50000000000000 : ℝ)*(sp2) + (1218749996303739/20000000000000 : ℝ)*(sp4) + (76171296763293/1250000000000 : ℝ)*(sp5) + (609369473997001/10000000000000 : ℝ)*(sp6) + (358930919774717/12500000000000 : ℝ)*(sp7) + (358930919774717/12500000000000 : ℝ)*(f.failure) + (1218749996303739/20000000000000 : ℝ)*(f.sum) + (1576580053663/3511000000000000000000000000 : ℝ)*base66 + (705778578640866123/87775000000000000000000000000000 : ℝ)*base67 + (225802257092316123/87775000000000000000000000000000 : ℝ)*base69 + (170169229292441123/87775000000000000000000000000000 : ℝ)*base71 + (211430568747/43887500000000000000000000 : ℝ)*base73 + (1401652098173391123/87775000000000000000000000000000 : ℝ)*base75 + (551044671609458877/87775000000000000000000000000000 : ℝ)*base78 + (316931985095458877/87775000000000000000000000000000 : ℝ)*base80 + (5697331257249/1755500000000000000000000000 : ℝ)*base81 + (1294459/156250000000000000000 : ℝ)*base90 + (1294459/156250000000000000000 : ℝ)*base92 + (1294459/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1377_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11229/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1377_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1377_s7_0 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-503529267/2500000000 : ℝ)*x 0 + (1352716421/2500000000 : ℝ)*x 1 + (5245655909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (503529267/2500000000 : ℝ)^4337 ≤ (6137018657277/50000000000000 : ℝ)^3313 := by
    have hnat : (503529267 : ℕ)^4337*50000000000000^3313 ≤ 6137018657277^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503529267 2500000000 6137018657277 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352716421/2500000000 : ℝ)^4337 ≤ (44753128003989/100000000000000 : ℝ)^3313 := by
    have hnat : (1352716421 : ℕ)^4337*100000000000000^3313 ≤ 44753128003989^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352716421 2500000000 44753128003989 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245655909/10000000000 : ℝ)^4337 ≤ (21486417333123/50000000000000 : ℝ)^3313 := by
    have hnat : (5245655909 : ℕ)^4337*50000000000000^3313 ≤ 21486417333123^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245655909 10000000000 21486417333123 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-503529267/2500000000 : ℝ), (1352716421/2500000000 : ℝ), (5245655909/10000000000 : ℝ)] ![(6137018657277/50000000000000 : ℝ), (44753128003989/100000000000000 : ℝ), (21486417333123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-503529267/2500000000 : ℝ)|^4337 ≤ (6137018657277/50000000000000 : ℝ)^3313
        have hw : |(-503529267/2500000000 : ℝ)|=(503529267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352716421/2500000000 : ℝ)|^4337 ≤ (44753128003989/100000000000000 : ℝ)^3313
        have hw : |(1352716421/2500000000 : ℝ)|=(1352716421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245655909/10000000000 : ℝ)|^4337 ≤ (21486417333123/50000000000000 : ℝ)^3313
        have hw : |(5245655909/10000000000 : ℝ)|=(5245655909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s7_1 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069671441/2000000000 : ℝ)*x 0 + (-524566391/2500000000 : ℝ)*x 1 + (5245655853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069671441/2000000000 : ℝ)^4337 ≤ (11019383639693/25000000000000 : ℝ)^3313 := by
    have hnat : (1069671441 : ℕ)^4337*25000000000000^3313 ≤ 11019383639693^3313*2000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069671441 2000000000 11019383639693 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524566391/2500000000 : ℝ)^4337 ≤ (809351960741/6250000000000 : ℝ)^3313 := by
    have hnat : (524566391 : ℕ)^4337*6250000000000^3313 ≤ 809351960741^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524566391 2500000000 809351960741 6250000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245655853/10000000000 : ℝ)^4337 ≤ (8594566813139/20000000000000 : ℝ)^3313 := by
    have hnat : (5245655853 : ℕ)^4337*20000000000000^3313 ≤ 8594566813139^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245655853 10000000000 8594566813139 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069671441/2000000000 : ℝ), (-524566391/2500000000 : ℝ), (5245655853/10000000000 : ℝ)] ![(11019383639693/25000000000000 : ℝ), (809351960741/6250000000000 : ℝ), (8594566813139/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069671441/2000000000 : ℝ)|^4337 ≤ (11019383639693/25000000000000 : ℝ)^3313
        have hw : |(1069671441/2000000000 : ℝ)|=(1069671441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-524566391/2500000000 : ℝ)|^4337 ≤ (809351960741/6250000000000 : ℝ)^3313
        have hw : |(-524566391/2500000000 : ℝ)|=(524566391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245655853/10000000000 : ℝ)|^4337 ≤ (8594566813139/20000000000000 : ℝ)^3313
        have hw : |(5245655853/10000000000 : ℝ)|=(5245655853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s7_2 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348357643/10000000000 : ℝ)*x 0 + (8393049/16000000 : ℝ)*x 1 + (-2098265281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348357643/10000000000 : ℝ)^4337 ≤ (44077539284177/100000000000000 : ℝ)^3313 := by
    have hnat : (5348357643 : ℕ)^4337*100000000000000^3313 ≤ 44077539284177^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348357643 10000000000 44077539284177 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8393049/16000000 : ℝ)^4337 ≤ (2685801976287/6250000000000 : ℝ)^3313 := by
    have hnat : (8393049 : ℕ)^4337*6250000000000^3313 ≤ 2685801976287^3313*16000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8393049 16000000 2685801976287 6250000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2098265281/10000000000 : ℝ)^4337 ≤ (647481454273/5000000000000 : ℝ)^3313 := by
    have hnat : (2098265281 : ℕ)^4337*5000000000000^3313 ≤ 647481454273^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098265281 10000000000 647481454273 5000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348357643/10000000000 : ℝ), (8393049/16000000 : ℝ), (-2098265281/10000000000 : ℝ)] ![(44077539284177/100000000000000 : ℝ), (2685801976287/6250000000000 : ℝ), (647481454273/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348357643/10000000000 : ℝ)|^4337 ≤ (44077539284177/100000000000000 : ℝ)^3313
        have hw : |(5348357643/10000000000 : ℝ)|=(5348357643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8393049/16000000 : ℝ)|^4337 ≤ (2685801976287/6250000000000 : ℝ)^3313
        have hw : |(8393049/16000000 : ℝ)|=(8393049/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2098265281/10000000000 : ℝ)|^4337 ≤ (647481454273/5000000000000 : ℝ)^3313
        have hw : |(-2098265281/10000000000 : ℝ)|=(2098265281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s7_3 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2158776127/5000000000 : ℝ)*x 0 + (4145524221/10000000000 : ℝ)*x 1 + (44961301/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158776127/5000000000 : ℝ)^4337 ≤ (6660776461847/20000000000000 : ℝ)^3313 := by
    have hnat : (2158776127 : ℕ)^4337*20000000000000^3313 ≤ 6660776461847^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158776127 5000000000 6660776461847 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4145524221/10000000000 : ℝ)^4337 ≤ (31577579875231/100000000000000 : ℝ)^3313 := by
    have hnat : (4145524221 : ℕ)^4337*100000000000000^3313 ≤ 31577579875231^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145524221 10000000000 31577579875231 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44961301/100000000 : ℝ)^4337 ≤ (35118537801081/100000000000000 : ℝ)^3313 := by
    have hnat : (44961301 : ℕ)^4337*100000000000000^3313 ≤ 35118537801081^3313*100000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44961301 100000000 35118537801081 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158776127/5000000000 : ℝ), (4145524221/10000000000 : ℝ), (44961301/100000000 : ℝ)] ![(6660776461847/20000000000000 : ℝ), (31577579875231/100000000000000 : ℝ), (35118537801081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158776127/5000000000 : ℝ)|^4337 ≤ (6660776461847/20000000000000 : ℝ)^3313
        have hw : |(2158776127/5000000000 : ℝ)|=(2158776127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4145524221/10000000000 : ℝ)|^4337 ≤ (31577579875231/100000000000000 : ℝ)^3313
        have hw : |(4145524221/10000000000 : ℝ)|=(4145524221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(44961301/100000000 : ℝ)|^4337 ≤ (35118537801081/100000000000000 : ℝ)^3313
        have hw : |(44961301/100000000 : ℝ)|=(44961301/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s7_4 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-402825739/2000000000 : ℝ)*x 0 + (5246249181/10000000000 : ℝ)*x 1 + (1352567371/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (402825739/2000000000 : ℝ)^4337 ≤ (12274130069863/100000000000000 : ℝ)^3313 := by
    have hnat : (402825739 : ℕ)^4337*100000000000000^3313 ≤ 12274130069863^3313*2000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402825739 2000000000 12274130069863 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246249181/10000000000 : ℝ)^4337 ≤ (42979197105249/100000000000000 : ℝ)^3313 := by
    have hnat : (5246249181 : ℕ)^4337*100000000000000^3313 ≤ 42979197105249^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246249181 10000000000 42979197105249 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352567371/2500000000 : ℝ)^4337 ≤ (4474667281139/10000000000000 : ℝ)^3313 := by
    have hnat : (1352567371 : ℕ)^4337*10000000000000^3313 ≤ 4474667281139^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352567371 2500000000 4474667281139 10000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-402825739/2000000000 : ℝ), (5246249181/10000000000 : ℝ), (1352567371/2500000000 : ℝ)] ![(12274130069863/100000000000000 : ℝ), (42979197105249/100000000000000 : ℝ), (4474667281139/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-402825739/2000000000 : ℝ)|^4337 ≤ (12274130069863/100000000000000 : ℝ)^3313
        have hw : |(-402825739/2000000000 : ℝ)|=(402825739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246249181/10000000000 : ℝ)|^4337 ≤ (42979197105249/100000000000000 : ℝ)^3313
        have hw : |(5246249181/10000000000 : ℝ)|=(5246249181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352567371/2500000000 : ℝ)|^4337 ≤ (4474667281139/10000000000000 : ℝ)^3313
        have hw : |(1352567371/2500000000 : ℝ)|=(1352567371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s7_5 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663204609/1250000000 : ℝ)*x 0 + (-1933651107/10000000000 : ℝ)*x 1 + (1082053901/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663204609/1250000000 : ℝ)^4337 ≤ (43617212187673/100000000000000 : ℝ)^3313 := by
    have hnat : (663204609 : ℕ)^4337*100000000000000^3313 ≤ 43617212187673^3313*1250000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663204609 1250000000 43617212187673 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1933651107/10000000000 : ℝ)^4337 ≤ (2327222951121/20000000000000 : ℝ)^3313 := by
    have hnat : (1933651107 : ℕ)^4337*20000000000000^3313 ≤ 2327222951121^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933651107 10000000000 2327222951121 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082053901/2000000000 : ℝ)^4337 ≤ (22373336519379/50000000000000 : ℝ)^3313 := by
    have hnat : (1082053901 : ℕ)^4337*50000000000000^3313 ≤ 22373336519379^3313*2000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082053901 2000000000 22373336519379 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663204609/1250000000 : ℝ), (-1933651107/10000000000 : ℝ), (1082053901/2000000000 : ℝ)] ![(43617212187673/100000000000000 : ℝ), (2327222951121/20000000000000 : ℝ), (22373336519379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663204609/1250000000 : ℝ)|^4337 ≤ (43617212187673/100000000000000 : ℝ)^3313
        have hw : |(663204609/1250000000 : ℝ)|=(663204609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1933651107/10000000000 : ℝ)|^4337 ≤ (2327222951121/20000000000000 : ℝ)^3313
        have hw : |(-1933651107/10000000000 : ℝ)|=(1933651107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082053901/2000000000 : ℝ)|^4337 ≤ (22373336519379/50000000000000 : ℝ)^3313
        have hw : |(1082053901/2000000000 : ℝ)|=(1082053901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s7_6 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326409171/2500000000 : ℝ)*x 0 + (2705134927/5000000000 : ℝ)*x 1 + (-966825443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326409171/2500000000 : ℝ)^4337 ≤ (21808605082219/50000000000000 : ℝ)^3313 := by
    have hnat : (1326409171 : ℕ)^4337*50000000000000^3313 ≤ 21808605082219^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326409171 2500000000 21808605082219 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705134927/5000000000 : ℝ)^4337 ≤ (11186669204349/25000000000000 : ℝ)^3313 := by
    have hnat : (2705134927 : ℕ)^4337*25000000000000^3313 ≤ 11186669204349^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705134927 5000000000 11186669204349 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (966825443/5000000000 : ℝ)^4337 ≤ (11636113014639/100000000000000 : ℝ)^3313 := by
    have hnat : (966825443 : ℕ)^4337*100000000000000^3313 ≤ 11636113014639^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966825443 5000000000 11636113014639 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326409171/2500000000 : ℝ), (2705134927/5000000000 : ℝ), (-966825443/5000000000 : ℝ)] ![(21808605082219/50000000000000 : ℝ), (11186669204349/25000000000000 : ℝ), (11636113014639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326409171/2500000000 : ℝ)|^4337 ≤ (21808605082219/50000000000000 : ℝ)^3313
        have hw : |(1326409171/2500000000 : ℝ)|=(1326409171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705134927/5000000000 : ℝ)|^4337 ≤ (11186669204349/25000000000000 : ℝ)^3313
        have hw : |(2705134927/5000000000 : ℝ)|=(2705134927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-966825443/5000000000 : ℝ)|^4337 ≤ (11636113014639/100000000000000 : ℝ)^3313
        have hw : |(-966825443/5000000000 : ℝ)|=(966825443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s7_7 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2158788699/5000000000 : ℝ)*x 0 + (4494871789/10000000000 : ℝ)*x 1 + (414678893/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158788699/5000000000 : ℝ)^4337 ≤ (1665206810383/5000000000000 : ℝ)^3313 := by
    have hnat : (2158788699 : ℕ)^4337*5000000000000^3313 ≤ 1665206810383^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158788699 5000000000 1665206810383 5000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4494871789/10000000000 : ℝ)^4337 ≤ (7021134412339/20000000000000 : ℝ)^3313 := by
    have hnat : (4494871789 : ℕ)^4337*20000000000000^3313 ≤ 7021134412339^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494871789 10000000000 7021134412339 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414678893/1000000000 : ℝ)^4337 ≤ (315901917153/1000000000000 : ℝ)^3313 := by
    have hnat : (414678893 : ℕ)^4337*1000000000000^3313 ≤ 315901917153^3313*1000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414678893 1000000000 315901917153 1000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158788699/5000000000 : ℝ), (4494871789/10000000000 : ℝ), (414678893/1000000000 : ℝ)] ![(1665206810383/5000000000000 : ℝ), (7021134412339/20000000000000 : ℝ), (315901917153/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158788699/5000000000 : ℝ)|^4337 ≤ (1665206810383/5000000000000 : ℝ)^3313
        have hw : |(2158788699/5000000000 : ℝ)|=(2158788699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4494871789/10000000000 : ℝ)|^4337 ≤ (7021134412339/20000000000000 : ℝ)^3313
        have hw : |(4494871789/10000000000 : ℝ)|=(4494871789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(414678893/1000000000 : ℝ)|^4337 ≤ (315901917153/1000000000000 : ℝ)^3313
        have hw : |(414678893/1000000000 : ℝ)|=(414678893/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1377_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11229/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1123/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1841/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14729/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11229/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14729/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11229/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14729/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11229/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14729/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11229/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14729/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11229/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14729/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11229/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11229/100000 : ℝ) ^ (271/64 : ℝ) ≤ (4761656061371573/50000000000000000000 : ℝ) := by
    have hpowers : (11229/100000 : ℝ)^271 ≤ (4761656061371573/50000000000000000000 : ℝ)^64 := by
      have hnat : (11229 : ℕ)^271*50000000000000000000^64 ≤ 4761656061371573^64*100000^271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11229 100000 4761656061371573 50000000000000000000 271 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11229/100000 : ℝ)) (X := (4761656061371573/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14729/100000 : ℝ) ^ (271/64 : ℝ) ≤ (6008466618220197/20000000000000000000 : ℝ) := by
    have hpowers : (14729/100000 : ℝ)^271 ≤ (6008466618220197/20000000000000000000 : ℝ)^64 := by
      have hnat : (14729 : ℕ)^271*20000000000000000000^64 ≤ 6008466618220197^64*100000^271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14729 100000 6008466618220197 20000000000000000000 271 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14729/100000 : ℝ)) (X := (6008466618220197/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004761656061371573/25000000000000000000 : ℝ) ≤ (2500112444214901/2500000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (25004761656061371573/25000000000000000000 : ℝ)^64 ≤ (2500112444214901/2500000000000000 : ℝ)^271 := by
      have hnat : (25004761656061371573 : ℕ)^64*2500000000000000^271 ≤ 2500112444214901^271*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004761656061371573 25000000000000000000 2500112444214901 2500000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500112444214901/2500000000000000 : ℝ)) (X := (25004761656061371573/25000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039565645213844131/100000000000000000000 : ℝ) ≤ (10000934250459471/10000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (100039565645213844131/100000000000000000000 : ℝ)^64 ≤ (10000934250459471/10000000000000000 : ℝ)^271 := by
      have hnat : (100039565645213844131 : ℕ)^64*10000000000000000^271 ≤ 10000934250459471^271*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039565645213844131 100000000000000000000 10000934250459471 10000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000934250459471/10000000000000000 : ℝ)) (X := (100039565645213844131/100000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006008466618220197/10000000000000000000 : ℝ) ≤ (5000709362029669/5000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (10006008466618220197/10000000000000000000 : ℝ)^64 ≤ (5000709362029669/5000000000000000 : ℝ)^271 := by
      have hnat : (10006008466618220197 : ℕ)^64*5000000000000000^271 ≤ 5000709362029669^271*10000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006008466618220197 10000000000000000000 5000709362029669 5000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000709362029669/5000000000000000 : ℝ)) (X := (10006008466618220197/10000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4761656061371573/50000000000000000000 : ℝ) ≤ ((17495346955451400457/17500000000000000000 : ℝ)+2*(484473599867/350000000000000 : ℝ)*(11229/100000 : ℝ))^(271/64 : ℝ) := by
    rw [show (17495346955451400457/17500000000000000000 : ℝ)+2*(484473599867/350000000000000 : ℝ)*(11229/100000 : ℝ)=(2500112444214901/2500000000000000 : ℝ) by norm_num, show 1+2*(4761656061371573/50000000000000000000 : ℝ)=(25004761656061371573/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6008466618220197/20000000000000000000 : ℝ)+(4761656061371573/50000000000000000000 : ℝ) ≤ ((17495346955451400457/17500000000000000000 : ℝ)+(484473599867/350000000000000 : ℝ)*((14729/100000 : ℝ)+(11229/100000 : ℝ)))^(271/64 : ℝ) := by
    rw [show (17495346955451400457/17500000000000000000 : ℝ)+(484473599867/350000000000000 : ℝ)*((14729/100000 : ℝ)+(11229/100000 : ℝ))=(10000934250459471/10000000000000000 : ℝ) by norm_num, show 1+(6008466618220197/20000000000000000000 : ℝ)+(4761656061371573/50000000000000000000 : ℝ)=(100039565645213844131/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6008466618220197/20000000000000000000 : ℝ) ≤ ((17495346955451400457/17500000000000000000 : ℝ)+2*(484473599867/350000000000000 : ℝ)*(14729/100000 : ℝ))^(271/64 : ℝ) := by
    rw [show (17495346955451400457/17500000000000000000 : ℝ)+2*(484473599867/350000000000000 : ℝ)*(14729/100000 : ℝ)=(5000709362029669/5000000000000000 : ℝ) by norm_num, show 1+2*(6008466618220197/20000000000000000000 : ℝ)=(10006008466618220197/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17495346955451400457/17500000000000000000 : ℝ)*(X 1 0+X 2 0)+(484473599867/350000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (11229/100000 : ℝ)) (hi := (14729/100000 : ℝ)) (c := (17495346955451400457/17500000000000000000 : ℝ)) (alpha := (484473599867/350000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17495346955451400457/17500000000000000000 : ℝ)*(X 0 1+X 2 1)+(484473599867/350000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (11229/100000 : ℝ)) (hi := (14729/100000 : ℝ)) (c := (17495346955451400457/17500000000000000000 : ℝ)) (alpha := (484473599867/350000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17495346955451400457/17500000000000000000 : ℝ)*(X 0 2+X 1 2)+(484473599867/350000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (11229/100000 : ℝ)) (hi := (14729/100000 : ℝ)) (c := (17495346955451400457/17500000000000000000 : ℝ)) (alpha := (484473599867/350000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-503529267/2500000000 : ℝ)*X 0 0+(1352716421/2500000000 : ℝ)*X 0 1+(5245655909/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069671441/2000000000 : ℝ)*X 1 0+(-524566391/2500000000 : ℝ)*X 1 1+(5245655853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348357643/10000000000 : ℝ)*X 2 0+(8393049/16000000 : ℝ)*X 2 1+(-2098265281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2158776127/5000000000 : ℝ)*X 0 0+(4145524221/10000000000 : ℝ)*X 0 1+(44961301/100000000 : ℝ)*X 0 2+(2158776127/5000000000 : ℝ)*X 1 0+(4145524221/10000000000 : ℝ)*X 1 1+(44961301/100000000 : ℝ)*X 1 2+(2158776127/5000000000 : ℝ)*X 2 0+(4145524221/10000000000 : ℝ)*X 2 1+(44961301/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-402825739/2000000000 : ℝ)*X 0 0+(5246249181/10000000000 : ℝ)*X 0 1+(1352567371/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663204609/1250000000 : ℝ)*X 1 0+(-1933651107/10000000000 : ℝ)*X 1 1+(1082053901/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326409171/2500000000 : ℝ)*X 2 0+(2705134927/5000000000 : ℝ)*X 2 1+(-966825443/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2158788699/5000000000 : ℝ)*X 0 0+(4494871789/10000000000 : ℝ)*X 0 1+(414678893/1000000000 : ℝ)*X 0 2+(2158788699/5000000000 : ℝ)*X 1 0+(4494871789/10000000000 : ℝ)*X 1 1+(414678893/1000000000 : ℝ)*X 1 2+(2158788699/5000000000 : ℝ)*X 2 0+(4494871789/10000000000 : ℝ)*X 2 1+(414678893/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3513470802908639704873369599/875000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3021531/3125000000000 : ℝ)*(base19) + (507277433/100000000000000 : ℝ)*(base23) + (792101/1000000000000 : ℝ)*(lower2) + (74953421/100000000000000 : ℝ)*(upper5) + (4452563096325069/100000000000000 : ℝ)*(major0) + (4452563096325069/100000000000000 : ℝ)*(major1) + (4452563096325069/100000000000000 : ℝ)*(major2) + (1210582047091023/20000000000000 : ℝ)*(sp0) + (1513227718045031/25000000000000 : ℝ)*(sp1) + (242116733907273/4000000000000 : ℝ)*(sp2) + (7130513928413/250000000000 : ℝ)*(sp3) + (8619504143/100000000000000 : ℝ)*(sp4) + (3943045071/50000000000000 : ℝ)*(sp5) + (1632479169/100000000000000 : ℝ)*(sp7) + (2852207203844369/100000000000000 : ℝ)*(f.failure) + (3026459427479629/50000000000000 : ℝ)*(f.sum) + (39398327831677/17500000000000000000000000000 : ℝ)*base66 + (8404544672541693467/1750000000000000000000000000000000 : ℝ)*base68 + (2042442130291693467/1750000000000000000000000000000000 : ℝ)*base70 + (18818950811041693467/1750000000000000000000000000000000 : ℝ)*base72 + (722252526677/17500000000000000000000000000 : ℝ)*base74 + (8656902583458306533/1750000000000000000000000000000000 : ℝ)*base75 + (4794098034708306533/1750000000000000000000000000000000 : ℝ)*base77 + (5439843566041693467/1750000000000000000000000000000000 : ℝ)*base80 + (11267593628323/17500000000000000000000000000 : ℝ)*base81 + (2942663/1250000000000000000000 : ℝ)*base90 + (2942663/1250000000000000000000 : ℝ)*base92 + (2942663/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (935551798209187742103243741/125000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1631192221/100000000000000 : ℝ)*(base19) + (1017161823/50000000000000 : ℝ)*(base23) + (625549047/100000000000000 : ℝ)*(lower1) + (33981853/25000000000000 : ℝ)*(upper3) + (237711351/100000000000000 : ℝ)*(lower4) + (4484810669930703/100000000000000 : ℝ)*(major0) + (4484810669930703/100000000000000 : ℝ)*(major1) + (4484810669930703/100000000000000 : ℝ)*(major2) + (10626461993/50000000000000 : ℝ)*(sp2) + (381577167/25000000000000 : ℝ)*(sp3) + (6096756849285261/100000000000000 : ℝ)*(sp4) + (76209440226163/1250000000000 : ℝ)*(sp5) + (609673356203763/10000000000000 : ℝ)*(sp6) + (718215678696747/25000000000000 : ℝ)*(sp7) + (359108030136957/12500000000000 : ℝ)*(f.failure) + (6096756849285261/100000000000000 : ℝ)*(f.sum) + (11566020535857/2500000000000000000000000000 : ℝ)*base66 + (740357622795368753/250000000000000000000000000000000 : ℝ)*base67 + (1966086017954631247/250000000000000000000000000000000 : ℝ)*base70 + (704581220954631247/250000000000000000000000000000000 : ℝ)*base72 + (9118428983357/2500000000000000000000000000 : ℝ)*base74 + (2092546513045368753/250000000000000000000000000000000 : ℝ)*base75 + (11398675519545368753/250000000000000000000000000000000 : ℝ)*base77 + (164281115545368753/250000000000000000000000000000000 : ℝ)*base79 + (9780042768357/2500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (675561/156250000000000000000 : ℝ)*base89 + (675561/156250000000000000000 : ℝ)*base91 + (675561/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1377_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11229/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1377_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1377_box_0 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1849591193/10000000000 : ℝ)*x 0 + (1347117439/2500000000 : ℝ)*x 1 + (2694234911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1849591193/10000000000 : ℝ)^4337 ≤ (68615078631/625000000000 : ℝ)^3313 := by
    have hnat : (1849591193 : ℕ)^4337*625000000000^3313 ≤ 68615078631^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1849591193 10000000000 68615078631 625000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347117439/2500000000 : ℝ)^4337 ≤ (44510793343341/100000000000000 : ℝ)^3313 := by
    have hnat : (1347117439 : ℕ)^4337*100000000000000^3313 ≤ 44510793343341^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347117439 2500000000 44510793343341 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2694234911/5000000000 : ℝ)^4337 ≤ (8902158811407/20000000000000 : ℝ)^3313 := by
    have hnat : (2694234911 : ℕ)^4337*20000000000000^3313 ≤ 8902158811407^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694234911 5000000000 8902158811407 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1849591193/10000000000 : ℝ), (1347117439/2500000000 : ℝ), (2694234911/5000000000 : ℝ)] ![(68615078631/625000000000 : ℝ), (44510793343341/100000000000000 : ℝ), (8902158811407/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1849591193/10000000000 : ℝ)|^4337 ≤ (68615078631/625000000000 : ℝ)^3313
        have hw : |(-1849591193/10000000000 : ℝ)|=(1849591193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347117439/2500000000 : ℝ)|^4337 ≤ (44510793343341/100000000000000 : ℝ)^3313
        have hw : |(1347117439/2500000000 : ℝ)|=(1347117439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2694234911/5000000000 : ℝ)|^4337 ≤ (8902158811407/20000000000000 : ℝ)^3313
        have hw : |(2694234911/5000000000 : ℝ)|=(2694234911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_box_1 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642798429/5000000000 : ℝ)*x 0 + (-99534847/500000000 : ℝ)*x 1 + (673558703/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642798429/5000000000 : ℝ)^4337 ≤ (43401669852251/100000000000000 : ℝ)^3313 := by
    have hnat : (2642798429 : ℕ)^4337*100000000000000^3313 ≤ 43401669852251^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642798429 5000000000 43401669852251 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (99534847/500000000 : ℝ)^4337 ≤ (6043769107841/50000000000000 : ℝ)^3313 := by
    have hnat : (99534847 : ℕ)^4337*50000000000000^3313 ≤ 6043769107841^3313*500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99534847 500000000 6043769107841 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673558703/1250000000 : ℝ)^4337 ≤ (22255395957977/50000000000000 : ℝ)^3313 := by
    have hnat : (673558703 : ℕ)^4337*50000000000000^3313 ≤ 22255395957977^3313*1250000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673558703 1250000000 22255395957977 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642798429/5000000000 : ℝ), (-99534847/500000000 : ℝ), (673558703/1250000000 : ℝ)] ![(43401669852251/100000000000000 : ℝ), (6043769107841/50000000000000 : ℝ), (22255395957977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642798429/5000000000 : ℝ)|^4337 ≤ (43401669852251/100000000000000 : ℝ)^3313
        have hw : |(2642798429/5000000000 : ℝ)|=(2642798429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-99534847/500000000 : ℝ)|^4337 ≤ (6043769107841/50000000000000 : ℝ)^3313
        have hw : |(-99534847/500000000 : ℝ)|=(99534847/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673558703/1250000000 : ℝ)|^4337 ≤ (22255395957977/50000000000000 : ℝ)^3313
        have hw : |(673558703/1250000000 : ℝ)|=(673558703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_box_2 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285597149/10000000000 : ℝ)*x 0 + (5388469497/10000000000 : ℝ)*x 1 + (-24883709/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285597149/10000000000 : ℝ)^4337 ≤ (43401672980299/100000000000000 : ℝ)^3313 := by
    have hnat : (5285597149 : ℕ)^4337*100000000000000^3313 ≤ 43401672980299^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285597149 10000000000 43401672980299 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5388469497/10000000000 : ℝ)^4337 ≤ (8902158108527/20000000000000 : ℝ)^3313 := by
    have hnat : (5388469497 : ℕ)^4337*20000000000000^3313 ≤ 8902158108527^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388469497 10000000000 8902158108527 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24883709/125000000 : ℝ)^4337 ≤ (12087536466949/100000000000000 : ℝ)^3313 := by
    have hnat : (24883709 : ℕ)^4337*100000000000000^3313 ≤ 12087536466949^3313*125000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24883709 125000000 12087536466949 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285597149/10000000000 : ℝ), (5388469497/10000000000 : ℝ), (-24883709/125000000 : ℝ)] ![(43401672980299/100000000000000 : ℝ), (8902158108527/20000000000000 : ℝ), (12087536466949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285597149/10000000000 : ℝ)|^4337 ≤ (43401672980299/100000000000000 : ℝ)^3313
        have hw : |(5285597149/10000000000 : ℝ)|=(5285597149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5388469497/10000000000 : ℝ)|^4337 ≤ (8902158108527/20000000000000 : ℝ)^3313
        have hw : |(5388469497/10000000000 : ℝ)|=(5388469497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-24883709/125000000 : ℝ)|^4337 ≤ (12087536466949/100000000000000 : ℝ)^3313
        have hw : |(-24883709/125000000 : ℝ)|=(24883709/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_box_3 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4464943321/10000000000 : ℝ)*x 0 + (2123835217/5000000000 : ℝ)*x 1 + (1061917573/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4464943321/10000000000 : ℝ)^4337 ≤ (34799993734249/100000000000000 : ℝ)^3313 := by
    have hnat : (4464943321 : ℕ)^4337*100000000000000^3313 ≤ 34799993734249^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4464943321 10000000000 34799993734249 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123835217/5000000000 : ℝ)^4337 ≤ (16300001919441/50000000000000 : ℝ)^3313 := by
    have hnat : (2123835217 : ℕ)^4337*50000000000000^3313 ≤ 16300001919441^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123835217 5000000000 16300001919441 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061917573/2500000000 : ℝ)^4337 ≤ (32600002412213/100000000000000 : ℝ)^3313 := by
    have hnat : (1061917573 : ℕ)^4337*100000000000000^3313 ≤ 32600002412213^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061917573 2500000000 32600002412213 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4464943321/10000000000 : ℝ), (2123835217/5000000000 : ℝ), (1061917573/2500000000 : ℝ)] ![(34799993734249/100000000000000 : ℝ), (16300001919441/50000000000000 : ℝ), (32600002412213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4464943321/10000000000 : ℝ)|^4337 ≤ (34799993734249/100000000000000 : ℝ)^3313
        have hw : |(4464943321/10000000000 : ℝ)|=(4464943321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2123835217/5000000000 : ℝ)|^4337 ≤ (16300001919441/50000000000000 : ℝ)^3313
        have hw : |(2123835217/5000000000 : ℝ)|=(2123835217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1061917573/2500000000 : ℝ)|^4337 ≤ (32600002412213/100000000000000 : ℝ)^3313
        have hw : |(1061917573/2500000000 : ℝ)|=(1061917573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_box_4 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2181387651/10000000000 : ℝ)*x 0 + (526564917/1000000000 : ℝ)*x 1 + (526564889/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181387651/10000000000 : ℝ)^4337 ≤ (6812630258581/50000000000000 : ℝ)^3313 := by
    have hnat : (2181387651 : ℕ)^4337*50000000000000^3313 ≤ 6812630258581^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181387651 10000000000 6812630258581 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526564917/1000000000 : ℝ)^4337 ≤ (21593685618631/50000000000000 : ℝ)^3313 := by
    have hnat : (526564917 : ℕ)^4337*50000000000000^3313 ≤ 21593685618631^3313*1000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526564917 1000000000 21593685618631 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526564889/1000000000 : ℝ)^4337 ≤ (10796842057743/25000000000000 : ℝ)^3313 := by
    have hnat : (526564889 : ℕ)^4337*25000000000000^3313 ≤ 10796842057743^3313*1000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526564889 1000000000 10796842057743 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2181387651/10000000000 : ℝ), (526564917/1000000000 : ℝ), (526564889/1000000000 : ℝ)] ![(6812630258581/50000000000000 : ℝ), (21593685618631/50000000000000 : ℝ), (10796842057743/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2181387651/10000000000 : ℝ)|^4337 ≤ (6812630258581/50000000000000 : ℝ)^3313
        have hw : |(-2181387651/10000000000 : ℝ)|=(2181387651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526564917/1000000000 : ℝ)|^4337 ≤ (21593685618631/50000000000000 : ℝ)^3313
        have hw : |(526564917/1000000000 : ℝ)|=(526564917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526564889/1000000000 : ℝ)|^4337 ≤ (10796842057743/25000000000000 : ℝ)^3313
        have hw : |(526564889/1000000000 : ℝ)|=(526564889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_box_5 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5371736999/10000000000 : ℝ)*x 0 + (-2040220217/10000000000 : ℝ)*x 1 + (658206099/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371736999/10000000000 : ℝ)^4337 ≤ (8865987981939/20000000000000 : ℝ)^3313 := by
    have hnat : (5371736999 : ℕ)^4337*20000000000000^3313 ≤ 8865987981939^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371736999 10000000000 8865987981939 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2040220217/10000000000 : ℝ)^4337 ≤ (12482692899903/100000000000000 : ℝ)^3313 := by
    have hnat : (2040220217 : ℕ)^4337*100000000000000^3313 ≤ 12482692899903^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040220217 10000000000 12482692899903 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658206099/1250000000 : ℝ)^4337 ≤ (4318736717877/10000000000000 : ℝ)^3313 := by
    have hnat : (658206099 : ℕ)^4337*10000000000000^3313 ≤ 4318736717877^3313*1250000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658206099 1250000000 4318736717877 10000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371736999/10000000000 : ℝ), (-2040220217/10000000000 : ℝ), (658206099/1250000000 : ℝ)] ![(8865987981939/20000000000000 : ℝ), (12482692899903/100000000000000 : ℝ), (4318736717877/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371736999/10000000000 : ℝ)|^4337 ≤ (8865987981939/20000000000000 : ℝ)^3313
        have hw : |(5371736999/10000000000 : ℝ)|=(5371736999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2040220217/10000000000 : ℝ)|^4337 ≤ (12482692899903/100000000000000 : ℝ)^3313
        have hw : |(-2040220217/10000000000 : ℝ)|=(2040220217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658206099/1250000000 : ℝ)|^4337 ≤ (4318736717877/10000000000000 : ℝ)^3313
        have hw : |(658206099/1250000000 : ℝ)|=(658206099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_box_6 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074347471/2000000000 : ℝ)*x 0 + (210625947/400000000 : ℝ)*x 1 + (-1020109947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074347471/2000000000 : ℝ)^4337 ≤ (1385310742363/3125000000000 : ℝ)^3313 := by
    have hnat : (1074347471 : ℕ)^4337*3125000000000^3313 ≤ 1385310742363^3313*2000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074347471 2000000000 1385310742363 3125000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210625947/400000000 : ℝ)^4337 ≤ (4318736592257/10000000000000 : ℝ)^3313 := by
    have hnat : (210625947 : ℕ)^4337*10000000000000^3313 ≤ 4318736592257^3313*400000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210625947 400000000 4318736592257 10000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1020109947/5000000000 : ℝ)^4337 ≤ (1560336289109/12500000000000 : ℝ)^3313 := by
    have hnat : (1020109947 : ℕ)^4337*12500000000000^3313 ≤ 1560336289109^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020109947 5000000000 1560336289109 12500000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074347471/2000000000 : ℝ), (210625947/400000000 : ℝ), (-1020109947/5000000000 : ℝ)] ![(1385310742363/3125000000000 : ℝ), (4318736592257/10000000000000 : ℝ), (1560336289109/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074347471/2000000000 : ℝ)|^4337 ≤ (1385310742363/3125000000000 : ℝ)^3313
        have hw : |(1074347471/2000000000 : ℝ)|=(1074347471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210625947/400000000 : ℝ)|^4337 ≤ (4318736592257/10000000000000 : ℝ)^3313
        have hw : |(210625947/400000000 : ℝ)|=(210625947/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1020109947/5000000000 : ℝ)|^4337 ≤ (1560336289109/12500000000000 : ℝ)^3313
        have hw : |(-1020109947/5000000000 : ℝ)|=(1020109947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_box_7 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4169185053/10000000000 : ℝ)*x 0 + (2197748529/5000000000 : ℝ)*x 1 + (1098874257/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4169185053/10000000000 : ℝ)^4337 ≤ (6362745087383/20000000000000 : ℝ)^3313 := by
    have hnat : (4169185053 : ℕ)^4337*20000000000000^3313 ≤ 6362745087383^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169185053 10000000000 6362745087383 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197748529/5000000000 : ℝ)^4337 ≤ (1065410544669/3125000000000 : ℝ)^3313 := by
    have hnat : (2197748529 : ℕ)^4337*3125000000000^3313 ≤ 1065410544669^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197748529 5000000000 1065410544669 3125000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098874257/2500000000 : ℝ)^4337 ≤ (6818627424959/20000000000000 : ℝ)^3313 := by
    have hnat : (1098874257 : ℕ)^4337*20000000000000^3313 ≤ 6818627424959^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098874257 2500000000 6818627424959 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4169185053/10000000000 : ℝ), (2197748529/5000000000 : ℝ), (1098874257/2500000000 : ℝ)] ![(6362745087383/20000000000000 : ℝ), (1065410544669/3125000000000 : ℝ), (6818627424959/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4169185053/10000000000 : ℝ)|^4337 ≤ (6362745087383/20000000000000 : ℝ)^3313
        have hw : |(4169185053/10000000000 : ℝ)|=(4169185053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2197748529/5000000000 : ℝ)|^4337 ≤ (1065410544669/3125000000000 : ℝ)^3313
        have hw : |(2197748529/5000000000 : ℝ)|=(2197748529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1098874257/2500000000 : ℝ)|^4337 ≤ (6818627424959/20000000000000 : ℝ)^3313
        have hw : |(1098874257/2500000000 : ℝ)|=(1098874257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_box_8 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-422324419/2000000000 : ℝ)*x 0 + (5180932833/10000000000 : ℝ)*x 1 + (2701237033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422324419/2000000000 : ℝ)^4337 ≤ (6528823303519/50000000000000 : ℝ)^3313 := by
    have hnat : (422324419 : ℕ)^4337*50000000000000^3313 ≤ 6528823303519^3313*2000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422324419 2000000000 6528823303519 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180932833/10000000000 : ℝ)^4337 ≤ (42280063091167/100000000000000 : ℝ)^3313 := by
    have hnat : (5180932833 : ℕ)^4337*100000000000000^3313 ≤ 42280063091167^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180932833 10000000000 42280063091167 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701237033/5000000000 : ℝ)^4337 ≤ (44662290290493/100000000000000 : ℝ)^3313 := by
    have hnat : (2701237033 : ℕ)^4337*100000000000000^3313 ≤ 44662290290493^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701237033 5000000000 44662290290493 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-422324419/2000000000 : ℝ), (5180932833/10000000000 : ℝ), (2701237033/5000000000 : ℝ)] ![(6528823303519/50000000000000 : ℝ), (42280063091167/100000000000000 : ℝ), (44662290290493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-422324419/2000000000 : ℝ)|^4337 ≤ (6528823303519/50000000000000 : ℝ)^3313
        have hw : |(-422324419/2000000000 : ℝ)|=(422324419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180932833/10000000000 : ℝ)|^4337 ≤ (42280063091167/100000000000000 : ℝ)^3313
        have hw : |(5180932833/10000000000 : ℝ)|=(5180932833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701237033/5000000000 : ℝ)|^4337 ≤ (44662290290493/100000000000000 : ℝ)^3313
        have hw : |(2701237033/5000000000 : ℝ)|=(2701237033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_box_9 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275770711/10000000000 : ℝ)*x 0 + (-1984920533/10000000000 : ℝ)*x 1 + (1350618293/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275770711/10000000000 : ℝ)^4337 ≤ (8659215191841/20000000000000 : ℝ)^3313 := by
    have hnat : (5275770711 : ℕ)^4337*20000000000000^3313 ≤ 8659215191841^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275770711 10000000000 8659215191841 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1984920533/10000000000 : ℝ)^4337 ≤ (96333147263/800000000000 : ℝ)^3313 := by
    have hnat : (1984920533 : ℕ)^4337*800000000000^3313 ≤ 96333147263^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984920533 10000000000 96333147263 800000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350618293/2500000000 : ℝ)^4337 ≤ (4466228061543/10000000000000 : ℝ)^3313 := by
    have hnat : (1350618293 : ℕ)^4337*10000000000000^3313 ≤ 4466228061543^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350618293 2500000000 4466228061543 10000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275770711/10000000000 : ℝ), (-1984920533/10000000000 : ℝ), (1350618293/2500000000 : ℝ)] ![(8659215191841/20000000000000 : ℝ), (96333147263/800000000000 : ℝ), (4466228061543/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275770711/10000000000 : ℝ)|^4337 ≤ (8659215191841/20000000000000 : ℝ)^3313
        have hw : |(5275770711/10000000000 : ℝ)|=(5275770711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1984920533/10000000000 : ℝ)|^4337 ≤ (96333147263/800000000000 : ℝ)^3313
        have hw : |(-1984920533/10000000000 : ℝ)|=(1984920533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350618293/2500000000 : ℝ)|^4337 ≤ (4466228061543/10000000000000 : ℝ)^3313
        have hw : |(1350618293/2500000000 : ℝ)|=(1350618293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_box_10 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275773053/10000000000 : ℝ)*x 0 + (5402471629/10000000000 : ℝ)*x 1 + (-496229867/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275773053/10000000000 : ℝ)^4337 ≤ (8659220223921/20000000000000 : ℝ)^3313 := by
    have hnat : (5275773053 : ℕ)^4337*20000000000000^3313 ≤ 8659220223921^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275773053 10000000000 8659220223921 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402471629/10000000000 : ℝ)^4337 ≤ (44662263916749/100000000000000 : ℝ)^3313 := by
    have hnat : (5402471629 : ℕ)^4337*100000000000000^3313 ≤ 44662263916749^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402471629 10000000000 44662263916749 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (496229867/2500000000 : ℝ)^4337 ≤ (12041634950021/100000000000000 : ℝ)^3313 := by
    have hnat : (496229867 : ℕ)^4337*100000000000000^3313 ≤ 12041634950021^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496229867 2500000000 12041634950021 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275773053/10000000000 : ℝ), (5402471629/10000000000 : ℝ), (-496229867/2500000000 : ℝ)] ![(8659220223921/20000000000000 : ℝ), (44662263916749/100000000000000 : ℝ), (12041634950021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275773053/10000000000 : ℝ)|^4337 ≤ (8659220223921/20000000000000 : ℝ)^3313
        have hw : |(5275773053/10000000000 : ℝ)|=(5275773053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402471629/10000000000 : ℝ)|^4337 ≤ (44662263916749/100000000000000 : ℝ)^3313
        have hw : |(5402471629/10000000000 : ℝ)|=(5402471629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-496229867/2500000000 : ℝ)|^4337 ≤ (12041634950021/100000000000000 : ℝ)^3313
        have hw : |(-496229867/2500000000 : ℝ)|=(496229867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_box_11 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2249053247/5000000000 : ℝ)*x 0 + (1057700551/2500000000 : ℝ)*x 1 + (2115400363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2249053247/5000000000 : ℝ)^4337 ≤ (35138747905991/100000000000000 : ℝ)^3313 := by
    have hnat : (2249053247 : ℕ)^4337*100000000000000^3313 ≤ 35138747905991^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249053247 5000000000 35138747905991 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057700551/2500000000 : ℝ)^4337 ≤ (2026914590777/6250000000000 : ℝ)^3313 := by
    have hnat : (1057700551 : ℕ)^4337*6250000000000^3313 ≤ 2026914590777^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057700551 2500000000 2026914590777 6250000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115400363/5000000000 : ℝ)^4337 ≤ (32430618621273/100000000000000 : ℝ)^3313 := by
    have hnat : (2115400363 : ℕ)^4337*100000000000000^3313 ≤ 32430618621273^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115400363 5000000000 32430618621273 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2249053247/5000000000 : ℝ), (1057700551/2500000000 : ℝ), (2115400363/5000000000 : ℝ)] ![(35138747905991/100000000000000 : ℝ), (2026914590777/6250000000000 : ℝ), (32430618621273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2249053247/5000000000 : ℝ)|^4337 ≤ (35138747905991/100000000000000 : ℝ)^3313
        have hw : |(2249053247/5000000000 : ℝ)|=(2249053247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1057700551/2500000000 : ℝ)|^4337 ≤ (2026914590777/6250000000000 : ℝ)^3313
        have hw : |(1057700551/2500000000 : ℝ)|=(1057700551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115400363/5000000000 : ℝ)|^4337 ≤ (32430618621273/100000000000000 : ℝ)^3313
        have hw : |(2115400363/5000000000 : ℝ)|=(2115400363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_box_12 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-479906941/2500000000 : ℝ)*x 0 + (2735528301/5000000000 : ℝ)*x 1 + (656819147/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (479906941/2500000000 : ℝ)^4337 ≤ (11525767488253/100000000000000 : ℝ)^3313 := by
    have hnat : (479906941 : ℕ)^4337*100000000000000^3313 ≤ 11525767488253^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479906941 2500000000 11525767488253 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2735528301/5000000000 : ℝ)^4337 ≤ (22702978675603/50000000000000 : ℝ)^3313 := by
    have hnat : (2735528301 : ℕ)^4337*50000000000000^3313 ≤ 22702978675603^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735528301 5000000000 22702978675603 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656819147/1250000000 : ℝ)^4337 ≤ (43068275141261/100000000000000 : ℝ)^3313 := by
    have hnat : (656819147 : ℕ)^4337*100000000000000^3313 ≤ 43068275141261^3313*1250000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656819147 1250000000 43068275141261 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-479906941/2500000000 : ℝ), (2735528301/5000000000 : ℝ), (656819147/1250000000 : ℝ)] ![(11525767488253/100000000000000 : ℝ), (22702978675603/50000000000000 : ℝ), (43068275141261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-479906941/2500000000 : ℝ)|^4337 ≤ (11525767488253/100000000000000 : ℝ)^3313
        have hw : |(-479906941/2500000000 : ℝ)|=(479906941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2735528301/5000000000 : ℝ)|^4337 ≤ (22702978675603/50000000000000 : ℝ)^3313
        have hw : |(2735528301/5000000000 : ℝ)|=(2735528301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656819147/1250000000 : ℝ)|^4337 ≤ (43068275141261/100000000000000 : ℝ)^3313
        have hw : |(656819147/1250000000 : ℝ)|=(656819147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_box_13 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075903397/2000000000 : ℝ)*x 0 + (-2044591441/10000000000 : ℝ)*x 1 + (1050910681/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075903397/2000000000 : ℝ)^4337 ≤ (44414007067843/100000000000000 : ℝ)^3313 := by
    have hnat : (1075903397 : ℕ)^4337*100000000000000^3313 ≤ 44414007067843^3313*2000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075903397 2000000000 44414007067843 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2044591441/10000000000 : ℝ)^4337 ≤ (3129428826773/25000000000000 : ℝ)^3313 := by
    have hnat : (2044591441 : ℕ)^4337*25000000000000^3313 ≤ 3129428826773^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044591441 10000000000 3129428826773 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050910681/2000000000 : ℝ)^4337 ≤ (344546220787/800000000000 : ℝ)^3313 := by
    have hnat : (1050910681 : ℕ)^4337*800000000000^3313 ≤ 344546220787^3313*2000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050910681 2000000000 344546220787 800000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075903397/2000000000 : ℝ), (-2044591441/10000000000 : ℝ), (1050910681/2000000000 : ℝ)] ![(44414007067843/100000000000000 : ℝ), (3129428826773/25000000000000 : ℝ), (344546220787/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075903397/2000000000 : ℝ)|^4337 ≤ (44414007067843/100000000000000 : ℝ)^3313
        have hw : |(1075903397/2000000000 : ℝ)|=(1075903397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2044591441/10000000000 : ℝ)|^4337 ≤ (3129428826773/25000000000000 : ℝ)^3313
        have hw : |(-2044591441/10000000000 : ℝ)|=(2044591441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050910681/2000000000 : ℝ)|^4337 ≤ (344546220787/800000000000 : ℝ)^3313
        have hw : |(1050910681/2000000000 : ℝ)|=(1050910681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_box_14 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10506869/19531250 : ℝ)*x 0 + (5254553391/10000000000 : ℝ)*x 1 + (-1022295769/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10506869/19531250 : ℝ)^4337 ≤ (11103501612947/25000000000000 : ℝ)^3313 := by
    have hnat : (10506869 : ℕ)^4337*25000000000000^3313 ≤ 11103501612947^3313*19531250^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10506869 19531250 11103501612947 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254553391/10000000000 : ℝ)^4337 ≤ (21534138724079/50000000000000 : ℝ)^3313 := by
    have hnat : (5254553391 : ℕ)^4337*50000000000000^3313 ≤ 21534138724079^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254553391 10000000000 21534138724079 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1022295769/5000000000 : ℝ)^4337 ≤ (12517716084517/100000000000000 : ℝ)^3313 := by
    have hnat : (1022295769 : ℕ)^4337*100000000000000^3313 ≤ 12517716084517^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022295769 5000000000 12517716084517 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10506869/19531250 : ℝ), (5254553391/10000000000 : ℝ), (-1022295769/5000000000 : ℝ)] ![(11103501612947/25000000000000 : ℝ), (21534138724079/50000000000000 : ℝ), (12517716084517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10506869/19531250 : ℝ)|^4337 ≤ (11103501612947/25000000000000 : ℝ)^3313
        have hw : |(10506869/19531250 : ℝ)|=(10506869/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254553391/10000000000 : ℝ)|^4337 ≤ (21534138724079/50000000000000 : ℝ)^3313
        have hw : |(5254553391/10000000000 : ℝ)|=(5254553391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1022295769/5000000000 : ℝ)|^4337 ≤ (12517716084517/100000000000000 : ℝ)^3313
        have hw : |(-1022295769/5000000000 : ℝ)|=(1022295769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_box_15 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4142017527/10000000000 : ℝ)*x 0 + (4408840949/10000000000 : ℝ)*x 1 + (4408840931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4142017527/10000000000 : ℝ)^4337 ≤ (3154261689433/10000000000000 : ℝ)^3313 := by
    have hnat : (4142017527 : ℕ)^4337*10000000000000^3313 ≤ 3154261689433^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4142017527 10000000000 3154261689433 10000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4408840949/10000000000 : ℝ)^4337 ≤ (34228691639939/100000000000000 : ℝ)^3313 := by
    have hnat : (4408840949 : ℕ)^4337*100000000000000^3313 ≤ 34228691639939^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4408840949 10000000000 34228691639939 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4408840931/10000000000 : ℝ)^4337 ≤ (34228691457/100000000000 : ℝ)^3313 := by
    have hnat : (4408840931 : ℕ)^4337*100000000000^3313 ≤ 34228691457^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4408840931 10000000000 34228691457 100000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4142017527/10000000000 : ℝ), (4408840949/10000000000 : ℝ), (4408840931/10000000000 : ℝ)] ![(3154261689433/10000000000000 : ℝ), (34228691639939/100000000000000 : ℝ), (34228691457/100000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4142017527/10000000000 : ℝ)|^4337 ≤ (3154261689433/10000000000000 : ℝ)^3313
        have hw : |(4142017527/10000000000 : ℝ)|=(4142017527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4408840949/10000000000 : ℝ)|^4337 ≤ (34228691639939/100000000000000 : ℝ)^3313
        have hw : |(4408840949/10000000000 : ℝ)|=(4408840949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4408840931/10000000000 : ℝ)|^4337 ≤ (34228691457/100000000000 : ℝ)^3313
        have hw : |(4408840931/10000000000 : ℝ)|=(4408840931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1377_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62871/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5901/10000 : ℝ) ∧ (80157/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84487/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1841/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1123/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1841/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1123/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1841/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1123/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1841/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1123/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1841/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1123/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1841/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1123/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1123/10000 : ℝ) ^ (271/64 : ℝ) ≤ (2381725953091033/25000000000000000000 : ℝ) := by
    have hpowers : (1123/10000 : ℝ)^271 ≤ (2381725953091033/25000000000000000000 : ℝ)^64 := by
      have hnat : (1123 : ℕ)^271*25000000000000000000^64 ≤ 2381725953091033^64*10000^271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1123 10000 2381725953091033 25000000000000000000 271 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1123/10000 : ℝ)) (X := (2381725953091033/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hpowhi : (1841/12500 : ℝ) ^ (271/64 : ℝ) ≤ (6006739460400043/20000000000000000000 : ℝ) := by
    have hpowers : (1841/12500 : ℝ)^271 ≤ (6006739460400043/20000000000000000000 : ℝ)^64 := by
      have hnat : (1841 : ℕ)^271*20000000000000000000^64 ≤ 6006739460400043^64*12500^271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1841 12500 6006739460400043 20000000000000000000 271 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1841/12500 : ℝ)) (X := (6006739460400043/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502381725953091033/12500000000000000000 : ℝ) ≤ (1250056243309913/1250000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (12502381725953091033/12500000000000000000 : ℝ)^64 ≤ (1250056243309913/1250000000000000 : ℝ)^271 := by
      have hnat : (12502381725953091033 : ℕ)^64*1250000000000000^271 ≤ 1250056243309913^271*12500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502381725953091033 12500000000000000000 1250056243309913 1250000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250056243309913/1250000000000000 : ℝ)) (X := (12502381725953091033/12500000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039560601114364347/100000000000000000000 : ℝ) ≤ (10000934131372813/10000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (100039560601114364347/100000000000000000000 : ℝ)^64 ≤ (10000934131372813/10000000000000000 : ℝ)^271 := by
      have hnat : (100039560601114364347 : ℕ)^64*10000000000000000^271 ≤ 10000934131372813^271*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039560601114364347 100000000000000000000 10000934131372813 10000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000934131372813/10000000000000000 : ℝ)) (X := (100039560601114364347/100000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006006739460400043/10000000000000000000 : ℝ) ≤ (5000709158133161/5000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (10006006739460400043/10000000000000000000 : ℝ)^64 ≤ (5000709158133161/5000000000000000 : ℝ)^271 := by
      have hnat : (10006006739460400043 : ℕ)^64*5000000000000000^271 ≤ 5000709158133161^271*10000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006006739460400043 10000000000000000000 5000709158133161 5000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000709158133161/5000000000000000 : ℝ)) (X := (10006006739460400043/10000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2381725953091033/25000000000000000000 : ℝ) ≤ ((2914224926673032771/2915000000000000000 : ℝ)+2*(161394964503/116600000000000 : ℝ)*(1123/10000 : ℝ))^(271/64 : ℝ) := by
    rw [show (2914224926673032771/2915000000000000000 : ℝ)+2*(161394964503/116600000000000 : ℝ)*(1123/10000 : ℝ)=(1250056243309913/1250000000000000 : ℝ) by norm_num, show 1+2*(2381725953091033/25000000000000000000 : ℝ)=(12502381725953091033/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6006739460400043/20000000000000000000 : ℝ)+(2381725953091033/25000000000000000000 : ℝ) ≤ ((2914224926673032771/2915000000000000000 : ℝ)+(161394964503/116600000000000 : ℝ)*((1841/12500 : ℝ)+(1123/10000 : ℝ)))^(271/64 : ℝ) := by
    rw [show (2914224926673032771/2915000000000000000 : ℝ)+(161394964503/116600000000000 : ℝ)*((1841/12500 : ℝ)+(1123/10000 : ℝ))=(10000934131372813/10000000000000000 : ℝ) by norm_num, show 1+(6006739460400043/20000000000000000000 : ℝ)+(2381725953091033/25000000000000000000 : ℝ)=(100039560601114364347/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6006739460400043/20000000000000000000 : ℝ) ≤ ((2914224926673032771/2915000000000000000 : ℝ)+2*(161394964503/116600000000000 : ℝ)*(1841/12500 : ℝ))^(271/64 : ℝ) := by
    rw [show (2914224926673032771/2915000000000000000 : ℝ)+2*(161394964503/116600000000000 : ℝ)*(1841/12500 : ℝ)=(5000709158133161/5000000000000000 : ℝ) by norm_num, show 1+2*(6006739460400043/20000000000000000000 : ℝ)=(10006006739460400043/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2914224926673032771/2915000000000000000 : ℝ)*(X 1 0+X 2 0)+(161394964503/116600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (1123/10000 : ℝ)) (hi := (1841/12500 : ℝ)) (c := (2914224926673032771/2915000000000000000 : ℝ)) (alpha := (161394964503/116600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2914224926673032771/2915000000000000000 : ℝ)*(X 0 1+X 2 1)+(161394964503/116600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (1123/10000 : ℝ)) (hi := (1841/12500 : ℝ)) (c := (2914224926673032771/2915000000000000000 : ℝ)) (alpha := (161394964503/116600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2914224926673032771/2915000000000000000 : ℝ)*(X 0 2+X 1 2)+(161394964503/116600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (1123/10000 : ℝ)) (hi := (1841/12500 : ℝ)) (c := (2914224926673032771/2915000000000000000 : ℝ)) (alpha := (161394964503/116600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1849591193/10000000000 : ℝ)*X 0 0+(1347117439/2500000000 : ℝ)*X 0 1+(2694234911/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642798429/5000000000 : ℝ)*X 1 0+(-99534847/500000000 : ℝ)*X 1 1+(673558703/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285597149/10000000000 : ℝ)*X 2 0+(5388469497/10000000000 : ℝ)*X 2 1+(-24883709/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4464943321/10000000000 : ℝ)*X 0 0+(2123835217/5000000000 : ℝ)*X 0 1+(1061917573/2500000000 : ℝ)*X 0 2+(4464943321/10000000000 : ℝ)*X 1 0+(2123835217/5000000000 : ℝ)*X 1 1+(1061917573/2500000000 : ℝ)*X 1 2+(4464943321/10000000000 : ℝ)*X 2 0+(2123835217/5000000000 : ℝ)*X 2 1+(1061917573/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2181387651/10000000000 : ℝ)*X 0 0+(526564917/1000000000 : ℝ)*X 0 1+(526564889/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5371736999/10000000000 : ℝ)*X 1 0+(-2040220217/10000000000 : ℝ)*X 1 1+(658206099/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1074347471/2000000000 : ℝ)*X 2 0+(210625947/400000000 : ℝ)*X 2 1+(-1020109947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4169185053/10000000000 : ℝ)*X 0 0+(2197748529/5000000000 : ℝ)*X 0 1+(1098874257/2500000000 : ℝ)*X 0 2+(4169185053/10000000000 : ℝ)*X 1 0+(2197748529/5000000000 : ℝ)*X 1 1+(1098874257/2500000000 : ℝ)*X 1 2+(4169185053/10000000000 : ℝ)*X 2 0+(2197748529/5000000000 : ℝ)*X 2 1+(1098874257/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-422324419/2000000000 : ℝ)*X 0 0+(5180932833/10000000000 : ℝ)*X 0 1+(2701237033/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275770711/10000000000 : ℝ)*X 1 0+(-1984920533/10000000000 : ℝ)*X 1 1+(1350618293/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275773053/10000000000 : ℝ)*X 2 0+(5402471629/10000000000 : ℝ)*X 2 1+(-496229867/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2249053247/5000000000 : ℝ)*X 0 0+(1057700551/2500000000 : ℝ)*X 0 1+(2115400363/5000000000 : ℝ)*X 0 2+(2249053247/5000000000 : ℝ)*X 1 0+(1057700551/2500000000 : ℝ)*X 1 1+(2115400363/5000000000 : ℝ)*X 1 2+(2249053247/5000000000 : ℝ)*X 2 0+(1057700551/2500000000 : ℝ)*X 2 1+(2115400363/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-479906941/2500000000 : ℝ)*X 0 0+(2735528301/5000000000 : ℝ)*X 0 1+(656819147/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1075903397/2000000000 : ℝ)*X 1 0+(-2044591441/10000000000 : ℝ)*X 1 1+(1050910681/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((10506869/19531250 : ℝ)*X 2 0+(5254553391/10000000000 : ℝ)*X 2 1+(-1022295769/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4142017527/10000000000 : ℝ)*X 0 0+(4408840949/10000000000 : ℝ)*X 0 1+(4408840931/10000000000 : ℝ)*X 0 2+(4142017527/10000000000 : ℝ)*X 1 0+(4408840949/10000000000 : ℝ)*X 1 1+(4408840931/10000000000 : ℝ)*X 1 2+(4142017527/10000000000 : ℝ)*X 2 0+(4408840949/10000000000 : ℝ)*X 2 1+(4408840931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62871/100000 : ℝ) ≤ (-22907601244667003648182376131707/36437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1054541/625000000000 : ℝ)*(upper0) + (26970179/25000000000000 : ℝ)*(upper1) + (4513899/2500000000000 : ℝ)*(upper4) + (1722911/4000000000000 : ℝ)*(upper5) + (739916974534987/25000000000000 : ℝ)*(major0) + (739916974534987/25000000000000 : ℝ)*(major1) + (739916974534987/25000000000000 : ℝ)*(major2) + (2123016223/50000000000000 : ℝ)*(sp1) + (1622969087/100000000000000 : ℝ)*(sp3) + (2022194707306247/50000000000000 : ℝ)*(sp4) + (404439396781869/10000000000000 : ℝ)*(sp5) + (808879642770227/20000000000000 : ℝ)*(sp6) + (473973006730477/25000000000000 : ℝ)*(sp7) + (4399619321/50000000000000 : ℝ)*(sp8) + (947946824945497/50000000000000 : ℝ)*(f.failure) + (808879642770227/20000000000000 : ℝ)*(f.sum) + (6207584808383/2915000000000000000000000000 : ℝ)*base66 + (925002367426916023/72875000000000000000000000000000 : ℝ)*base68 + (920714378523916023/72875000000000000000000000000000 : ℝ)*base70 + (871879541589791023/72875000000000000000000000000000 : ℝ)*base72 + (4476377990171/1457500000000000000000000000 : ℝ)*base73 + (694922322825916023/72875000000000000000000000000000 : ℝ)*base76 + (314260588477416023/72875000000000000000000000000000 : ℝ)*base78 + (561875960964041023/72875000000000000000000000000000 : ℝ)*base80 + (146221983913/728750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (3719519/625000000000000000000 : ℝ)*base90 + (3719519/625000000000000000000 : ℝ)*base92 + (3719519/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (5901/10000 : ℝ) ≤ (7819109977778069208640357833627/13250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22463703/100000000000000 : ℝ)*(upper0) + (22609859/100000000000000 : ℝ)*(lower1) + (149127611/100000000000000 : ℝ)*(upper4) + (3029513344635169/100000000000000 : ℝ)*(major0) + (3029513344635169/100000000000000 : ℝ)*(major1) + (3029513344635169/100000000000000 : ℝ)*(major2) + (256169997365497/6250000000000 : ℝ)*(sp0) + (2049322929525809/50000000000000 : ℝ)*(sp1) + (2049338116381427/50000000000000 : ℝ)*(sp2) + (60644771856587/3125000000000 : ℝ)*(sp3) + (460175081/20000000000000 : ℝ)*(sp7) + (202842191/20000000000000 : ℝ)*(sp8) + (9389125911/12500000000000 : ℝ)*(sp9) + (11184824013/25000000000000 : ℝ)*(sp10) + (194063500028619/10000000000000 : ℝ)*(f.failure) + (2049360486029453/50000000000000 : ℝ)*(f.sum) + (33289241201567/5830000000000000000000000000 : ℝ)*base65 + (636022878203201701/291500000000000000000000000000000 : ℝ)*base68 + (2060693818516701701/291500000000000000000000000000000 : ℝ)*base70 + (3581775399324798299/291500000000000000000000000000000 : ℝ)*base71 + (189177540221253/5830000000000000000000000000 : ℝ)*base74 + (1315745628167701701/291500000000000000000000000000000 : ℝ)*base76 + (2210025374239798299/291500000000000000000000000000000 : ℝ)*base77 + (13062390346591701701/291500000000000000000000000000000 : ℝ)*base80 + (2710358077153/5830000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (557587/125000000000000000000 : ℝ)*base89 + (557587/125000000000000000000 : ℝ)*base91 + (557587/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (80157/100000 : ℝ) ≤ (584160288877824621821207001/728750000000000000000000000 : ℝ) := by norm_num
    linear_combination (71268221/100000000000000 : ℝ)*(lower2) + (186173129/25000000000000 : ℝ)*(lower3) + (207656143/25000000000000 : ℝ)*(upper4) + (19555837/4000000000000 : ℝ)*(lower5) + (417510170389403/12500000000000 : ℝ)*(major0) + (417510170389403/12500000000000 : ℝ)*(major1) + (417510170389403/12500000000000 : ℝ)*(major2) + (243618937087/100000000000000 : ℝ)*(sp1) + (42817705143/50000000000000 : ℝ)*(sp2) + (183420365177/50000000000000 : ℝ)*(sp3) + (4513865418493431/100000000000000 : ℝ)*(sp8) + (564202724944543/12500000000000 : ℝ)*(sp9) + (902755956616629/20000000000000 : ℝ)*(sp10) + (2139210728235791/100000000000000 : ℝ)*(sp11) + (427915513793229/20000000000000 : ℝ)*(f.failure) + (4513865418493431/100000000000000 : ℝ)*(f.sum) + (4367189954509/2915000000000000000000000000 : ℝ)*base66 + (48514159932711787/36437500000000000000000000000000 : ℝ)*base68 + (517275277177850713/36437500000000000000000000000000 : ℝ)*base69 + (1993203524363024287/36437500000000000000000000000000 : ℝ)*base72 + (464829160887/91093750000000000000000000 : ℝ)*base74 + (638973320313475713/36437500000000000000000000000000 : ℝ)*base75 + (2235002041935288213/36437500000000000000000000000000 : ℝ)*base77 + (126451032800961787/36437500000000000000000000000000 : ℝ)*base80 + (9121534606287/1457500000000000000000000000 : ℝ)*base82 + (320117/250000000000000000000 : ℝ)*base89 + (320117/250000000000000000000 : ℝ)*base91 + (320117/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84487/100000 : ℝ) ≤ (-1399282406635798402300504150191/1656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6039367/100000000000000 : ℝ)*(lower1) + (22335697/25000000000000 : ℝ)*(upper3) + (31734261/100000000000000 : ℝ)*(lower4) + (18822429/50000000000000 : ℝ)*(upper5) + (422118855332827/12500000000000 : ℝ)*(major0) + (422118855332827/12500000000000 : ℝ)*(major1) + (422118855332827/12500000000000 : ℝ)*(major2) + (775849997/100000000000000 : ℝ)*(sp0) + (868735489/12500000000000 : ℝ)*(sp6) + (1656607279/6250000000000 : ℝ)*(sp7) + (923773455501623/20000000000000 : ℝ)*(sp12) + (144339626667441/3125000000000 : ℝ)*(sp13) + (23094305517371/500000000000 : ℝ)*(sp14) + (108158439237449/5000000000000 : ℝ)*(sp15) + (540798822616361/25000000000000 : ℝ)*(f.failure) + (144339626667441/3125000000000 : ℝ)*(f.sum) + (4725052567459/2915000000000000000000000000 : ℝ)*base65 + (216020687357473617/36437500000000000000000000000000 : ℝ)*base67 + (45645414050223617/36437500000000000000000000000000 : ℝ)*base69 + (99112554440348617/36437500000000000000000000000000 : ℝ)*base71 + (2080771638853/364375000000000000000000000 : ℝ)*base73 + (130043734239651383/36437500000000000000000000000000 : ℝ)*base76 + (36306764607848617/36437500000000000000000000000000 : ℝ)*base77 + (126896736677151383/36437500000000000000000000000000 : ℝ)*base80 + (369902404599/45546875000000000000000000 : ℝ)*base82 + (1996047/312500000000000000000 : ℝ)*base90 + (1996047/312500000000000000000 : ℝ)*base92 + (1996047/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1377_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62871/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5901/10000 : ℝ) else (80157/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84487/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1377_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1377_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62871/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5901/10000 : ℝ) else (80157/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84487/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1377_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1377_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1377_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62871/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5901/10000 : ℝ) else (80157/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84487/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1377_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

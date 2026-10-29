-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1312_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:39:56.152678+00:00
-- url     : https://prove2.me/submissions/02bc617e-38b3-44f2-8b25-49b229e66af8

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
theorem support_rectangle_w1312_s0_0 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-456753723/2500000000 : ℝ)*x 0 + (6009974961/10000000000 : ℝ)*x 1 + (4803701003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (456753723/2500000000 : ℝ)^267 ≤ (10690322923683/100000000000000 : ℝ)^203 := by
    have hnat : (456753723 : ℕ)^267*100000000000000^203 ≤ 10690322923683^203*2500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456753723 2500000000 10690322923683 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6009974961/10000000000 : ℝ)^267 ≤ (2559337996457/5000000000000 : ℝ)^203 := by
    have hnat : (6009974961 : ℕ)^267*5000000000000^203 ≤ 2559337996457^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6009974961 10000000000 2559337996457 5000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4803701003/10000000000 : ℝ)^267 ≤ (9530729283299/25000000000000 : ℝ)^203 := by
    have hnat : (4803701003 : ℕ)^267*25000000000000^203 ≤ 9530729283299^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4803701003 10000000000 9530729283299 25000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-456753723/2500000000 : ℝ), (6009974961/10000000000 : ℝ), (4803701003/10000000000 : ℝ)] ![(10690322923683/100000000000000 : ℝ), (2559337996457/5000000000000 : ℝ), (9530729283299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-456753723/2500000000 : ℝ)|^267 ≤ (10690322923683/100000000000000 : ℝ)^203
        have hw : |(-456753723/2500000000 : ℝ)|=(456753723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6009974961/10000000000 : ℝ)|^267 ≤ (2559337996457/5000000000000 : ℝ)^203
        have hw : |(6009974961/10000000000 : ℝ)|=(6009974961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4803701003/10000000000 : ℝ)|^267 ≤ (9530729283299/25000000000000 : ℝ)^203
        have hw : |(4803701003/10000000000 : ℝ)|=(4803701003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s0_1 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (172036723/312500000 : ℝ)*x 0 + (-1257082313/5000000000 : ℝ)*x 1 + (960740189/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172036723/312500000 : ℝ)^267 ≤ (1425259144077/3125000000000 : ℝ)^203 := by
    have hnat : (172036723 : ℕ)^267*3125000000000^203 ≤ 1425259144077^203*312500000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172036723 312500000 1425259144077 3125000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1257082313/5000000000 : ℝ)^267 ≤ (8134395423829/50000000000000 : ℝ)^203 := by
    have hnat : (1257082313 : ℕ)^267*50000000000000^203 ≤ 8134395423829^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1257082313 5000000000 8134395423829 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (960740189/2000000000 : ℝ)^267 ≤ (38122916527781/100000000000000 : ℝ)^203 := by
    have hnat : (960740189 : ℕ)^267*100000000000000^203 ≤ 38122916527781^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960740189 2000000000 38122916527781 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172036723/312500000 : ℝ), (-1257082313/5000000000 : ℝ), (960740189/2000000000 : ℝ)] ![(1425259144077/3125000000000 : ℝ), (8134395423829/50000000000000 : ℝ), (38122916527781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172036723/312500000 : ℝ)|^267 ≤ (1425259144077/3125000000000 : ℝ)^203
        have hw : |(172036723/312500000 : ℝ)|=(172036723/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1257082313/5000000000 : ℝ)|^267 ≤ (8134395423829/50000000000000 : ℝ)^203
        have hw : |(-1257082313/5000000000 : ℝ)|=(1257082313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(960740189/2000000000 : ℝ)|^267 ≤ (38122916527781/100000000000000 : ℝ)^203
        have hw : |(960740189/2000000000 : ℝ)|=(960740189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s0_2 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5505174453/10000000000 : ℝ)*x 0 + (600462687/1250000000 : ℝ)*x 1 + (-100566593/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5505174453/10000000000 : ℝ)^267 ≤ (2280414258407/5000000000000 : ℝ)^203 := by
    have hnat : (5505174453 : ℕ)^267*5000000000000^203 ≤ 2280414258407^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505174453 10000000000 2280414258407 5000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (600462687/1250000000 : ℝ)^267 ≤ (19061461139613/50000000000000 : ℝ)^203 := by
    have hnat : (600462687 : ℕ)^267*50000000000000^203 ≤ 19061461139613^203*1250000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600462687 1250000000 19061461139613 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100566593/400000000 : ℝ)^267 ≤ (4067198135333/25000000000000 : ℝ)^203 := by
    have hnat : (100566593 : ℕ)^267*25000000000000^203 ≤ 4067198135333^203*400000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100566593 400000000 4067198135333 25000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5505174453/10000000000 : ℝ), (600462687/1250000000 : ℝ), (-100566593/400000000 : ℝ)] ![(2280414258407/5000000000000 : ℝ), (19061461139613/50000000000000 : ℝ), (4067198135333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5505174453/10000000000 : ℝ)|^267 ≤ (2280414258407/5000000000000 : ℝ)^203
        have hw : |(5505174453/10000000000 : ℝ)|=(5505174453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(600462687/1250000000 : ℝ)|^267 ≤ (19061461139613/50000000000000 : ℝ)^203
        have hw : |(600462687/1250000000 : ℝ)|=(600462687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-100566593/400000000 : ℝ)|^267 ≤ (4067198135333/25000000000000 : ℝ)^203
        have hw : |(-100566593/400000000 : ℝ)|=(100566593/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s0_3 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4183273253/10000000000 : ℝ)*x 0 + (3108191977/10000000000 : ℝ)*x 1 + (2803164873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4183273253/10000000000 : ℝ)^267 ≤ (6356547523133/20000000000000 : ℝ)^203 := by
    have hnat : (4183273253 : ℕ)^267*20000000000000^203 ≤ 6356547523133^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183273253 10000000000 6356547523133 20000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3108191977/10000000000 : ℝ)^267 ≤ (21503557039879/100000000000000 : ℝ)^203 := by
    have hnat : (3108191977 : ℕ)^267*100000000000000^203 ≤ 21503557039879^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3108191977 10000000000 21503557039879 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2803164873/5000000000 : ℝ)^267 ≤ (46713705334107/100000000000000 : ℝ)^203 := by
    have hnat : (2803164873 : ℕ)^267*100000000000000^203 ≤ 46713705334107^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2803164873 5000000000 46713705334107 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4183273253/10000000000 : ℝ), (3108191977/10000000000 : ℝ), (2803164873/5000000000 : ℝ)] ![(6356547523133/20000000000000 : ℝ), (21503557039879/100000000000000 : ℝ), (46713705334107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4183273253/10000000000 : ℝ)|^267 ≤ (6356547523133/20000000000000 : ℝ)^203
        have hw : |(4183273253/10000000000 : ℝ)|=(4183273253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3108191977/10000000000 : ℝ)|^267 ≤ (21503557039879/100000000000000 : ℝ)^203
        have hw : |(3108191977/10000000000 : ℝ)|=(3108191977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2803164873/5000000000 : ℝ)|^267 ≤ (46713705334107/100000000000000 : ℝ)^203
        have hw : |(2803164873/5000000000 : ℝ)|=(2803164873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s0_4 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-915815549/5000000000 : ℝ)*x 0 + (1208699993/2500000000 : ℝ)*x 1 + (5977767359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (915815549/5000000000 : ℝ)^267 ≤ (5362931648349/50000000000000 : ℝ)^203 := by
    have hnat : (915815549 : ℕ)^267*50000000000000^203 ≤ 5362931648349^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915815549 5000000000 5362931648349 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1208699993/2500000000 : ℝ)^267 ≤ (7689573001821/20000000000000 : ℝ)^203 := by
    have hnat : (1208699993 : ℕ)^267*20000000000000^203 ≤ 7689573001821^203*2500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208699993 2500000000 7689573001821 20000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5977767359/10000000000 : ℝ)^267 ≤ (50826271684999/100000000000000 : ℝ)^203 := by
    have hnat : (5977767359 : ℕ)^267*100000000000000^203 ≤ 50826271684999^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5977767359 10000000000 50826271684999 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-915815549/5000000000 : ℝ), (1208699993/2500000000 : ℝ), (5977767359/10000000000 : ℝ)] ![(5362931648349/50000000000000 : ℝ), (7689573001821/20000000000000 : ℝ), (50826271684999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-915815549/5000000000 : ℝ)|^267 ≤ (5362931648349/50000000000000 : ℝ)^203
        have hw : |(-915815549/5000000000 : ℝ)|=(915815549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1208699993/2500000000 : ℝ)|^267 ≤ (7689573001821/20000000000000 : ℝ)^203
        have hw : |(1208699993/2500000000 : ℝ)|=(1208699993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5977767359/10000000000 : ℝ)|^267 ≤ (50826271684999/100000000000000 : ℝ)^203
        have hw : |(5977767359/10000000000 : ℝ)|=(5977767359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s0_5 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (517662943/1000000000 : ℝ)*x 0 + (-670049497/5000000000 : ℝ)*x 1 + (5977767299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517662943/1000000000 : ℝ)^267 ≤ (328612789279/781250000000 : ℝ)^203 := by
    have hnat : (517662943 : ℕ)^267*781250000000^203 ≤ 328612789279^203*1000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517662943 1000000000 328612789279 781250000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (670049497/5000000000 : ℝ)^267 ≤ (444455746891/6250000000000 : ℝ)^203 := by
    have hnat : (670049497 : ℕ)^267*6250000000000^203 ≤ 444455746891^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670049497 5000000000 444455746891 6250000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5977767299/10000000000 : ℝ)^267 ≤ (50826271014009/100000000000000 : ℝ)^203 := by
    have hnat : (5977767299 : ℕ)^267*100000000000000^203 ≤ 50826271014009^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5977767299 10000000000 50826271014009 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517662943/1000000000 : ℝ), (-670049497/5000000000 : ℝ), (5977767299/10000000000 : ℝ)] ![(328612789279/781250000000 : ℝ), (444455746891/6250000000000 : ℝ), (50826271014009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517662943/1000000000 : ℝ)|^267 ≤ (328612789279/781250000000 : ℝ)^203
        have hw : |(517662943/1000000000 : ℝ)|=(517662943/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-670049497/5000000000 : ℝ)|^267 ≤ (444455746891/6250000000000 : ℝ)^203
        have hw : |(-670049497/5000000000 : ℝ)|=(670049497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5977767299/10000000000 : ℝ)|^267 ≤ (50826271014009/100000000000000 : ℝ)^203
        have hw : |(5977767299/10000000000 : ℝ)|=(5977767299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s0_6 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5176629443/10000000000 : ℝ)*x 0 + (5977767333/10000000000 : ℝ)*x 1 + (-1340098919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5176629443/10000000000 : ℝ)^267 ≤ (8412487433329/20000000000000 : ℝ)^203 := by
    have hnat : (5176629443 : ℕ)^267*20000000000000^203 ≤ 8412487433329^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176629443 10000000000 8412487433329 20000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5977767333/10000000000 : ℝ)^267 ≤ (50826271394237/100000000000000 : ℝ)^203 := by
    have hnat : (5977767333 : ℕ)^267*100000000000000^203 ≤ 50826271394237^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5977767333 10000000000 50826271394237 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1340098919/10000000000 : ℝ)^267 ≤ (711129142679/10000000000000 : ℝ)^203 := by
    have hnat : (1340098919 : ℕ)^267*10000000000000^203 ≤ 711129142679^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340098919 10000000000 711129142679 10000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5176629443/10000000000 : ℝ), (5977767333/10000000000 : ℝ), (-1340098919/10000000000 : ℝ)] ![(8412487433329/20000000000000 : ℝ), (50826271394237/100000000000000 : ℝ), (711129142679/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5176629443/10000000000 : ℝ)|^267 ≤ (8412487433329/20000000000000 : ℝ)^203
        have hw : |(5176629443/10000000000 : ℝ)|=(5176629443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5977767333/10000000000 : ℝ)|^267 ≤ (50826271394237/100000000000000 : ℝ)^203
        have hw : |(5977767333/10000000000 : ℝ)|=(5977767333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1340098919/10000000000 : ℝ)|^267 ≤ (711129142679/10000000000000 : ℝ)^203
        have hw : |(-1340098919/10000000000 : ℝ)|=(1340098919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s0_7 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4192832601/10000000000 : ℝ)*x 0 + (554192567/1000000000 : ℝ)*x 1 + (317489189/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4192832601/10000000000 : ℝ)^267 ≤ (3984787167699/12500000000000 : ℝ)^203 := by
    have hnat : (4192832601 : ℕ)^267*12500000000000^203 ≤ 3984787167699^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4192832601 10000000000 3984787167699 12500000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554192567/1000000000 : ℝ)^267 ≤ (46009166373971/100000000000000 : ℝ)^203 := by
    have hnat : (554192567 : ℕ)^267*100000000000000^203 ≤ 46009166373971^203*1000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554192567 1000000000 46009166373971 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317489189/1000000000 : ℝ)^267 ≤ (11056268140797/50000000000000 : ℝ)^203 := by
    have hnat : (317489189 : ℕ)^267*50000000000000^203 ≤ 11056268140797^203*1000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317489189 1000000000 11056268140797 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4192832601/10000000000 : ℝ), (554192567/1000000000 : ℝ), (317489189/1000000000 : ℝ)] ![(3984787167699/12500000000000 : ℝ), (46009166373971/100000000000000 : ℝ), (11056268140797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4192832601/10000000000 : ℝ)|^267 ≤ (3984787167699/12500000000000 : ℝ)^203
        have hw : |(4192832601/10000000000 : ℝ)|=(4192832601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(554192567/1000000000 : ℝ)|^267 ≤ (46009166373971/100000000000000 : ℝ)^203
        have hw : |(554192567/1000000000 : ℝ)|=(554192567/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317489189/1000000000 : ℝ)|^267 ≤ (11056268140797/50000000000000 : ℝ)^203
        have hw : |(317489189/1000000000 : ℝ)|=(317489189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1312_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153547737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1187/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27089/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4271/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4271 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4271*1^1024 ≤ 0^1024*1^4271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4271/1024 : ℝ) ≤ (2188933861628801923/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4271 ≤ (2188933861628801923/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4271*100000000000000000000^1024 ≤ 2188933861628801923^1024*5^4271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2188933861628801923 100000000000000000000 4271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2188933861628801923/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4271/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4271 := by
      have hnat : (1 : ℕ)^1024*1^4271 ≤ 1^4271*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102188933861628801923/100000000000000000000 : ℝ) ≤ (10052049961593871/10000000000000000 : ℝ) ^ (4271/1024 : ℝ) := by
    have hpowers : (102188933861628801923/100000000000000000000 : ℝ)^1024 ≤ (10052049961593871/10000000000000000 : ℝ)^4271 := by
      have hnat : (102188933861628801923 : ℕ)^1024*10000000000000000^4271 ≤ 10052049961593871^4271*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102188933861628801923 100000000000000000000 10052049961593871 10000000000000000 1024 4271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10052049961593871/10000000000000000 : ℝ)) (X := (102188933861628801923/100000000000000000000 : ℝ)) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52188933861628801923/50000000000000000000 : ℝ) ≤ (5052049961593871/5000000000000000 : ℝ) ^ (4271/1024 : ℝ) := by
    have hpowers : (52188933861628801923/50000000000000000000 : ℝ)^1024 ≤ (5052049961593871/5000000000000000 : ℝ)^4271 := by
      have hnat : (52188933861628801923 : ℕ)^1024*5000000000000000^4271 ≤ 5052049961593871^4271*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52188933861628801923 50000000000000000000 5052049961593871 5000000000000000 1024 4271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5052049961593871/5000000000000000 : ℝ)) (X := (52188933861628801923/50000000000000000000 : ℝ)) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(52049961593871/4000000000000000 : ℝ)*(0 : ℝ))^(4271/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(52049961593871/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2188933861628801923/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(52049961593871/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4271/1024 : ℝ) := by
    rw [show (1 : ℝ)+(52049961593871/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10052049961593871/10000000000000000 : ℝ) by norm_num, show 1+(2188933861628801923/100000000000000000000 : ℝ)+(0 : ℝ)=(102188933861628801923/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2188933861628801923/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(52049961593871/4000000000000000 : ℝ)*(2/5 : ℝ))^(4271/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(52049961593871/4000000000000000 : ℝ)*(2/5 : ℝ)=(5052049961593871/5000000000000000 : ℝ) by norm_num, show 1+2*(2188933861628801923/100000000000000000000 : ℝ)=(52188933861628801923/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(52049961593871/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4271/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (52049961593871/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(52049961593871/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4271/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (52049961593871/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(52049961593871/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4271/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (52049961593871/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-456753723/2500000000 : ℝ)*X 0 0+(6009974961/10000000000 : ℝ)*X 0 1+(4803701003/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((172036723/312500000 : ℝ)*X 1 0+(-1257082313/5000000000 : ℝ)*X 1 1+(960740189/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5505174453/10000000000 : ℝ)*X 2 0+(600462687/1250000000 : ℝ)*X 2 1+(-100566593/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4183273253/10000000000 : ℝ)*X 0 0+(3108191977/10000000000 : ℝ)*X 0 1+(2803164873/5000000000 : ℝ)*X 0 2+(4183273253/10000000000 : ℝ)*X 1 0+(3108191977/10000000000 : ℝ)*X 1 1+(2803164873/5000000000 : ℝ)*X 1 2+(4183273253/10000000000 : ℝ)*X 2 0+(3108191977/10000000000 : ℝ)*X 2 1+(2803164873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-915815549/5000000000 : ℝ)*X 0 0+(1208699993/2500000000 : ℝ)*X 0 1+(5977767359/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((517662943/1000000000 : ℝ)*X 1 0+(-670049497/5000000000 : ℝ)*X 1 1+(5977767299/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5176629443/10000000000 : ℝ)*X 2 0+(5977767333/10000000000 : ℝ)*X 2 1+(-1340098919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4192832601/10000000000 : ℝ)*X 0 0+(554192567/1000000000 : ℝ)*X 0 1+(317489189/1000000000 : ℝ)*X 0 2+(4192832601/10000000000 : ℝ)*X 1 0+(554192567/1000000000 : ℝ)*X 1 1+(317489189/1000000000 : ℝ)*X 1 2+(4192832601/10000000000 : ℝ)*X 2 0+(554192567/1000000000 : ℝ)*X 2 1+(317489189/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (254387078318349441880401/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1068299/2000000000000 : ℝ)*(base1) + (713194853/100000000000000 : ℝ)*(base19) + (305172267/50000000000000 : ℝ)*(base23) + (4183239/4000000000000 : ℝ)*(upper3) + (2630651/12500000000000 : ℝ)*(upper5) + (307325967309159/50000000000000 : ℝ)*(major0) + (307325967309159/50000000000000 : ℝ)*(major1) + (307325967309159/50000000000000 : ℝ)*(major2) + (829001607938831/100000000000000 : ℝ)*(sp0) + (165800569519503/20000000000000 : ℝ)*(sp1) + (829002950447833/100000000000000 : ℝ)*(sp2) + (400299063180941/100000000000000 : ℝ)*(sp3) + (1003134243/50000000000000 : ℝ)*(sp4) + (1107052679/100000000000000 : ℝ)*(sp7) + (40030022364857/10000000000000 : ℝ)*(f.failure) + (51812722549523/6250000000000 : ℝ)*(f.sum) + (175896370635511/100000000000000000000000000000 : ℝ)*base66 + (974529997435511/200000000000000000000000000000 : ℝ)*base68 + (1479036603964489/200000000000000000000000000000 : ℝ)*base69 + (626304581835511/200000000000000000000000000000 : ℝ)*base72 + (560512933135511/100000000000000000000000000000 : ℝ)*base74 + (430294537635511/200000000000000000000000000000 : ℝ)*base76 + (271789243635511/200000000000000000000000000000 : ℝ)*base78 + (211563034435511/200000000000000000000000000000 : ℝ)*base80 + (426187649464489/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (678609/1000000000000000000000 : ℝ)*base89 + (678609/1000000000000000000000 : ℝ)*base91 + (678609/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (107629729942615964471637/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2058543727/100000000000000 : ℝ)*(base19) + (519953439/25000000000000 : ℝ)*(base23) + (52915827/50000000000000 : ℝ)*(base32) + (287416539/100000000000000 : ℝ)*(upper3) + (102353991/50000000000000 : ℝ)*(upper5) + (81086559437749/12500000000000 : ℝ)*(major0) + (81086559437749/12500000000000 : ℝ)*(major1) + (81086559437749/12500000000000 : ℝ)*(major2) + (4559607373/100000000000000 : ℝ)*(sp1) + (303758343/6250000000000 : ℝ)*(sp2) + (437457543331233/50000000000000 : ℝ)*(sp4) + (437454234255683/50000000000000 : ℝ)*(sp5) + (874908146715223/100000000000000 : ℝ)*(sp6) + (422469471497247/100000000000000 : ℝ)*(sp7) + (422469577328901/100000000000000 : ℝ)*(f.failure) + (437457543331233/50000000000000 : ℝ)*(f.sum) + (20191900038621/25000000000000000000000000000 : ℝ)*base66 + (39823572336379/50000000000000000000000000000 : ℝ)*base67 + (184626061763621/50000000000000000000000000000 : ℝ)*base70 + (165998783313621/50000000000000000000000000000 : ℝ)*base72 + (8915714736379/25000000000000000000000000000 : ℝ)*base73 + (20951906986379/50000000000000000000000000000 : ℝ)*base75 + (72924470563621/50000000000000000000000000000 : ℝ)*base78 + (469089295413621/50000000000000000000000000000 : ℝ)*base80 + (65990437888621/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (53247037/10000000000000000000000 : ℝ)*base89 + (53247037/10000000000000000000000 : ℝ)*base91 + (53247037/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1312_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153547737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1187/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27089/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1312_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1312_s1_0 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2016160899/10000000000 : ℝ)*x 0 + (226234703/400000000 : ℝ)*x 1 + (5036703587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2016160899/10000000000 : ℝ)^267 ≤ (12169204599649/100000000000000 : ℝ)^203 := by
    have hnat : (2016160899 : ℕ)^267*100000000000000^203 ≤ 12169204599649^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016160899 10000000000 12169204599649 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226234703/400000000 : ℝ)^267 ≤ (47257357541227/100000000000000 : ℝ)^203 := by
    have hnat : (226234703 : ℕ)^267*100000000000000^203 ≤ 47257357541227^203*400000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226234703 400000000 47257357541227 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5036703587/10000000000 : ℝ)^267 ≤ (20286718924833/50000000000000 : ℝ)^203 := by
    have hnat : (5036703587 : ℕ)^267*50000000000000^203 ≤ 20286718924833^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5036703587 10000000000 20286718924833 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2016160899/10000000000 : ℝ), (226234703/400000000 : ℝ), (5036703587/10000000000 : ℝ)] ![(12169204599649/100000000000000 : ℝ), (47257357541227/100000000000000 : ℝ), (20286718924833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2016160899/10000000000 : ℝ)|^267 ≤ (12169204599649/100000000000000 : ℝ)^203
        have hw : |(-2016160899/10000000000 : ℝ)|=(2016160899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226234703/400000000 : ℝ)|^267 ≤ (47257357541227/100000000000000 : ℝ)^203
        have hw : |(226234703/400000000 : ℝ)|=(226234703/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5036703587/10000000000 : ℝ)|^267 ≤ (20286718924833/50000000000000 : ℝ)^203
        have hw : |(5036703587/10000000000 : ℝ)|=(5036703587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s1_1 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5408869019/10000000000 : ℝ)*x 0 + (-293428369/1250000000 : ℝ)*x 1 + (5036703601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5408869019/10000000000 : ℝ)^267 ≤ (8912359279891/20000000000000 : ℝ)^203 := by
    have hnat : (5408869019 : ℕ)^267*20000000000000^203 ≤ 8912359279891^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408869019 10000000000 8912359279891 20000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (293428369/1250000000 : ℝ)^267 ≤ (1486476557959/10000000000000 : ℝ)^203 := by
    have hnat : (293428369 : ℕ)^267*10000000000000^203 ≤ 1486476557959^203*1250000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293428369 1250000000 1486476557959 10000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5036703601/10000000000 : ℝ)^267 ≤ (40573437997999/100000000000000 : ℝ)^203 := by
    have hnat : (5036703601 : ℕ)^267*100000000000000^203 ≤ 40573437997999^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5036703601 10000000000 40573437997999 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5408869019/10000000000 : ℝ), (-293428369/1250000000 : ℝ), (5036703601/10000000000 : ℝ)] ![(8912359279891/20000000000000 : ℝ), (1486476557959/10000000000000 : ℝ), (40573437997999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5408869019/10000000000 : ℝ)|^267 ≤ (8912359279891/20000000000000 : ℝ)^203
        have hw : |(5408869019/10000000000 : ℝ)|=(5408869019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-293428369/1250000000 : ℝ)|^267 ≤ (1486476557959/10000000000000 : ℝ)^203
        have hw : |(-293428369/1250000000 : ℝ)|=(293428369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5036703601/10000000000 : ℝ)|^267 ≤ (40573437997999/100000000000000 : ℝ)^203
        have hw : |(5036703601/10000000000 : ℝ)|=(5036703601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s1_2 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (338054321/625000000 : ℝ)*x 0 + (5036703297/10000000000 : ℝ)*x 1 + (-586856797/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338054321/625000000 : ℝ)^267 ≤ (22280898833637/50000000000000 : ℝ)^203 := by
    have hnat : (338054321 : ℕ)^267*50000000000000^203 ≤ 22280898833637^203*625000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338054321 625000000 22280898833637 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5036703297/10000000000 : ℝ)^267 ≤ (40573434777047/100000000000000 : ℝ)^203 := by
    have hnat : (5036703297 : ℕ)^267*100000000000000^203 ≤ 40573434777047^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5036703297 10000000000 40573434777047 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (586856797/2500000000 : ℝ)^267 ≤ (14864767545181/100000000000000 : ℝ)^203 := by
    have hnat : (586856797 : ℕ)^267*100000000000000^203 ≤ 14864767545181^203*2500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586856797 2500000000 14864767545181 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(338054321/625000000 : ℝ), (5036703297/10000000000 : ℝ), (-586856797/2500000000 : ℝ)] ![(22280898833637/50000000000000 : ℝ), (40573434777047/100000000000000 : ℝ), (14864767545181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(338054321/625000000 : ℝ)|^267 ≤ (22280898833637/50000000000000 : ℝ)^203
        have hw : |(338054321/625000000 : ℝ)|=(338054321/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5036703297/10000000000 : ℝ)|^267 ≤ (40573434777047/100000000000000 : ℝ)^203
        have hw : |(5036703297/10000000000 : ℝ)|=(5036703297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-586856797/2500000000 : ℝ)|^267 ≤ (14864767545181/100000000000000 : ℝ)^203
        have hw : |(-586856797/2500000000 : ℝ)|=(586856797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s1_3 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4297624631/10000000000 : ℝ)*x 0 + (1850700049/5000000000 : ℝ)*x 1 + (2491830511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297624631/10000000000 : ℝ)^267 ≤ (16465164879869/50000000000000 : ℝ)^203 := by
    have hnat : (4297624631 : ℕ)^267*50000000000000^203 ≤ 16465164879869^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297624631 10000000000 16465164879869 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1850700049/5000000000 : ℝ)^267 ≤ (13528647823643/50000000000000 : ℝ)^203 := by
    have hnat : (1850700049 : ℕ)^267*50000000000000^203 ≤ 13528647823643^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1850700049 5000000000 13528647823643 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2491830511/5000000000 : ℝ)^267 ≤ (8002474914541/20000000000000 : ℝ)^203 := by
    have hnat : (2491830511 : ℕ)^267*20000000000000^203 ≤ 8002474914541^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491830511 5000000000 8002474914541 20000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297624631/10000000000 : ℝ), (1850700049/5000000000 : ℝ), (2491830511/5000000000 : ℝ)] ![(16465164879869/50000000000000 : ℝ), (13528647823643/50000000000000 : ℝ), (8002474914541/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297624631/10000000000 : ℝ)|^267 ≤ (16465164879869/50000000000000 : ℝ)^203
        have hw : |(4297624631/10000000000 : ℝ)|=(4297624631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1850700049/5000000000 : ℝ)|^267 ≤ (13528647823643/50000000000000 : ℝ)^203
        have hw : |(1850700049/5000000000 : ℝ)|=(1850700049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2491830511/5000000000 : ℝ)|^267 ≤ (8002474914541/20000000000000 : ℝ)^203
        have hw : |(2491830511/5000000000 : ℝ)|=(2491830511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s1_4 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-504188921/2500000000 : ℝ)*x 0 + (2522326693/5000000000 : ℝ)*x 1 + (2823884851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (504188921/2500000000 : ℝ)^267 ≤ (6086963334877/50000000000000 : ℝ)^203 := by
    have hnat : (504188921 : ℕ)^267*50000000000000^203 ≤ 6086963334877^203*2500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504188921 2500000000 6086963334877 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2522326693/5000000000 : ℝ)^267 ≤ (40657688796391/100000000000000 : ℝ)^203 := by
    have hnat : (2522326693 : ℕ)^267*100000000000000^203 ≤ 40657688796391^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2522326693 5000000000 40657688796391 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2823884851/5000000000 : ℝ)^267 ≤ (1179209613071/2500000000000 : ℝ)^203 := by
    have hnat : (2823884851 : ℕ)^267*2500000000000^203 ≤ 1179209613071^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2823884851 5000000000 1179209613071 2500000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-504188921/2500000000 : ℝ), (2522326693/5000000000 : ℝ), (2823884851/5000000000 : ℝ)] ![(6086963334877/50000000000000 : ℝ), (40657688796391/100000000000000 : ℝ), (1179209613071/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-504188921/2500000000 : ℝ)|^267 ≤ (6086963334877/50000000000000 : ℝ)^203
        have hw : |(-504188921/2500000000 : ℝ)|=(504188921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2522326693/5000000000 : ℝ)|^267 ≤ (40657688796391/100000000000000 : ℝ)^203
        have hw : |(2522326693/5000000000 : ℝ)|=(2522326693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2823884851/5000000000 : ℝ)|^267 ≤ (1179209613071/2500000000000 : ℝ)^203
        have hw : |(2823884851/5000000000 : ℝ)|=(2823884851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s1_5 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1049723127/2000000000 : ℝ)*x 0 + (-868180469/5000000000 : ℝ)*x 1 + (2823884707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049723127/2000000000 : ℝ)^267 ≤ (21416723348767/50000000000000 : ℝ)^203 := by
    have hnat : (1049723127 : ℕ)^267*50000000000000^203 ≤ 21416723348767^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049723127 2000000000 21416723348767 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (868180469/5000000000 : ℝ)^267 ≤ (9998171927879/100000000000000 : ℝ)^203 := by
    have hnat : (868180469 : ℕ)^267*100000000000000^203 ≤ 9998171927879^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868180469 5000000000 9998171927879 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2823884707/5000000000 : ℝ)^267 ≤ (47168381359239/100000000000000 : ℝ)^203 := by
    have hnat : (2823884707 : ℕ)^267*100000000000000^203 ≤ 47168381359239^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2823884707 5000000000 47168381359239 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049723127/2000000000 : ℝ), (-868180469/5000000000 : ℝ), (2823884707/5000000000 : ℝ)] ![(21416723348767/50000000000000 : ℝ), (9998171927879/100000000000000 : ℝ), (47168381359239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049723127/2000000000 : ℝ)|^267 ≤ (21416723348767/50000000000000 : ℝ)^203
        have hw : |(1049723127/2000000000 : ℝ)|=(1049723127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-868180469/5000000000 : ℝ)|^267 ≤ (9998171927879/100000000000000 : ℝ)^203
        have hw : |(-868180469/5000000000 : ℝ)|=(868180469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2823884707/5000000000 : ℝ)|^267 ≤ (47168381359239/100000000000000 : ℝ)^203
        have hw : |(2823884707/5000000000 : ℝ)|=(2823884707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s1_6 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1312153891/2500000000 : ℝ)*x 0 + (1129553853/2000000000 : ℝ)*x 1 + (-347272251/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312153891/2500000000 : ℝ)^267 ≤ (8566689187087/20000000000000 : ℝ)^203 := by
    have hnat : (1312153891 : ℕ)^267*20000000000000^203 ≤ 8566689187087^203*2500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312153891 2500000000 8566689187087 20000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129553853/2000000000 : ℝ)^267 ≤ (9433675944503/20000000000000 : ℝ)^203 := by
    have hnat : (1129553853 : ℕ)^267*20000000000000^203 ≤ 9433675944503^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129553853 2000000000 9433675944503 20000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (347272251/2000000000 : ℝ)^267 ≤ (4999087164337/50000000000000 : ℝ)^203 := by
    have hnat : (347272251 : ℕ)^267*50000000000000^203 ≤ 4999087164337^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347272251 2000000000 4999087164337 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312153891/2500000000 : ℝ), (1129553853/2000000000 : ℝ), (-347272251/2000000000 : ℝ)] ![(8566689187087/20000000000000 : ℝ), (9433675944503/20000000000000 : ℝ), (4999087164337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312153891/2500000000 : ℝ)|^267 ≤ (8566689187087/20000000000000 : ℝ)^203
        have hw : |(1312153891/2500000000 : ℝ)|=(1312153891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1129553853/2000000000 : ℝ)|^267 ≤ (9433675944503/20000000000000 : ℝ)^203
        have hw : |(1129553853/2000000000 : ℝ)|=(1129553853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-347272251/2000000000 : ℝ)|^267 ≤ (4999087164337/50000000000000 : ℝ)^203
        have hw : |(-347272251/2000000000 : ℝ)|=(347272251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s1_7 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2149427899/5000000000 : ℝ)*x 0 + (4967196653/10000000000 : ℝ)*x 1 + (929542803/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149427899/5000000000 : ℝ)^267 ≤ (32942738263017/100000000000000 : ℝ)^203 := by
    have hnat : (2149427899 : ℕ)^267*100000000000000^203 ≤ 32942738263017^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149427899 5000000000 32942738263017 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4967196653/10000000000 : ℝ)^267 ≤ (9959650648577/25000000000000 : ℝ)^203 := by
    have hnat : (4967196653 : ℕ)^267*25000000000000^203 ≤ 9959650648577^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4967196653 10000000000 9959650648577 25000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (929542803/2500000000 : ℝ)^267 ≤ (13609329563993/50000000000000 : ℝ)^203 := by
    have hnat : (929542803 : ℕ)^267*50000000000000^203 ≤ 13609329563993^203*2500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929542803 2500000000 13609329563993 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149427899/5000000000 : ℝ), (4967196653/10000000000 : ℝ), (929542803/2500000000 : ℝ)] ![(32942738263017/100000000000000 : ℝ), (9959650648577/25000000000000 : ℝ), (13609329563993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149427899/5000000000 : ℝ)|^267 ≤ (32942738263017/100000000000000 : ℝ)^203
        have hw : |(2149427899/5000000000 : ℝ)|=(2149427899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4967196653/10000000000 : ℝ)|^267 ≤ (9959650648577/25000000000000 : ℝ)^203
        have hw : |(4967196653/10000000000 : ℝ)|=(4967196653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(929542803/2500000000 : ℝ)|^267 ≤ (13609329563993/50000000000000 : ℝ)^203
        have hw : |(929542803/2500000000 : ℝ)|=(929542803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1312_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153547737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1187/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1321/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4923/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1187/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1187/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1187/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1187/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1187/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1187/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1187/100000 : ℝ) ^ (4271/1024 : ℝ) ≤ (46526407133/5000000000000000000 : ℝ) := by
    have hpowers : (1187/100000 : ℝ)^4271 ≤ (46526407133/5000000000000000000 : ℝ)^1024 := by
      have hnat : (1187 : ℕ)^4271*5000000000000000000^1024 ≤ 46526407133^1024*100000^4271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1187 100000 46526407133 5000000000000000000 4271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1187/100000 : ℝ)) (X := (46526407133/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27089/100000 : ℝ) ^ (4271/1024 : ℝ) ≤ (17230468631813981/4000000000000000000 : ℝ) := by
    have hpowers : (27089/100000 : ℝ)^4271 ≤ (17230468631813981/4000000000000000000 : ℝ)^1024 := by
      have hnat : (27089 : ℕ)^4271*4000000000000000000^1024 ≤ 17230468631813981^1024*100000^4271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27089 100000 17230468631813981 4000000000000000000 4271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27089/100000 : ℝ)) (X := (17230468631813981/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500000046526407133/2500000000000000000 : ℝ) ≤ (5000000022310017/5000000000000000 : ℝ) ^ (4271/1024 : ℝ) := by
    have hpowers : (2500000046526407133/2500000000000000000 : ℝ)^1024 ≤ (5000000022310017/5000000000000000 : ℝ)^4271 := by
      have hnat : (2500000046526407133 : ℕ)^1024*5000000000000000^4271 ≤ 5000000022310017^4271*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500000046526407133 2500000000000000000 5000000022310017 5000000000000000 1024 4271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000022310017/5000000000000000 : ℝ)) (X := (2500000046526407133/2500000000000000000 : ℝ)) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20086152529264698437/20000000000000000000 : ℝ) ≤ (1251288868243171/1250000000000000 : ℝ) ^ (4271/1024 : ℝ) := by
    have hpowers : (20086152529264698437/20000000000000000000 : ℝ)^1024 ≤ (1251288868243171/1250000000000000 : ℝ)^4271 := by
      have hnat : (20086152529264698437 : ℕ)^1024*1250000000000000^4271 ≤ 1251288868243171^4271*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20086152529264698437 20000000000000000000 1251288868243171 1250000000000000 1024 4271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251288868243171/1250000000000000 : ℝ)) (X := (20086152529264698437/20000000000000000000 : ℝ)) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2017230468631813981/2000000000000000000 : ℝ) ≤ (5010310923635351/5000000000000000 : ℝ) ^ (4271/1024 : ℝ) := by
    have hpowers : (2017230468631813981/2000000000000000000 : ℝ)^1024 ≤ (5010310923635351/5000000000000000 : ℝ)^4271 := by
      have hnat : (2017230468631813981 : ℕ)^1024*5000000000000000^4271 ≤ 5010310923635351^4271*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2017230468631813981 2000000000000000000 5010310923635351 5000000000000000 1024 4271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5010310923635351/5000000000000000 : ℝ)) (X := (2017230468631813981/2000000000000000000 : ℝ)) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(46526407133/5000000000000000000 : ℝ) ≤ ((32374440384500222219/32377500000000000000 : ℝ)+2*(5155450662667/1295100000000000 : ℝ)*(1187/100000 : ℝ))^(4271/1024 : ℝ) := by
    rw [show (32374440384500222219/32377500000000000000 : ℝ)+2*(5155450662667/1295100000000000 : ℝ)*(1187/100000 : ℝ)=(5000000022310017/5000000000000000 : ℝ) by norm_num, show 1+2*(46526407133/5000000000000000000 : ℝ)=(2500000046526407133/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17230468631813981/4000000000000000000 : ℝ)+(46526407133/5000000000000000000 : ℝ) ≤ ((32374440384500222219/32377500000000000000 : ℝ)+(5155450662667/1295100000000000 : ℝ)*((27089/100000 : ℝ)+(1187/100000 : ℝ)))^(4271/1024 : ℝ) := by
    rw [show (32374440384500222219/32377500000000000000 : ℝ)+(5155450662667/1295100000000000 : ℝ)*((27089/100000 : ℝ)+(1187/100000 : ℝ))=(1251288868243171/1250000000000000 : ℝ) by norm_num, show 1+(17230468631813981/4000000000000000000 : ℝ)+(46526407133/5000000000000000000 : ℝ)=(20086152529264698437/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17230468631813981/4000000000000000000 : ℝ) ≤ ((32374440384500222219/32377500000000000000 : ℝ)+2*(5155450662667/1295100000000000 : ℝ)*(27089/100000 : ℝ))^(4271/1024 : ℝ) := by
    rw [show (32374440384500222219/32377500000000000000 : ℝ)+2*(5155450662667/1295100000000000 : ℝ)*(27089/100000 : ℝ)=(5010310923635351/5000000000000000 : ℝ) by norm_num, show 1+2*(17230468631813981/4000000000000000000 : ℝ)=(2017230468631813981/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32374440384500222219/32377500000000000000 : ℝ)*(X 1 0+X 2 0)+(5155450662667/1295100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4271/1024 : ℝ)) (lo := (1187/100000 : ℝ)) (hi := (27089/100000 : ℝ)) (c := (32374440384500222219/32377500000000000000 : ℝ)) (alpha := (5155450662667/1295100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32374440384500222219/32377500000000000000 : ℝ)*(X 0 1+X 2 1)+(5155450662667/1295100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4271/1024 : ℝ)) (lo := (1187/100000 : ℝ)) (hi := (27089/100000 : ℝ)) (c := (32374440384500222219/32377500000000000000 : ℝ)) (alpha := (5155450662667/1295100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32374440384500222219/32377500000000000000 : ℝ)*(X 0 2+X 1 2)+(5155450662667/1295100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4271/1024 : ℝ)) (lo := (1187/100000 : ℝ)) (hi := (27089/100000 : ℝ)) (c := (32374440384500222219/32377500000000000000 : ℝ)) (alpha := (5155450662667/1295100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2016160899/10000000000 : ℝ)*X 0 0+(226234703/400000000 : ℝ)*X 0 1+(5036703587/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5408869019/10000000000 : ℝ)*X 1 0+(-293428369/1250000000 : ℝ)*X 1 1+(5036703601/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((338054321/625000000 : ℝ)*X 2 0+(5036703297/10000000000 : ℝ)*X 2 1+(-586856797/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4297624631/10000000000 : ℝ)*X 0 0+(1850700049/5000000000 : ℝ)*X 0 1+(2491830511/5000000000 : ℝ)*X 0 2+(4297624631/10000000000 : ℝ)*X 1 0+(1850700049/5000000000 : ℝ)*X 1 1+(2491830511/5000000000 : ℝ)*X 1 2+(4297624631/10000000000 : ℝ)*X 2 0+(1850700049/5000000000 : ℝ)*X 2 1+(2491830511/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-504188921/2500000000 : ℝ)*X 0 0+(2522326693/5000000000 : ℝ)*X 0 1+(2823884851/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1049723127/2000000000 : ℝ)*X 1 0+(-868180469/5000000000 : ℝ)*X 1 1+(2823884707/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1312153891/2500000000 : ℝ)*X 2 0+(1129553853/2000000000 : ℝ)*X 2 1+(-347272251/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2149427899/5000000000 : ℝ)*X 0 0+(4967196653/10000000000 : ℝ)*X 0 1+(929542803/2500000000 : ℝ)*X 0 2+(2149427899/5000000000 : ℝ)*X 1 0+(4967196653/10000000000 : ℝ)*X 1 1+(929542803/2500000000 : ℝ)*X 1 2+(2149427899/5000000000 : ℝ)*X 2 0+(4967196653/10000000000 : ℝ)*X 2 1+(929542803/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (273728791476113661144591363/44968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73826977/100000000000000 : ℝ)*(base1) + (1007024527/100000000000000 : ℝ)*(base19) + (208392153/20000000000000 : ℝ)*(base23) + (177722443/100000000000000 : ℝ)*(upper3) + (93134459/100000000000000 : ℝ)*(upper5) + (299371112408769/25000000000000 : ℝ)*(major0) + (299371112408769/25000000000000 : ℝ)*(major1) + (299371112408769/25000000000000 : ℝ)*(major2) + (1615086442389751/100000000000000 : ℝ)*(sp0) + (80754503051769/5000000000000 : ℝ)*(sp1) + (807545013049571/50000000000000 : ℝ)*(sp2) + (779874765248809/100000000000000 : ℝ)*(sp3) + (2349748567/50000000000000 : ℝ)*(sp4) + (1394615739/50000000000000 : ℝ)*(sp7) + (155975525661453/20000000000000 : ℝ)*(f.failure) + (403772767014977/25000000000000 : ℝ)*(f.sum) + (45466456487767/10792500000000000000000000000 : ℝ)*base65 + (50089130278597121/89937500000000000000000000000000 : ℝ)*base68 + (225193761996472121/89937500000000000000000000000000 : ℝ)*base70 + (36307514337527879/89937500000000000000000000000000 : ℝ)*base71 + (33483656175701/5396250000000000000000000000 : ℝ)*base73 + (451169292283215379/89937500000000000000000000000000 : ℝ)*base75 + (243614432875777879/89937500000000000000000000000000 : ℝ)*base77 + (234414514197965379/89937500000000000000000000000000 : ℝ)*base79 + (17521508331667/10792500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (16281861/2000000000000000000000 : ℝ)*base89 + (16281861/2000000000000000000000 : ℝ)*base91 + (16281861/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5478893483523835807281247697/539625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40442913/100000000000000 : ℝ)*(base1) + (983098611/50000000000000 : ℝ)*(base19) + (190356647/10000000000000 : ℝ)*(base23) + (50787603/25000000000000 : ℝ)*(upper3) + (132790359/50000000000000 : ℝ)*(upper5) + (1229339851654163/100000000000000 : ℝ)*(major0) + (1229339851654163/100000000000000 : ℝ)*(major1) + (1229339851654163/100000000000000 : ℝ)*(major2) + (4762095343/50000000000000 : ℝ)*(sp1) + (2051874459/25000000000000 : ℝ)*(sp2) + (103628470249323/6250000000000 : ℝ)*(sp4) + (1658043993158347/100000000000000 : ℝ)*(sp5) + (33160907449639/2000000000000 : ℝ)*(sp6) + (800623840880823/100000000000000 : ℝ)*(sp7) + (100077985165467/12500000000000 : ℝ)*(f.failure) + (331611096709251/20000000000000 : ℝ)*(f.sum) + (27320823440989/64755000000000000000000000000 : ℝ)*base66 + (657315194191740899/1079250000000000000000000000000000 : ℝ)*base67 + (3972072762950490899/1079250000000000000000000000000000 : ℝ)*base69 + (2515750891688759101/1079250000000000000000000000000000 : ℝ)*base72 + (40602895675667/32377500000000000000000000000 : ℝ)*base74 + (1451882672433509101/1079250000000000000000000000000000 : ℝ)*base76 + (6139383617711009101/1079250000000000000000000000000000 : ℝ)*base78 + (3767943503432759101/1079250000000000000000000000000000 : ℝ)*base80 + (264405358951931/64755000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (9101821/1250000000000000000000 : ℝ)*base90 + (9101821/1250000000000000000000 : ℝ)*base92 + (9101821/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1312_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153547737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1187/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1321/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4923/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1312_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1312_s2_0 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2058996381/10000000000 : ℝ)*x 0 + (1372064527/2500000000 : ℝ)*x 1 + (1294230329/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2058996381/10000000000 : ℝ)^267 ≤ (12510398295923/100000000000000 : ℝ)^203 := by
    have hnat : (2058996381 : ℕ)^267*100000000000000^203 ≤ 12510398295923^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058996381 10000000000 12510398295923 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372064527/2500000000 : ℝ)^267 ≤ (45424045199531/100000000000000 : ℝ)^203 := by
    have hnat : (1372064527 : ℕ)^267*100000000000000^203 ≤ 45424045199531^203*2500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372064527 2500000000 45424045199531 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294230329/2500000000 : ℝ)^267 ≤ (8413111297947/20000000000000 : ℝ)^203 := by
    have hnat : (1294230329 : ℕ)^267*20000000000000^203 ≤ 8413111297947^203*2500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294230329 2500000000 8413111297947 20000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2058996381/10000000000 : ℝ), (1372064527/2500000000 : ℝ), (1294230329/2500000000 : ℝ)] ![(12510398295923/100000000000000 : ℝ), (45424045199531/100000000000000 : ℝ), (8413111297947/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2058996381/10000000000 : ℝ)|^267 ≤ (12510398295923/100000000000000 : ℝ)^203
        have hw : |(-2058996381/10000000000 : ℝ)|=(2058996381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372064527/2500000000 : ℝ)|^267 ≤ (45424045199531/100000000000000 : ℝ)^203
        have hw : |(1372064527/2500000000 : ℝ)|=(1372064527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294230329/2500000000 : ℝ)|^267 ≤ (8413111297947/20000000000000 : ℝ)^203
        have hw : |(1294230329/2500000000 : ℝ)|=(1294230329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s2_1 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5368107563/10000000000 : ℝ)*x 0 + (-1110071329/5000000000 : ℝ)*x 1 + (207076837/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368107563/10000000000 : ℝ)^267 ≤ (2757539273887/6250000000000 : ℝ)^203 := by
    have hnat : (5368107563 : ℕ)^267*6250000000000^203 ≤ 2757539273887^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368107563 10000000000 2757539273887 6250000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1110071329/5000000000 : ℝ)^267 ≤ (13813819285949/100000000000000 : ℝ)^203 := by
    have hnat : (1110071329 : ℕ)^267*100000000000000^203 ≤ 13813819285949^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110071329 5000000000 13813819285949 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207076837/400000000 : ℝ)^267 ≤ (42065552310979/100000000000000 : ℝ)^203 := by
    have hnat : (207076837 : ℕ)^267*100000000000000^203 ≤ 42065552310979^203*400000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207076837 400000000 42065552310979 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368107563/10000000000 : ℝ), (-1110071329/5000000000 : ℝ), (207076837/400000000 : ℝ)] ![(2757539273887/6250000000000 : ℝ), (13813819285949/100000000000000 : ℝ), (42065552310979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368107563/10000000000 : ℝ)|^267 ≤ (2757539273887/6250000000000 : ℝ)^203
        have hw : |(5368107563/10000000000 : ℝ)|=(5368107563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1110071329/5000000000 : ℝ)|^267 ≤ (13813819285949/100000000000000 : ℝ)^203
        have hw : |(-1110071329/5000000000 : ℝ)|=(1110071329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207076837/400000000 : ℝ)|^267 ≤ (42065552310979/100000000000000 : ℝ)^203
        have hw : |(207076837/400000000 : ℝ)|=(207076837/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s2_2 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5368107003/10000000000 : ℝ)*x 0 + (2588460727/5000000000 : ℝ)*x 1 + (-555035677/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368107003/10000000000 : ℝ)^267 ≤ (44120622328453/100000000000000 : ℝ)^203 := by
    have hnat : (5368107003 : ℕ)^267*100000000000000^203 ≤ 44120622328453^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368107003 10000000000 44120622328453 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588460727/5000000000 : ℝ)^267 ≤ (42065557964591/100000000000000 : ℝ)^203 := by
    have hnat : (2588460727 : ℕ)^267*100000000000000^203 ≤ 42065557964591^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588460727 5000000000 42065557964591 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (555035677/2500000000 : ℝ)^267 ≤ (3453454923783/25000000000000 : ℝ)^203 := by
    have hnat : (555035677 : ℕ)^267*25000000000000^203 ≤ 3453454923783^203*2500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555035677 2500000000 3453454923783 25000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368107003/10000000000 : ℝ), (2588460727/5000000000 : ℝ), (-555035677/2500000000 : ℝ)] ![(44120622328453/100000000000000 : ℝ), (42065557964591/100000000000000 : ℝ), (3453454923783/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368107003/10000000000 : ℝ)|^267 ≤ (44120622328453/100000000000000 : ℝ)^203
        have hw : |(5368107003/10000000000 : ℝ)|=(5368107003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588460727/5000000000 : ℝ)|^267 ≤ (42065557964591/100000000000000 : ℝ)^203
        have hw : |(2588460727/5000000000 : ℝ)|=(2588460727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-555035677/2500000000 : ℝ)|^267 ≤ (3453454923783/25000000000000 : ℝ)^203
        have hw : |(-555035677/2500000000 : ℝ)|=(555035677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s2_3 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1081868441/2500000000 : ℝ)*x 0 + (1004106869/2500000000 : ℝ)*x 1 + (2330599999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081868441/2500000000 : ℝ)^267 ≤ (33231484028431/100000000000000 : ℝ)^203 := by
    have hnat : (1081868441 : ℕ)^267*100000000000000^203 ≤ 33231484028431^203*2500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081868441 2500000000 33231484028431 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004106869/2500000000 : ℝ)^267 ≤ (30126048652543/100000000000000 : ℝ)^203 := by
    have hnat : (1004106869 : ℕ)^267*100000000000000^203 ≤ 30126048652543^203*2500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004106869 2500000000 30126048652543 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2330599999/5000000000 : ℝ)^267 ≤ (18321233654151/50000000000000 : ℝ)^203 := by
    have hnat : (2330599999 : ℕ)^267*50000000000000^203 ≤ 18321233654151^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2330599999 5000000000 18321233654151 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081868441/2500000000 : ℝ), (1004106869/2500000000 : ℝ), (2330599999/5000000000 : ℝ)] ![(33231484028431/100000000000000 : ℝ), (30126048652543/100000000000000 : ℝ), (18321233654151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081868441/2500000000 : ℝ)|^267 ≤ (33231484028431/100000000000000 : ℝ)^203
        have hw : |(1081868441/2500000000 : ℝ)|=(1081868441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004106869/2500000000 : ℝ)|^267 ≤ (30126048652543/100000000000000 : ℝ)^203
        have hw : |(1004106869/2500000000 : ℝ)|=(1004106869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2330599999/5000000000 : ℝ)|^267 ≤ (18321233654151/50000000000000 : ℝ)^203
        have hw : |(2330599999/5000000000 : ℝ)|=(2330599999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s2_4 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2059071543/10000000000 : ℝ)*x 0 + (5178940669/10000000000 : ℝ)*x 1 + (342888761/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2059071543/10000000000 : ℝ)^267 ≤ (12510998959923/100000000000000 : ℝ)^203 := by
    have hnat : (2059071543 : ℕ)^267*100000000000000^203 ≤ 12510998959923^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059071543 10000000000 12510998959923 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178940669/10000000000 : ℝ)^267 ≤ (42087139362117/100000000000000 : ℝ)^203 := by
    have hnat : (5178940669 : ℕ)^267*100000000000000^203 ≤ 42087139362117^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178940669 10000000000 42087139362117 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (342888761/625000000 : ℝ)^267 ≤ (2270093083189/5000000000000 : ℝ)^203 := by
    have hnat : (342888761 : ℕ)^267*5000000000000^203 ≤ 2270093083189^203*625000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342888761 625000000 2270093083189 5000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2059071543/10000000000 : ℝ), (5178940669/10000000000 : ℝ), (342888761/625000000 : ℝ)] ![(12510998959923/100000000000000 : ℝ), (42087139362117/100000000000000 : ℝ), (2270093083189/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2059071543/10000000000 : ℝ)|^267 ≤ (12510998959923/100000000000000 : ℝ)^203
        have hw : |(-2059071543/10000000000 : ℝ)|=(2059071543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178940669/10000000000 : ℝ)|^267 ≤ (42087139362117/100000000000000 : ℝ)^203
        have hw : |(5178940669/10000000000 : ℝ)|=(5178940669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(342888761/625000000 : ℝ)|^267 ≤ (2270093083189/5000000000000 : ℝ)^203
        have hw : |(342888761/625000000 : ℝ)|=(342888761/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s2_5 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2644063553/5000000000 : ℝ)*x 0 + (-1910842931/10000000000 : ℝ)*x 1 + (685777533/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644063553/5000000000 : ℝ)^267 ≤ (1730322292793/4000000000000 : ℝ)^203 := by
    have hnat : (2644063553 : ℕ)^267*4000000000000^203 ≤ 1730322292793^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644063553 5000000000 1730322292793 4000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1910842931/10000000000 : ℝ)^267 ≤ (11340080040409/100000000000000 : ℝ)^203 := by
    have hnat : (1910842931 : ℕ)^267*100000000000000^203 ≤ 11340080040409^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1910842931 10000000000 11340080040409 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685777533/1250000000 : ℝ)^267 ≤ (709404103463/1562500000000 : ℝ)^203 := by
    have hnat : (685777533 : ℕ)^267*1562500000000^203 ≤ 709404103463^203*1250000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685777533 1250000000 709404103463 1562500000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644063553/5000000000 : ℝ), (-1910842931/10000000000 : ℝ), (685777533/1250000000 : ℝ)] ![(1730322292793/4000000000000 : ℝ), (11340080040409/100000000000000 : ℝ), (709404103463/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644063553/5000000000 : ℝ)|^267 ≤ (1730322292793/4000000000000 : ℝ)^203
        have hw : |(2644063553/5000000000 : ℝ)|=(2644063553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1910842931/10000000000 : ℝ)|^267 ≤ (11340080040409/100000000000000 : ℝ)^203
        have hw : |(-1910842931/10000000000 : ℝ)|=(1910842931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(685777533/1250000000 : ℝ)|^267 ≤ (709404103463/1562500000000 : ℝ)^203
        have hw : |(685777533/1250000000 : ℝ)|=(685777533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s2_6 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5288127221/10000000000 : ℝ)*x 0 + (5486220183/10000000000 : ℝ)*x 1 + (-382168577/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288127221/10000000000 : ℝ)^267 ≤ (21629029278567/50000000000000 : ℝ)^203 := by
    have hnat : (5288127221 : ℕ)^267*50000000000000^203 ≤ 21629029278567^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288127221 10000000000 21629029278567 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5486220183/10000000000 : ℝ)^267 ≤ (45401861739973/100000000000000 : ℝ)^203 := by
    have hnat : (5486220183 : ℕ)^267*100000000000000^203 ≤ 45401861739973^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486220183 10000000000 45401861739973 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (382168577/2000000000 : ℝ)^267 ≤ (11340079681351/100000000000000 : ℝ)^203 := by
    have hnat : (382168577 : ℕ)^267*100000000000000^203 ≤ 11340079681351^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382168577 2000000000 11340079681351 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288127221/10000000000 : ℝ), (5486220183/10000000000 : ℝ), (-382168577/2000000000 : ℝ)] ![(21629029278567/50000000000000 : ℝ), (45401861739973/100000000000000 : ℝ), (11340079681351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288127221/10000000000 : ℝ)|^267 ≤ (21629029278567/50000000000000 : ℝ)^203
        have hw : |(5288127221/10000000000 : ℝ)|=(5288127221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5486220183/10000000000 : ℝ)|^267 ≤ (45401861739973/100000000000000 : ℝ)^203
        have hw : |(5486220183/10000000000 : ℝ)|=(5486220183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-382168577/2000000000 : ℝ)|^267 ≤ (11340079681351/100000000000000 : ℝ)^203
        have hw : |(-382168577/2000000000 : ℝ)|=(382168577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s2_7 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1081907041/2500000000 : ℝ)*x 0 + (1164253989/2500000000 : ℝ)*x 1 + (502581649/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081907041/2500000000 : ℝ)^267 ≤ (33233043510029/100000000000000 : ℝ)^203 := by
    have hnat : (1081907041 : ℕ)^267*100000000000000^203 ≤ 33233043510029^203*2500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081907041 2500000000 33233043510029 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1164253989/2500000000 : ℝ)^267 ≤ (9149803065997/25000000000000 : ℝ)^203 := by
    have hnat : (1164253989 : ℕ)^267*25000000000000^203 ≤ 9149803065997^203*2500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1164253989 2500000000 9149803065997 25000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502581649/1250000000 : ℝ)^267 ≤ (30167744209301/100000000000000 : ℝ)^203 := by
    have hnat : (502581649 : ℕ)^267*100000000000000^203 ≤ 30167744209301^203*1250000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502581649 1250000000 30167744209301 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081907041/2500000000 : ℝ), (1164253989/2500000000 : ℝ), (502581649/1250000000 : ℝ)] ![(33233043510029/100000000000000 : ℝ), (9149803065997/25000000000000 : ℝ), (30167744209301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081907041/2500000000 : ℝ)|^267 ≤ (33233043510029/100000000000000 : ℝ)^203
        have hw : |(1081907041/2500000000 : ℝ)|=(1081907041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1164253989/2500000000 : ℝ)|^267 ≤ (9149803065997/25000000000000 : ℝ)^203
        have hw : |(1164253989/2500000000 : ℝ)|=(1164253989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(502581649/1250000000 : ℝ)|^267 ≤ (30167744209301/100000000000000 : ℝ)^203
        have hw : |(502581649/1250000000 : ℝ)|=(502581649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1312_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153547737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4923/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1321/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (603/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4057/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4923/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1321/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4923/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1321/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4923/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1321/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4923/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1321/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4923/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1321/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4923/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1321/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1321/20000 : ℝ) ^ (4271/1024 : ℝ) ≤ (47848616862783/4000000000000000000 : ℝ) := by
    have hpowers : (1321/20000 : ℝ)^4271 ≤ (47848616862783/4000000000000000000 : ℝ)^1024 := by
      have hnat : (1321 : ℕ)^4271*4000000000000000000^1024 ≤ 47848616862783^1024*20000^4271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1321 20000 47848616862783 4000000000000000000 4271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1321/20000 : ℝ)) (X := (47848616862783/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4923/25000 : ℝ) ^ (4271/1024 : ℝ) ≤ (56954041434853293/50000000000000000000 : ℝ) := by
    have hpowers : (4923/25000 : ℝ)^4271 ≤ (56954041434853293/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4923 : ℕ)^4271*50000000000000000000^1024 ≤ 56954041434853293^1024*25000^4271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4923 25000 56954041434853293 50000000000000000000 4271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4923/25000 : ℝ)) (X := (56954041434853293/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000047848616862783/2000000000000000000 : ℝ) ≤ (10000057359562267/10000000000000000 : ℝ) ^ (4271/1024 : ℝ) := by
    have hpowers : (2000047848616862783/2000000000000000000 : ℝ)^1024 ≤ (10000057359562267/10000000000000000 : ℝ)^4271 := by
      have hnat : (2000047848616862783 : ℕ)^1024*10000000000000000^4271 ≤ 10000057359562267^4271*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000047848616862783 2000000000000000000 10000057359562267 10000000000000000 1024 4271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000057359562267/10000000000000000 : ℝ)) (X := (2000047848616862783/2000000000000000000 : ℝ)) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100115104298291276161/100000000000000000000 : ℝ) ≤ (5001379246841811/5000000000000000 : ℝ) ^ (4271/1024 : ℝ) := by
    have hpowers : (100115104298291276161/100000000000000000000 : ℝ)^1024 ≤ (5001379246841811/5000000000000000 : ℝ)^4271 := by
      have hnat : (100115104298291276161 : ℕ)^1024*5000000000000000^4271 ≤ 5001379246841811^4271*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100115104298291276161 100000000000000000000 5001379246841811 5000000000000000 1024 4271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001379246841811/5000000000000000 : ℝ)) (X := (100115104298291276161/100000000000000000000 : ℝ)) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25056954041434853293/25000000000000000000 : ℝ) ≤ (10005459627804977/10000000000000000 : ℝ) ^ (4271/1024 : ℝ) := by
    have hpowers : (25056954041434853293/25000000000000000000 : ℝ)^1024 ≤ (10005459627804977/10000000000000000 : ℝ)^4271 := by
      have hnat : (25056954041434853293 : ℕ)^1024*10000000000000000^4271 ≤ 10005459627804977^4271*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25056954041434853293 25000000000000000000 10005459627804977 10000000000000000 1024 4271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005459627804977/10000000000000000 : ℝ)) (X := (25056954041434853293/25000000000000000000 : ℝ)) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(47848616862783/4000000000000000000 : ℝ) ≤ ((130835068682848288679/130870000000000000000 : ℝ)+2*(540226824271/261740000000000 : ℝ)*(1321/20000 : ℝ))^(4271/1024 : ℝ) := by
    rw [show (130835068682848288679/130870000000000000000 : ℝ)+2*(540226824271/261740000000000 : ℝ)*(1321/20000 : ℝ)=(10000057359562267/10000000000000000 : ℝ) by norm_num, show 1+2*(47848616862783/4000000000000000000 : ℝ)=(2000047848616862783/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(56954041434853293/50000000000000000000 : ℝ)+(47848616862783/4000000000000000000 : ℝ) ≤ ((130835068682848288679/130870000000000000000 : ℝ)+(540226824271/261740000000000 : ℝ)*((4923/25000 : ℝ)+(1321/20000 : ℝ)))^(4271/1024 : ℝ) := by
    rw [show (130835068682848288679/130870000000000000000 : ℝ)+(540226824271/261740000000000 : ℝ)*((4923/25000 : ℝ)+(1321/20000 : ℝ))=(5001379246841811/5000000000000000 : ℝ) by norm_num, show 1+(56954041434853293/50000000000000000000 : ℝ)+(47848616862783/4000000000000000000 : ℝ)=(100115104298291276161/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(56954041434853293/50000000000000000000 : ℝ) ≤ ((130835068682848288679/130870000000000000000 : ℝ)+2*(540226824271/261740000000000 : ℝ)*(4923/25000 : ℝ))^(4271/1024 : ℝ) := by
    rw [show (130835068682848288679/130870000000000000000 : ℝ)+2*(540226824271/261740000000000 : ℝ)*(4923/25000 : ℝ)=(10005459627804977/10000000000000000 : ℝ) by norm_num, show 1+2*(56954041434853293/50000000000000000000 : ℝ)=(25056954041434853293/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (130835068682848288679/130870000000000000000 : ℝ)*(X 1 0+X 2 0)+(540226824271/261740000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4271/1024 : ℝ)) (lo := (1321/20000 : ℝ)) (hi := (4923/25000 : ℝ)) (c := (130835068682848288679/130870000000000000000 : ℝ)) (alpha := (540226824271/261740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (130835068682848288679/130870000000000000000 : ℝ)*(X 0 1+X 2 1)+(540226824271/261740000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4271/1024 : ℝ)) (lo := (1321/20000 : ℝ)) (hi := (4923/25000 : ℝ)) (c := (130835068682848288679/130870000000000000000 : ℝ)) (alpha := (540226824271/261740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (130835068682848288679/130870000000000000000 : ℝ)*(X 0 2+X 1 2)+(540226824271/261740000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4271/1024 : ℝ)) (lo := (1321/20000 : ℝ)) (hi := (4923/25000 : ℝ)) (c := (130835068682848288679/130870000000000000000 : ℝ)) (alpha := (540226824271/261740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2058996381/10000000000 : ℝ)*X 0 0+(1372064527/2500000000 : ℝ)*X 0 1+(1294230329/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5368107563/10000000000 : ℝ)*X 1 0+(-1110071329/5000000000 : ℝ)*X 1 1+(207076837/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5368107003/10000000000 : ℝ)*X 2 0+(2588460727/5000000000 : ℝ)*X 2 1+(-555035677/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1081868441/2500000000 : ℝ)*X 0 0+(1004106869/2500000000 : ℝ)*X 0 1+(2330599999/5000000000 : ℝ)*X 0 2+(1081868441/2500000000 : ℝ)*X 1 0+(1004106869/2500000000 : ℝ)*X 1 1+(2330599999/5000000000 : ℝ)*X 1 2+(1081868441/2500000000 : ℝ)*X 2 0+(1004106869/2500000000 : ℝ)*X 2 1+(2330599999/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2059071543/10000000000 : ℝ)*X 0 0+(5178940669/10000000000 : ℝ)*X 0 1+(342888761/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644063553/5000000000 : ℝ)*X 1 0+(-1910842931/10000000000 : ℝ)*X 1 1+(685777533/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288127221/10000000000 : ℝ)*X 2 0+(5486220183/10000000000 : ℝ)*X 2 1+(-382168577/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081907041/2500000000 : ℝ)*X 0 0+(1164253989/2500000000 : ℝ)*X 0 1+(502581649/1250000000 : ℝ)*X 0 2+(1081907041/2500000000 : ℝ)*X 1 0+(1164253989/2500000000 : ℝ)*X 1 1+(502581649/1250000000 : ℝ)*X 1 2+(1081907041/2500000000 : ℝ)*X 2 0+(1164253989/2500000000 : ℝ)*X 2 1+(502581649/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9075021081006363911169069159/1635875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (130962033/6250000000000 : ℝ)*(base19) + (252536241/20000000000000 : ℝ)*(base23) + (267137671/100000000000000 : ℝ)*(lower2) + (336883149/50000000000000 : ℝ)*(upper3) + (196259/125000000000 : ℝ)*(upper5) + (1190735958163707/50000000000000 : ℝ)*(major0) + (1190735958163707/50000000000000 : ℝ)*(major1) + (1190735958163707/50000000000000 : ℝ)*(major2) + (802992912413531/25000000000000 : ℝ)*(sp0) + (1605988192431591/50000000000000 : ℝ)*(sp1) + (1605988608787253/50000000000000 : ℝ)*(sp2) + (310189461535541/20000000000000 : ℝ)*(sp3) + (3415300793/50000000000000 : ℝ)*(sp4) + (17859804649/100000000000000 : ℝ)*(sp7) + (775482583741177/50000000000000 : ℝ)*(f.failure) + (321197848025571/10000000000000 : ℝ)*(f.sum) + (2348068197347/1635875000000000000000000000 : ℝ)*base65 + (3234671046000273053/6543500000000000000000000000000000 : ℝ)*base67 + (9513376098957726947/6543500000000000000000000000000000 : ℝ)*base70 + (26772321963631726947/6543500000000000000000000000000000 : ℝ)*base72 + (25659344074939/6543500000000000000000000000 : ℝ)*base73 + (50503018494762726947/6543500000000000000000000000000000 : ℝ)*base76 + (55029903573893726947/6543500000000000000000000000000000 : ℝ)*base78 + (42863719119462726947/6543500000000000000000000000000000 : ℝ)*base80 + (6762381454443/1635875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (22066449/5000000000000000000000 : ℝ)*base89 + (22066449/5000000000000000000000 : ℝ)*base91 + (22066449/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1521410782646033444799/817937500000000000000000000 : ℝ) := by norm_num
    linear_combination (52529999/12500000000000 : ℝ)*(base19) + (621446167/100000000000000 : ℝ)*(base23) + (17002799/25000000000000 : ℝ)*(upper3) + (11768807/25000000000000 : ℝ)*(lower4) + (1206449145764127/50000000000000 : ℝ)*(major0) + (1206449145764127/50000000000000 : ℝ)*(major1) + (1206449145764127/50000000000000 : ℝ)*(major2) + (37967439/781250000000 : ℝ)*(sp1) + (3799030703/50000000000000 : ℝ)*(sp2) + (351770787/100000000000000 : ℝ)*(sp3) + (3254364509960699/100000000000000 : ℝ)*(sp4) + (1627179614944257/50000000000000 : ℝ)*(sp5) + (1627178145226563/50000000000000 : ℝ)*(sp6) + (1571431659323101/100000000000000 : ℝ)*(sp7) + (12276812586671/781250000000 : ℝ)*(f.failure) + (3254364509960699/100000000000000 : ℝ)*(f.sum) + (25586472766091/13087000000000000000000000000 : ℝ)*base66 + (32541411906309581767/6543500000000000000000000000000000 : ℝ)*base68 + (19544705944180081767/6543500000000000000000000000000000 : ℝ)*base70 + (9218114861524918233/6543500000000000000000000000000000 : ℝ)*base71 + (3822542780273/3271750000000000000000000000 : ℝ)*base74 + (66173820488987918233/6543500000000000000000000000000000 : ℝ)*base75 + (10721546254470918233/6543500000000000000000000000000000 : ℝ)*base77 + (45397287313478081767/6543500000000000000000000000000000 : ℝ)*base80 + (735859935993/6543500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (23973/78125000000000000000 : ℝ)*base90 + (23973/78125000000000000000 : ℝ)*base92 + (23973/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1312_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153547737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4923/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1321/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (603/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4057/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1312_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1312_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153547737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (603/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4057/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1312_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1312_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1312_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153547737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (603/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4057/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1312_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

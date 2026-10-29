-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1428_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:53:35.255986+00:00
-- url     : https://prove2.me/submissions/ce867732-e3bc-4c4e-838c-c4f7d737aa83

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
theorem support_rectangle_w1428_s0_0 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1759380129/10000000000 : ℝ)*x 0 + (745074207/1250000000 : ℝ)*x 1 + (1207752351/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1759380129/10000000000 : ℝ)^1097 ≤ (5183433524459/50000000000000 : ℝ)^841 := by
    have hnat : (1759380129 : ℕ)^1097*50000000000000^841 ≤ 5183433524459^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759380129 10000000000 5183433524459 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (745074207/1250000000 : ℝ)^1097 ≤ (50919924594347/100000000000000 : ℝ)^841 := by
    have hnat : (745074207 : ℕ)^1097*100000000000000^841 ≤ 50919924594347^841*1250000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745074207 1250000000 50919924594347 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1207752351/2500000000 : ℝ)^1097 ≤ (387132083343/1000000000000 : ℝ)^841 := by
    have hnat : (1207752351 : ℕ)^1097*1000000000000^841 ≤ 387132083343^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207752351 2500000000 387132083343 1000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1759380129/10000000000 : ℝ), (745074207/1250000000 : ℝ), (1207752351/2500000000 : ℝ)] ![(5183433524459/50000000000000 : ℝ), (50919924594347/100000000000000 : ℝ), (387132083343/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1759380129/10000000000 : ℝ)|^1097 ≤ (5183433524459/50000000000000 : ℝ)^841
        have hw : |(-1759380129/10000000000 : ℝ)|=(1759380129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(745074207/1250000000 : ℝ)|^1097 ≤ (50919924594347/100000000000000 : ℝ)^841
        have hw : |(745074207/1250000000 : ℝ)|=(745074207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1207752351/2500000000 : ℝ)|^1097 ≤ (387132083343/1000000000000 : ℝ)^841
        have hw : |(1207752351/2500000000 : ℝ)|=(1207752351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s0_1 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5492210371/10000000000 : ℝ)*x 0 + (-2397522627/10000000000 : ℝ)*x 1 + (4831009841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5492210371/10000000000 : ℝ)^1097 ≤ (45764247362543/100000000000000 : ℝ)^841 := by
    have hnat : (5492210371 : ℕ)^1097*100000000000000^841 ≤ 45764247362543^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492210371 10000000000 45764247362543 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2397522627/10000000000 : ℝ)^1097 ≤ (15522539723097/100000000000000 : ℝ)^841 := by
    have hnat : (2397522627 : ℕ)^1097*100000000000000^841 ≤ 15522539723097^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397522627 10000000000 15522539723097 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4831009841/10000000000 : ℝ)^1097 ≤ (19356606451083/50000000000000 : ℝ)^841 := by
    have hnat : (4831009841 : ℕ)^1097*50000000000000^841 ≤ 19356606451083^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4831009841 10000000000 19356606451083 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5492210371/10000000000 : ℝ), (-2397522627/10000000000 : ℝ), (4831009841/10000000000 : ℝ)] ![(45764247362543/100000000000000 : ℝ), (15522539723097/100000000000000 : ℝ), (19356606451083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5492210371/10000000000 : ℝ)|^1097 ≤ (45764247362543/100000000000000 : ℝ)^841
        have hw : |(5492210371/10000000000 : ℝ)|=(5492210371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2397522627/10000000000 : ℝ)|^1097 ≤ (15522539723097/100000000000000 : ℝ)^841
        have hw : |(-2397522627/10000000000 : ℝ)|=(2397522627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4831009841/10000000000 : ℝ)|^1097 ≤ (19356606451083/50000000000000 : ℝ)^841
        have hw : |(4831009841/10000000000 : ℝ)|=(4831009841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s0_2 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5492210867/10000000000 : ℝ)*x 0 + (603876207/1250000000 : ℝ)*x 1 + (-2397522217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5492210867/10000000000 : ℝ)^1097 ≤ (4576425275357/10000000000000 : ℝ)^841 := by
    have hnat : (5492210867 : ℕ)^1097*10000000000000^841 ≤ 4576425275357^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492210867 10000000000 4576425275357 10000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (603876207/1250000000 : ℝ)^1097 ≤ (38713210968401/100000000000000 : ℝ)^841 := by
    have hnat : (603876207 : ℕ)^1097*100000000000000^841 ≤ 38713210968401^841*1250000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603876207 1250000000 38713210968401 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2397522217/10000000000 : ℝ)^1097 ≤ (15522536260559/100000000000000 : ℝ)^841 := by
    have hnat : (2397522217 : ℕ)^1097*100000000000000^841 ≤ 15522536260559^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397522217 10000000000 15522536260559 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5492210867/10000000000 : ℝ), (603876207/1250000000 : ℝ), (-2397522217/10000000000 : ℝ)] ![(4576425275357/10000000000000 : ℝ), (38713210968401/100000000000000 : ℝ), (15522536260559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5492210867/10000000000 : ℝ)|^1097 ≤ (4576425275357/10000000000000 : ℝ)^841
        have hw : |(5492210867/10000000000 : ℝ)|=(5492210867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(603876207/1250000000 : ℝ)|^1097 ≤ (38713210968401/100000000000000 : ℝ)^841
        have hw : |(603876207/1250000000 : ℝ)|=(603876207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2397522217/10000000000 : ℝ)|^1097 ≤ (15522536260559/100000000000000 : ℝ)^841
        have hw : |(-2397522217/10000000000 : ℝ)|=(2397522217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s0_3 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2083072033/5000000000 : ℝ)*x 0 + (96980679/312500000 : ℝ)*x 1 + (5546155697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083072033/5000000000 : ℝ)^1097 ≤ (15957012492967/50000000000000 : ℝ)^841 := by
    have hnat : (2083072033 : ℕ)^1097*50000000000000^841 ≤ 15957012492967^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083072033 5000000000 15957012492967 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96980679/312500000 : ℝ)^1097 ≤ (10867260540589/50000000000000 : ℝ)^841 := by
    have hnat : (96980679 : ℕ)^1097*50000000000000^841 ≤ 10867260540589^841*312500000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96980679 312500000 10867260540589 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5546155697/10000000000 : ℝ)^1097 ≤ (46351453922489/100000000000000 : ℝ)^841 := by
    have hnat : (5546155697 : ℕ)^1097*100000000000000^841 ≤ 46351453922489^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5546155697 10000000000 46351453922489 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2083072033/5000000000 : ℝ), (96980679/312500000 : ℝ), (5546155697/10000000000 : ℝ)] ![(15957012492967/50000000000000 : ℝ), (10867260540589/50000000000000 : ℝ), (46351453922489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2083072033/5000000000 : ℝ)|^1097 ≤ (15957012492967/50000000000000 : ℝ)^841
        have hw : |(2083072033/5000000000 : ℝ)|=(2083072033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(96980679/312500000 : ℝ)|^1097 ≤ (10867260540589/50000000000000 : ℝ)^841
        have hw : |(96980679/312500000 : ℝ)|=(96980679/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5546155697/10000000000 : ℝ)|^1097 ≤ (46351453922489/100000000000000 : ℝ)^841
        have hw : |(5546155697/10000000000 : ℝ)|=(5546155697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s0_4 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-440850529/2500000000 : ℝ)*x 0 + (2429956551/5000000000 : ℝ)*x 1 + (2965329023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (440850529/2500000000 : ℝ)^1097 ≤ (649861915969/6250000000000 : ℝ)^841 := by
    have hnat : (440850529 : ℕ)^1097*6250000000000^841 ≤ 649861915969^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440850529 2500000000 649861915969 6250000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2429956551/5000000000 : ℝ)^1097 ≤ (39015607137501/100000000000000 : ℝ)^841 := by
    have hnat : (2429956551 : ℕ)^1097*100000000000000^841 ≤ 39015607137501^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2429956551 5000000000 39015607137501 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2965329023/5000000000 : ℝ)^1097 ≤ (50586602197197/100000000000000 : ℝ)^841 := by
    have hnat : (2965329023 : ℕ)^1097*100000000000000^841 ≤ 50586602197197^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2965329023 5000000000 50586602197197 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-440850529/2500000000 : ℝ), (2429956551/5000000000 : ℝ), (2965329023/5000000000 : ℝ)] ![(649861915969/6250000000000 : ℝ), (39015607137501/100000000000000 : ℝ), (50586602197197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-440850529/2500000000 : ℝ)|^1097 ≤ (649861915969/6250000000000 : ℝ)^841
        have hw : |(-440850529/2500000000 : ℝ)|=(440850529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2429956551/5000000000 : ℝ)|^1097 ≤ (39015607137501/100000000000000 : ℝ)^841
        have hw : |(2429956551/5000000000 : ℝ)|=(2429956551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2965329023/5000000000 : ℝ)|^1097 ≤ (50586602197197/100000000000000 : ℝ)^841
        have hw : |(2965329023/5000000000 : ℝ)|=(2965329023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s0_5 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5183906721/10000000000 : ℝ)*x 0 + (-648936877/5000000000 : ℝ)*x 1 + (148266453/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183906721/10000000000 : ℝ)^1097 ≤ (5305288089033/12500000000000 : ℝ)^841 := by
    have hnat : (5183906721 : ℕ)^1097*12500000000000^841 ≤ 5305288089033^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183906721 10000000000 5305288089033 12500000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (648936877/5000000000 : ℝ)^1097 ≤ (6971092246319/100000000000000 : ℝ)^841 := by
    have hnat : (648936877 : ℕ)^1097*100000000000000^841 ≤ 6971092246319^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648936877 5000000000 6971092246319 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (148266453/250000000 : ℝ)^1097 ≤ (50586603020529/100000000000000 : ℝ)^841 := by
    have hnat : (148266453 : ℕ)^1097*100000000000000^841 ≤ 50586603020529^841*250000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148266453 250000000 50586603020529 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183906721/10000000000 : ℝ), (-648936877/5000000000 : ℝ), (148266453/250000000 : ℝ)] ![(5305288089033/12500000000000 : ℝ), (6971092246319/100000000000000 : ℝ), (50586603020529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183906721/10000000000 : ℝ)|^1097 ≤ (5305288089033/12500000000000 : ℝ)^841
        have hw : |(5183906721/10000000000 : ℝ)|=(5183906721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-648936877/5000000000 : ℝ)|^1097 ≤ (6971092246319/100000000000000 : ℝ)^841
        have hw : |(-648936877/5000000000 : ℝ)|=(648936877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(148266453/250000000 : ℝ)|^1097 ≤ (50586603020529/100000000000000 : ℝ)^841
        have hw : |(148266453/250000000 : ℝ)|=(148266453/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s0_6 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5183906741/10000000000 : ℝ)*x 0 + (5930657959/10000000000 : ℝ)*x 1 + (-64893699/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183906741/10000000000 : ℝ)^1097 ≤ (8488460985171/20000000000000 : ℝ)^841 := by
    have hnat : (5183906741 : ℕ)^1097*20000000000000^841 ≤ 8488460985171^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183906741 10000000000 8488460985171 20000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5930657959/10000000000 : ℝ)^1097 ≤ (25293300614613/50000000000000 : ℝ)^841 := by
    have hnat : (5930657959 : ℕ)^1097*50000000000000^841 ≤ 25293300614613^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5930657959 10000000000 25293300614613 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64893699/500000000 : ℝ)^1097 ≤ (6971093829707/100000000000000 : ℝ)^841 := by
    have hnat : (64893699 : ℕ)^1097*100000000000000^841 ≤ 6971093829707^841*500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64893699 500000000 6971093829707 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183906741/10000000000 : ℝ), (5930657959/10000000000 : ℝ), (-64893699/500000000 : ℝ)] ![(8488460985171/20000000000000 : ℝ), (25293300614613/50000000000000 : ℝ), (6971093829707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183906741/10000000000 : ℝ)|^1097 ≤ (8488460985171/20000000000000 : ℝ)^841
        have hw : |(5183906741/10000000000 : ℝ)|=(5183906741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5930657959/10000000000 : ℝ)|^1097 ≤ (25293300614613/50000000000000 : ℝ)^841
        have hw : |(5930657959/10000000000 : ℝ)|=(5930657959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64893699/500000000 : ℝ)|^1097 ≤ (6971093829707/100000000000000 : ℝ)^841
        have hw : |(-64893699/500000000 : ℝ)|=(64893699/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s0_7 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2087421993/5000000000 : ℝ)*x 0 + (5483649957/10000000000 : ℝ)*x 1 + (1584059643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087421993/5000000000 : ℝ)^1097 ≤ (6400196660791/20000000000000 : ℝ)^841 := by
    have hnat : (2087421993 : ℕ)^1097*20000000000000^841 ≤ 6400196660791^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087421993 5000000000 6400196660791 20000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5483649957/10000000000 : ℝ)^1097 ≤ (45671226259389/100000000000000 : ℝ)^841 := by
    have hnat : (5483649957 : ℕ)^1097*100000000000000^841 ≤ 45671226259389^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483649957 10000000000 45671226259389 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1584059643/5000000000 : ℝ)^1097 ≤ (2790973802577/12500000000000 : ℝ)^841 := by
    have hnat : (1584059643 : ℕ)^1097*12500000000000^841 ≤ 2790973802577^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584059643 5000000000 2790973802577 12500000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2087421993/5000000000 : ℝ), (5483649957/10000000000 : ℝ), (1584059643/5000000000 : ℝ)] ![(6400196660791/20000000000000 : ℝ), (45671226259389/100000000000000 : ℝ), (2790973802577/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2087421993/5000000000 : ℝ)|^1097 ≤ (6400196660791/20000000000000 : ℝ)^841
        have hw : |(2087421993/5000000000 : ℝ)|=(2087421993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5483649957/10000000000 : ℝ)|^1097 ≤ (45671226259389/100000000000000 : ℝ)^841
        have hw : |(5483649957/10000000000 : ℝ)|=(5483649957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1584059643/5000000000 : ℝ)|^1097 ≤ (2790973802577/12500000000000 : ℝ)^841
        have hw : |(1584059643/5000000000 : ℝ)|=(1584059643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1428_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2041/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5253/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4387/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4387 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4387*1^1024 ≤ 0^1024*1^4387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4387 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4387/1024 : ℝ) ≤ (1973119996789208197/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4387 ≤ (1973119996789208197/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4387*100000000000000000000^1024 ≤ 1973119996789208197^1024*5^4387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1973119996789208197 100000000000000000000 4387 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1973119996789208197/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4387 := by
      have hnat : (1 : ℕ)^1024*1^4387 ≤ 1^4387*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101973119996789208197/100000000000000000000 : ℝ) ≤ (627856977405127/625000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (101973119996789208197/100000000000000000000 : ℝ)^1024 ≤ (627856977405127/625000000000000 : ℝ)^4387 := by
      have hnat : (101973119996789208197 : ℕ)^1024*625000000000000^4387 ≤ 627856977405127^4387*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101973119996789208197 100000000000000000000 627856977405127 625000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (627856977405127/625000000000000 : ℝ)) (X := (101973119996789208197/100000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51973119996789208197/50000000000000000000 : ℝ) ≤ (315356977405127/312500000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (51973119996789208197/50000000000000000000 : ℝ)^1024 ≤ (315356977405127/312500000000000 : ℝ)^4387 := by
      have hnat : (51973119996789208197 : ℕ)^1024*312500000000000^4387 ≤ 315356977405127^4387*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51973119996789208197 50000000000000000000 315356977405127 312500000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (315356977405127/312500000000000 : ℝ)) (X := (51973119996789208197/50000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2856977405127/250000000000000 : ℝ)*(0 : ℝ))^(4387/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2856977405127/250000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1973119996789208197/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2856977405127/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4387/1024 : ℝ) := by
    rw [show (1 : ℝ)+(2856977405127/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(627856977405127/625000000000000 : ℝ) by norm_num, show 1+(1973119996789208197/100000000000000000000 : ℝ)+(0 : ℝ)=(101973119996789208197/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1973119996789208197/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2856977405127/250000000000000 : ℝ)*(2/5 : ℝ))^(4387/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2856977405127/250000000000000 : ℝ)*(2/5 : ℝ)=(315356977405127/312500000000000 : ℝ) by norm_num, show 1+2*(1973119996789208197/100000000000000000000 : ℝ)=(51973119996789208197/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2856977405127/250000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2856977405127/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2856977405127/250000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2856977405127/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2856977405127/250000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2856977405127/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1759380129/10000000000 : ℝ)*X 0 0+(745074207/1250000000 : ℝ)*X 0 1+(1207752351/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5492210371/10000000000 : ℝ)*X 1 0+(-2397522627/10000000000 : ℝ)*X 1 1+(4831009841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5492210867/10000000000 : ℝ)*X 2 0+(603876207/1250000000 : ℝ)*X 2 1+(-2397522217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2083072033/5000000000 : ℝ)*X 0 0+(96980679/312500000 : ℝ)*X 0 1+(5546155697/10000000000 : ℝ)*X 0 2+(2083072033/5000000000 : ℝ)*X 1 0+(96980679/312500000 : ℝ)*X 1 1+(5546155697/10000000000 : ℝ)*X 1 2+(2083072033/5000000000 : ℝ)*X 2 0+(96980679/312500000 : ℝ)*X 2 1+(5546155697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-440850529/2500000000 : ℝ)*X 0 0+(2429956551/5000000000 : ℝ)*X 0 1+(2965329023/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5183906721/10000000000 : ℝ)*X 1 0+(-648936877/5000000000 : ℝ)*X 1 1+(148266453/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5183906741/10000000000 : ℝ)*X 2 0+(5930657959/10000000000 : ℝ)*X 2 1+(-64893699/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2087421993/5000000000 : ℝ)*X 0 0+(5483649957/10000000000 : ℝ)*X 0 1+(1584059643/5000000000 : ℝ)*X 0 2+(2087421993/5000000000 : ℝ)*X 1 0+(5483649957/10000000000 : ℝ)*X 1 1+(1584059643/5000000000 : ℝ)*X 1 2+(2087421993/5000000000 : ℝ)*X 2 0+(5483649957/10000000000 : ℝ)*X 2 1+(1584059643/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2685431117120729399127/1562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (6709491/1250000000000 : ℝ)*(base19) + (517608813/100000000000000 : ℝ)*(base23) + (54970063/100000000000000 : ℝ)*(upper3) + (13606993/25000000000000 : ℝ)*(upper4) + (25075797/25000000000000 : ℝ)*(upper5) + (323664542365709/50000000000000 : ℝ)*(major0) + (323664542365709/50000000000000 : ℝ)*(major1) + (323664542365709/50000000000000 : ℝ)*(major2) + (885283081061001/100000000000000 : ℝ)*(sp0) + (88528491930811/10000000000000 : ℝ)*(sp1) + (885284938458577/100000000000000 : ℝ)*(sp2) + (409371661701939/100000000000000 : ℝ)*(sp3) + (2375006389/100000000000000 : ℝ)*(sp4) + (198880861/20000000000000 : ℝ)*(sp7) + (81874531221249/20000000000000 : ℝ)*(f.failure) + (88528545606739/10000000000000 : ℝ)*(f.sum) + (27913339021293/6250000000000000000000000000 : ℝ)*base65 + (33406487047457/12500000000000000000000000000 : ℝ)*base68 + (58813714547457/12500000000000000000000000000 : ℝ)*base70 + (40085279165043/12500000000000000000000000000 : ℝ)*base71 + (737255078707/6250000000000000000000000000 : ℝ)*base74 + (58416229697457/12500000000000000000000000000 : ℝ)*base76 + (3305936052543/12500000000000000000000000000 : ℝ)*base77 + (4639001772457/12500000000000000000000000000 : ℝ)*base80 + (999673809957/6250000000000000000000000000 : ℝ)*base82 + (7710203/1000000000000000000000 : ℝ)*base89 + (7710203/1000000000000000000000 : ℝ)*base91 + (7710203/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38076684816151761707007/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1387482589/100000000000000 : ℝ)*(base19) + (1398287371/100000000000000 : ℝ)*(base23) + (75530979/50000000000000 : ℝ)*(base32) + (21196593/10000000000000 : ℝ)*(upper3) + (14626217/12500000000000 : ℝ)*(upper5) + (682897490241147/100000000000000 : ℝ)*(major0) + (682897490241147/100000000000000 : ℝ)*(major1) + (682897490241147/100000000000000 : ℝ)*(major2) + (1634882937/50000000000000 : ℝ)*(sp1) + (847712619/25000000000000 : ℝ)*(sp2) + (466964282944369/50000000000000 : ℝ)*(sp4) + (37356956345611/4000000000000 : ℝ)*(sp5) + (93392377675089/10000000000000 : ℝ)*(sp6) + (431866060455941/100000000000000 : ℝ)*(sp7) + (431866211517899/100000000000000 : ℝ)*(f.failure) + (466964282944369/50000000000000 : ℝ)*(f.sum) + (3189096064331/12500000000000000000000000000 : ℝ)*base66 + (65675701164331/25000000000000000000000000000 : ℝ)*base68 + (101935057689331/25000000000000000000000000000 : ℝ)*base70 + (186295664714331/25000000000000000000000000000 : ℝ)*base72 + (72864404298169/12500000000000000000000000000 : ℝ)*base73 + (226616634839331/25000000000000000000000000000 : ℝ)*base76 + (59785781039331/25000000000000000000000000000 : ℝ)*base78 + (27340313414331/25000000000000000000000000000 : ℝ)*base80 + (32617661235669/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1072247/5000000000000000000000 : ℝ)*base90 + (1072247/5000000000000000000000 : ℝ)*base92 + (1072247/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1428_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2041/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5253/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1428_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1428_s1_0 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1931877039/10000000000 : ℝ)*x 0 + (5605624599/10000000000 : ℝ)*x 1 + (5075396173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1931877039/10000000000 : ℝ)^1097 ≤ (366000767427/3125000000000 : ℝ)^841 := by
    have hnat : (1931877039 : ℕ)^1097*3125000000000^841 ≤ 366000767427^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931877039 10000000000 366000767427 3125000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5605624599/10000000000 : ℝ)^1097 ≤ (47000803080639/100000000000000 : ℝ)^841 := by
    have hnat : (5605624599 : ℕ)^1097*100000000000000^841 ≤ 47000803080639^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5605624599 10000000000 47000803080639 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5075396173/10000000000 : ℝ)^1097 ≤ (645112067799/1562500000000 : ℝ)^841 := by
    have hnat : (5075396173 : ℕ)^1097*1562500000000^841 ≤ 645112067799^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075396173 10000000000 645112067799 1562500000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1931877039/10000000000 : ℝ), (5605624599/10000000000 : ℝ), (5075396173/10000000000 : ℝ)] ![(366000767427/3125000000000 : ℝ), (47000803080639/100000000000000 : ℝ), (645112067799/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1931877039/10000000000 : ℝ)|^1097 ≤ (366000767427/3125000000000 : ℝ)^841
        have hw : |(-1931877039/10000000000 : ℝ)|=(1931877039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5605624599/10000000000 : ℝ)|^1097 ≤ (47000803080639/100000000000000 : ℝ)^841
        have hw : |(5605624599/10000000000 : ℝ)|=(5605624599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5075396173/10000000000 : ℝ)|^1097 ≤ (645112067799/1562500000000 : ℝ)^841
        have hw : |(5075396173/10000000000 : ℝ)|=(5075396173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s1_1 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2698455043/5000000000 : ℝ)*x 0 + (-1106429699/5000000000 : ℝ)*x 1 + (1015079503/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698455043/5000000000 : ℝ)^1097 ≤ (5591396839931/12500000000000 : ℝ)^841 := by
    have hnat : (2698455043 : ℕ)^1097*12500000000000^841 ≤ 5591396839931^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698455043 5000000000 5591396839931 12500000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1106429699/5000000000 : ℝ)^1097 ≤ (2796327736687/20000000000000 : ℝ)^841 := by
    have hnat : (1106429699 : ℕ)^1097*20000000000000^841 ≤ 2796327736687^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106429699 5000000000 2796327736687 20000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1015079503/2000000000 : ℝ)^1097 ≤ (20643593289541/50000000000000 : ℝ)^841 := by
    have hnat : (1015079503 : ℕ)^1097*50000000000000^841 ≤ 20643593289541^841*2000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015079503 2000000000 20643593289541 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698455043/5000000000 : ℝ), (-1106429699/5000000000 : ℝ), (1015079503/2000000000 : ℝ)] ![(5591396839931/12500000000000 : ℝ), (2796327736687/20000000000000 : ℝ), (20643593289541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698455043/5000000000 : ℝ)|^1097 ≤ (5591396839931/12500000000000 : ℝ)^841
        have hw : |(2698455043/5000000000 : ℝ)|=(2698455043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1106429699/5000000000 : ℝ)|^1097 ≤ (2796327736687/20000000000000 : ℝ)^841
        have hw : |(-1106429699/5000000000 : ℝ)|=(1106429699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1015079503/2000000000 : ℝ)|^1097 ≤ (20643593289541/50000000000000 : ℝ)^841
        have hw : |(1015079503/2000000000 : ℝ)|=(1015079503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s1_2 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5396911127/10000000000 : ℝ)*x 0 + (5075396349/10000000000 : ℝ)*x 1 + (-1106429767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396911127/10000000000 : ℝ)^1097 ≤ (11182796493489/25000000000000 : ℝ)^841 := by
    have hnat : (5396911127 : ℕ)^1097*25000000000000^841 ≤ 11182796493489^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396911127 10000000000 11182796493489 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5075396349/10000000000 : ℝ)^1097 ≤ (4128717420667/10000000000000 : ℝ)^841 := by
    have hnat : (5075396349 : ℕ)^1097*10000000000000^841 ≤ 4128717420667^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075396349 10000000000 4128717420667 10000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1106429767/5000000000 : ℝ)^1097 ≤ (13981639804301/100000000000000 : ℝ)^841 := by
    have hnat : (1106429767 : ℕ)^1097*100000000000000^841 ≤ 13981639804301^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106429767 5000000000 13981639804301 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396911127/10000000000 : ℝ), (5075396349/10000000000 : ℝ), (-1106429767/5000000000 : ℝ)] ![(11182796493489/25000000000000 : ℝ), (4128717420667/10000000000000 : ℝ), (13981639804301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396911127/10000000000 : ℝ)|^1097 ≤ (11182796493489/25000000000000 : ℝ)^841
        have hw : |(5396911127/10000000000 : ℝ)|=(5396911127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5075396349/10000000000 : ℝ)|^1097 ≤ (4128717420667/10000000000000 : ℝ)^841
        have hw : |(5075396349/10000000000 : ℝ)|=(5075396349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1106429767/5000000000 : ℝ)|^1097 ≤ (13981639804301/100000000000000 : ℝ)^841
        have hw : |(-1106429767/5000000000 : ℝ)|=(1106429767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s1_3 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4276820813/10000000000 : ℝ)*x 0 + (3737819829/10000000000 : ℝ)*x 1 + (1221114641/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4276820813/10000000000 : ℝ)^1097 ≤ (8256091322261/25000000000000 : ℝ)^841 := by
    have hnat : (4276820813 : ℕ)^1097*25000000000000^841 ≤ 8256091322261^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4276820813 10000000000 8256091322261 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3737819829/10000000000 : ℝ)^1097 ≤ (13851397771313/50000000000000 : ℝ)^841 := by
    have hnat : (3737819829 : ℕ)^1097*50000000000000^841 ≤ 13851397771313^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3737819829 10000000000 13851397771313 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1221114641/2500000000 : ℝ)^1097 ≤ (19636419579957/50000000000000 : ℝ)^841 := by
    have hnat : (1221114641 : ℕ)^1097*50000000000000^841 ≤ 19636419579957^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221114641 2500000000 19636419579957 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4276820813/10000000000 : ℝ), (3737819829/10000000000 : ℝ), (1221114641/2500000000 : ℝ)] ![(8256091322261/25000000000000 : ℝ), (13851397771313/50000000000000 : ℝ), (19636419579957/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4276820813/10000000000 : ℝ)|^1097 ≤ (8256091322261/25000000000000 : ℝ)^841
        have hw : |(4276820813/10000000000 : ℝ)|=(4276820813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3737819829/10000000000 : ℝ)|^1097 ≤ (13851397771313/50000000000000 : ℝ)^841
        have hw : |(3737819829/10000000000 : ℝ)|=(3737819829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1221114641/2500000000 : ℝ)|^1097 ≤ (19636419579957/50000000000000 : ℝ)^841
        have hw : |(1221114641/2500000000 : ℝ)|=(1221114641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s1_4 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-483069093/2500000000 : ℝ)*x 0 + (1270404663/2500000000 : ℝ)*x 1 + (699912069/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (483069093/2500000000 : ℝ)^1097 ≤ (11715182556667/100000000000000 : ℝ)^841 := by
    have hnat : (483069093 : ℕ)^1097*100000000000000^841 ≤ 11715182556667^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483069093 2500000000 11715182556667 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270404663/2500000000 : ℝ)^1097 ≤ (41353211306181/100000000000000 : ℝ)^841 := by
    have hnat : (1270404663 : ℕ)^1097*100000000000000^841 ≤ 41353211306181^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270404663 2500000000 41353211306181 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (699912069/1250000000 : ℝ)^1097 ≤ (46931606130683/100000000000000 : ℝ)^841 := by
    have hnat : (699912069 : ℕ)^1097*100000000000000^841 ≤ 46931606130683^841*1250000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      699912069 1250000000 46931606130683 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-483069093/2500000000 : ℝ), (1270404663/2500000000 : ℝ), (699912069/1250000000 : ℝ)] ![(11715182556667/100000000000000 : ℝ), (41353211306181/100000000000000 : ℝ), (46931606130683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-483069093/2500000000 : ℝ)|^1097 ≤ (11715182556667/100000000000000 : ℝ)^841
        have hw : |(-483069093/2500000000 : ℝ)|=(483069093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1270404663/2500000000 : ℝ)|^1097 ≤ (41353211306181/100000000000000 : ℝ)^841
        have hw : |(1270404663/2500000000 : ℝ)|=(1270404663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(699912069/1250000000 : ℝ)|^1097 ≤ (46931606130683/100000000000000 : ℝ)^841
        have hw : |(699912069/1250000000 : ℝ)|=(699912069/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s1_5 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (525838641/1000000000 : ℝ)*x 0 + (-1688959761/10000000000 : ℝ)*x 1 + (2799648283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525838641/1000000000 : ℝ)^1097 ≤ (43239446866807/100000000000000 : ℝ)^841 := by
    have hnat : (525838641 : ℕ)^1097*100000000000000^841 ≤ 43239446866807^841*1000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525838641 1000000000 43239446866807 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1688959761/10000000000 : ℝ)^1097 ≤ (1228618354099/12500000000000 : ℝ)^841 := by
    have hnat : (1688959761 : ℕ)^1097*12500000000000^841 ≤ 1228618354099^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1688959761 10000000000 1228618354099 12500000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2799648283/5000000000 : ℝ)^1097 ≤ (23465803141873/50000000000000 : ℝ)^841 := by
    have hnat : (2799648283 : ℕ)^1097*50000000000000^841 ≤ 23465803141873^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2799648283 5000000000 23465803141873 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525838641/1000000000 : ℝ), (-1688959761/10000000000 : ℝ), (2799648283/5000000000 : ℝ)] ![(43239446866807/100000000000000 : ℝ), (1228618354099/12500000000000 : ℝ), (23465803141873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525838641/1000000000 : ℝ)|^1097 ≤ (43239446866807/100000000000000 : ℝ)^841
        have hw : |(525838641/1000000000 : ℝ)|=(525838641/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1688959761/10000000000 : ℝ)|^1097 ≤ (1228618354099/12500000000000 : ℝ)^841
        have hw : |(-1688959761/10000000000 : ℝ)|=(1688959761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2799648283/5000000000 : ℝ)|^1097 ≤ (23465803141873/50000000000000 : ℝ)^841
        have hw : |(2799648283/5000000000 : ℝ)|=(2799648283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s1_6 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1314596591/2500000000 : ℝ)*x 0 + (5599296529/10000000000 : ℝ)*x 1 + (-42223997/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314596591/2500000000 : ℝ)^1097 ≤ (4323944637341/10000000000000 : ℝ)^841 := by
    have hnat : (1314596591 : ℕ)^1097*10000000000000^841 ≤ 4323944637341^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314596591 2500000000 4323944637341 10000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5599296529/10000000000 : ℝ)^1097 ≤ (23465802939611/50000000000000 : ℝ)^841 := by
    have hnat : (5599296529 : ℕ)^1097*50000000000000^841 ≤ 23465802939611^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5599296529 10000000000 23465802939611 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42223997/250000000 : ℝ)^1097 ≤ (9828947736119/100000000000000 : ℝ)^841 := by
    have hnat : (42223997 : ℕ)^1097*100000000000000^841 ≤ 9828947736119^841*250000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42223997 250000000 9828947736119 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314596591/2500000000 : ℝ), (5599296529/10000000000 : ℝ), (-42223997/250000000 : ℝ)] ![(4323944637341/10000000000000 : ℝ), (23465802939611/50000000000000 : ℝ), (9828947736119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314596591/2500000000 : ℝ)|^1097 ≤ (4323944637341/10000000000000 : ℝ)^841
        have hw : |(1314596591/2500000000 : ℝ)|=(1314596591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5599296529/10000000000 : ℝ)|^1097 ≤ (23465802939611/50000000000000 : ℝ)^841
        have hw : |(5599296529/10000000000 : ℝ)|=(5599296529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-42223997/250000000 : ℝ)|^1097 ≤ (9828947736119/100000000000000 : ℝ)^841
        have hw : |(-42223997/250000000 : ℝ)|=(42223997/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s1_7 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (213884243/500000000 : ℝ)*x 0 + (2435501629/5000000000 : ℝ)*x 1 + (3751502867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213884243/500000000 : ℝ)^1097 ≤ (4129133550641/12500000000000 : ℝ)^841 := by
    have hnat : (213884243 : ℕ)^1097*12500000000000^841 ≤ 4129133550641^841*500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213884243 500000000 4129133550641 12500000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2435501629/5000000000 : ℝ)^1097 ≤ (19565890560821/50000000000000 : ℝ)^841 := by
    have hnat : (2435501629 : ℕ)^1097*50000000000000^841 ≤ 19565890560821^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2435501629 5000000000 19565890560821 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3751502867/10000000000 : ℝ)^1097 ≤ (27835150464551/100000000000000 : ℝ)^841 := by
    have hnat : (3751502867 : ℕ)^1097*100000000000000^841 ≤ 27835150464551^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3751502867 10000000000 27835150464551 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213884243/500000000 : ℝ), (2435501629/5000000000 : ℝ), (3751502867/10000000000 : ℝ)] ![(4129133550641/12500000000000 : ℝ), (19565890560821/50000000000000 : ℝ), (27835150464551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213884243/500000000 : ℝ)|^1097 ≤ (4129133550641/12500000000000 : ℝ)^841
        have hw : |(213884243/500000000 : ℝ)|=(213884243/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2435501629/5000000000 : ℝ)|^1097 ≤ (19565890560821/50000000000000 : ℝ)^841
        have hw : |(2435501629/5000000000 : ℝ)|=(2435501629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3751502867/10000000000 : ℝ)|^1097 ≤ (27835150464551/100000000000000 : ℝ)^841
        have hw : |(3751502867/10000000000 : ℝ)|=(3751502867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1428_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5253/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2041/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (7643/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18853/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5253/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2041/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5253/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2041/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5253/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2041/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5253/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2041/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5253/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2041/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5253/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2041/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2041/100000 : ℝ) ^ (4387/1024 : ℝ) ≤ (1435501797979/25000000000000000000 : ℝ) := by
    have hpowers : (2041/100000 : ℝ)^4387 ≤ (1435501797979/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2041 : ℕ)^4387*25000000000000000000^1024 ≤ 1435501797979^1024*100000^4387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2041 100000 1435501797979 25000000000000000000 4387 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2041/100000 : ℝ)) (X := (1435501797979/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5253/20000 : ℝ) ^ (4387/1024 : ℝ) ≤ (325468133250561933/100000000000000000000 : ℝ) := by
    have hpowers : (5253/20000 : ℝ)^4387 ≤ (325468133250561933/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5253 : ℕ)^4387*100000000000000000000^1024 ≤ 325468133250561933^1024*20000^4387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5253 20000 325468133250561933 100000000000000000000 4387 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5253/20000 : ℝ)) (X := (325468133250561933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500001435501797979/12500000000000000000 : ℝ) ≤ (2500000067014077/2500000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (12500001435501797979/12500000000000000000 : ℝ)^1024 ≤ (2500000067014077/2500000000000000 : ℝ)^4387 := by
      have hnat : (12500001435501797979 : ℕ)^1024*2500000000000000^4387 ≤ 2500000067014077^4387*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500001435501797979 12500000000000000000 2500000067014077 2500000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000067014077/2500000000000000 : ℝ)) (X := (12500001435501797979/12500000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100325473875257753849/100000000000000000000 : ℝ) ≤ (1250948456420647/1250000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (100325473875257753849/100000000000000000000 : ℝ)^1024 ≤ (1250948456420647/1250000000000000 : ℝ)^4387 := by
      have hnat : (100325473875257753849 : ℕ)^1024*1250000000000000^4387 ≤ 1250948456420647^4387*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100325473875257753849 100000000000000000000 1250948456420647 1250000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250948456420647/1250000000000000 : ℝ)) (X := (100325473875257753849/100000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50325468133250561933/50000000000000000000 : ℝ) ≤ (2503793758668511/2500000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (50325468133250561933/50000000000000000000 : ℝ)^1024 ≤ (2503793758668511/2500000000000000 : ℝ)^4387 := by
      have hnat : (50325468133250561933 : ℕ)^1024*2500000000000000^4387 ≤ 2503793758668511^4387*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50325468133250561933 50000000000000000000 2503793758668511 2500000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503793758668511/2500000000000000 : ℝ)) (X := (50325468133250561933/50000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1435501797979/25000000000000000000 : ℝ) ≤ ((30276129349341150727/30280000000000000000 : ℝ)+2*(1896845827217/605600000000000 : ℝ)*(2041/100000 : ℝ))^(4387/1024 : ℝ) := by
    rw [show (30276129349341150727/30280000000000000000 : ℝ)+2*(1896845827217/605600000000000 : ℝ)*(2041/100000 : ℝ)=(2500000067014077/2500000000000000 : ℝ) by norm_num, show 1+2*(1435501797979/25000000000000000000 : ℝ)=(12500001435501797979/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(325468133250561933/100000000000000000000 : ℝ)+(1435501797979/25000000000000000000 : ℝ) ≤ ((30276129349341150727/30280000000000000000 : ℝ)+(1896845827217/605600000000000 : ℝ)*((5253/20000 : ℝ)+(2041/100000 : ℝ)))^(4387/1024 : ℝ) := by
    rw [show (30276129349341150727/30280000000000000000 : ℝ)+(1896845827217/605600000000000 : ℝ)*((5253/20000 : ℝ)+(2041/100000 : ℝ))=(1250948456420647/1250000000000000 : ℝ) by norm_num, show 1+(325468133250561933/100000000000000000000 : ℝ)+(1435501797979/25000000000000000000 : ℝ)=(100325473875257753849/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(325468133250561933/100000000000000000000 : ℝ) ≤ ((30276129349341150727/30280000000000000000 : ℝ)+2*(1896845827217/605600000000000 : ℝ)*(5253/20000 : ℝ))^(4387/1024 : ℝ) := by
    rw [show (30276129349341150727/30280000000000000000 : ℝ)+2*(1896845827217/605600000000000 : ℝ)*(5253/20000 : ℝ)=(2503793758668511/2500000000000000 : ℝ) by norm_num, show 1+2*(325468133250561933/100000000000000000000 : ℝ)=(50325468133250561933/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (30276129349341150727/30280000000000000000 : ℝ)*(X 1 0+X 2 0)+(1896845827217/605600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (2041/100000 : ℝ)) (hi := (5253/20000 : ℝ)) (c := (30276129349341150727/30280000000000000000 : ℝ)) (alpha := (1896845827217/605600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (30276129349341150727/30280000000000000000 : ℝ)*(X 0 1+X 2 1)+(1896845827217/605600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (2041/100000 : ℝ)) (hi := (5253/20000 : ℝ)) (c := (30276129349341150727/30280000000000000000 : ℝ)) (alpha := (1896845827217/605600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (30276129349341150727/30280000000000000000 : ℝ)*(X 0 2+X 1 2)+(1896845827217/605600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (2041/100000 : ℝ)) (hi := (5253/20000 : ℝ)) (c := (30276129349341150727/30280000000000000000 : ℝ)) (alpha := (1896845827217/605600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1931877039/10000000000 : ℝ)*X 0 0+(5605624599/10000000000 : ℝ)*X 0 1+(5075396173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2698455043/5000000000 : ℝ)*X 1 0+(-1106429699/5000000000 : ℝ)*X 1 1+(1015079503/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5396911127/10000000000 : ℝ)*X 2 0+(5075396349/10000000000 : ℝ)*X 2 1+(-1106429767/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4276820813/10000000000 : ℝ)*X 0 0+(3737819829/10000000000 : ℝ)*X 0 1+(1221114641/2500000000 : ℝ)*X 0 2+(4276820813/10000000000 : ℝ)*X 1 0+(3737819829/10000000000 : ℝ)*X 1 1+(1221114641/2500000000 : ℝ)*X 1 2+(4276820813/10000000000 : ℝ)*X 2 0+(3737819829/10000000000 : ℝ)*X 2 1+(1221114641/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-483069093/2500000000 : ℝ)*X 0 0+(1270404663/2500000000 : ℝ)*X 0 1+(699912069/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((525838641/1000000000 : ℝ)*X 1 0+(-1688959761/10000000000 : ℝ)*X 1 1+(2799648283/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1314596591/2500000000 : ℝ)*X 2 0+(5599296529/10000000000 : ℝ)*X 2 1+(-42223997/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((213884243/500000000 : ℝ)*X 0 0+(2435501629/5000000000 : ℝ)*X 0 1+(3751502867/10000000000 : ℝ)*X 0 2+(213884243/500000000 : ℝ)*X 1 0+(2435501629/5000000000 : ℝ)*X 1 1+(3751502867/10000000000 : ℝ)*X 1 2+(213884243/500000000 : ℝ)*X 2 0+(2435501629/5000000000 : ℝ)*X 2 1+(3751502867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7301545719614552494557544731/757000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19727891/100000000000000 : ℝ)*(base1) + (165644231/10000000000000 : ℝ)*(base19) + (2020231169/100000000000000 : ℝ)*(base23) + (46458539/25000000000000 : ℝ)*(upper3) + (204949217/100000000000000 : ℝ)*(upper5) + (689534742484517/50000000000000 : ℝ)*(major0) + (689534742484517/50000000000000 : ℝ)*(major1) + (689534742484517/50000000000000 : ℝ)*(major2) + (942997374748523/50000000000000 : ℝ)*(sp0) + (1886009736568809/100000000000000 : ℝ)*(sp1) + (37720187455599/2000000000000 : ℝ)*(sp2) + (174424103208153/20000000000000 : ℝ)*(sp3) + (3332648393/20000000000000 : ℝ)*(sp4) + (1679911481/25000000000000 : ℝ)*(sp7) + (872127255414581/100000000000000 : ℝ)*(f.failure) + (1886011393011119/100000000000000 : ℝ)*(f.sum) + (3367175060649/15140000000000000000000000000 : ℝ)*base65 + (13593139612133756141/1514000000000000000000000000000000 : ℝ)*base68 + (9978948933163756141/1514000000000000000000000000000000 : ℝ)*base70 + (11102223312005756141/1514000000000000000000000000000000 : ℝ)*base72 + (15112069789111/15140000000000000000000000000 : ℝ)*base74 + (5612118728621756141/1514000000000000000000000000000000 : ℝ)*base76 + (3157350971069756141/1514000000000000000000000000000000 : ℝ)*base78 + (16835880551557756141/1514000000000000000000000000000000 : ℝ)*base80 + (38068089838331/15140000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (29378807/5000000000000000000000 : ℝ)*base89 + (29378807/5000000000000000000000 : ℝ)*base91 + (29378807/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (518858616427328397860678073/75700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28488897/50000000000000 : ℝ)*(base1) + (180044521/12500000000000 : ℝ)*(base19) + (1415792653/100000000000000 : ℝ)*(base23) + (82980663/50000000000000 : ℝ)*(upper3) + (146161499/100000000000000 : ℝ)*(upper5) + (70623966667289/5000000000000 : ℝ)*(major0) + (70623966667289/5000000000000 : ℝ)*(major1) + (70623966667289/5000000000000 : ℝ)*(major2) + (8373703553/100000000000000 : ℝ)*(sp1) + (8082670387/100000000000000 : ℝ)*(sp2) + (965851380857229/50000000000000 : ℝ)*(sp4) + (1931692890676943/100000000000000 : ℝ)*(sp5) + (241461650784203/12500000000000 : ℝ)*(sp6) + (446627838252833/50000000000000 : ℝ)*(sp7) + (44662786674173/5000000000000 : ℝ)*(f.failure) + (241462838092083/12500000000000 : ℝ)*(f.sum) + (1090999003337/1514000000000000000000000000 : ℝ)*base65 + (893285791423519103/151400000000000000000000000000000 : ℝ)*base67 + (1796861764411919103/151400000000000000000000000000000 : ℝ)*base69 + (1103676302717919103/151400000000000000000000000000000 : ℝ)*base71 + (2160340644659/1514000000000000000000000000 : ℝ)*base73 + (1447097527258119103/151400000000000000000000000000000 : ℝ)*base75 + (1703692807432119103/151400000000000000000000000000000 : ℝ)*base77 + (1655312643413319103/151400000000000000000000000000000 : ℝ)*base79 + (4873138663697/1514000000000000000000000000 : ℝ)*base81 + (671631/250000000000000000000 : ℝ)*base89 + (671631/250000000000000000000 : ℝ)*base91 + (671631/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1428_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5253/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2041/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7643/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18853/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1428_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1428_s2_0 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-78603359/400000000 : ℝ)*x 0 + (5458400019/10000000000 : ℝ)*x 1 + (1040249409/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (78603359/400000000 : ℝ)^1097 ≤ (5987653574611/50000000000000 : ℝ)^841 := by
    have hnat : (78603359 : ℕ)^1097*50000000000000^841 ≤ 5987653574611^841*400000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78603359 400000000 5987653574611 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5458400019/10000000000 : ℝ)^1097 ≤ (22698553641129/50000000000000 : ℝ)^841 := by
    have hnat : (5458400019 : ℕ)^1097*50000000000000^841 ≤ 22698553641129^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458400019 10000000000 22698553641129 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040249409/2000000000 : ℝ)^1097 ≤ (42627585546683/100000000000000 : ℝ)^841 := by
    have hnat : (1040249409 : ℕ)^1097*100000000000000^841 ≤ 42627585546683^841*2000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040249409 2000000000 42627585546683 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-78603359/400000000 : ℝ), (5458400019/10000000000 : ℝ), (1040249409/2000000000 : ℝ)] ![(5987653574611/50000000000000 : ℝ), (22698553641129/50000000000000 : ℝ), (42627585546683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-78603359/400000000 : ℝ)|^1097 ≤ (5987653574611/50000000000000 : ℝ)^841
        have hw : |(-78603359/400000000 : ℝ)|=(78603359/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5458400019/10000000000 : ℝ)|^1097 ≤ (22698553641129/50000000000000 : ℝ)^841
        have hw : |(5458400019/10000000000 : ℝ)|=(5458400019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1040249409/2000000000 : ℝ)|^1097 ≤ (42627585546683/100000000000000 : ℝ)^841
        have hw : |(1040249409/2000000000 : ℝ)|=(1040249409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s2_1 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5360204519/10000000000 : ℝ)*x 0 + (-1048696971/5000000000 : ℝ)*x 1 + (2600623473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360204519/10000000000 : ℝ)^1097 ≤ (22167376615413/50000000000000 : ℝ)^841 := by
    have hnat : (5360204519 : ℕ)^1097*50000000000000^841 ≤ 22167376615413^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360204519 10000000000 22167376615413 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048696971/5000000000 : ℝ)^1097 ≤ (13037662267627/100000000000000 : ℝ)^841 := by
    have hnat : (1048696971 : ℕ)^1097*100000000000000^841 ≤ 13037662267627^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048696971 5000000000 13037662267627 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2600623473/5000000000 : ℝ)^1097 ≤ (21313792244167/50000000000000 : ℝ)^841 := by
    have hnat : (2600623473 : ℕ)^1097*50000000000000^841 ≤ 21313792244167^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600623473 5000000000 21313792244167 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360204519/10000000000 : ℝ), (-1048696971/5000000000 : ℝ), (2600623473/5000000000 : ℝ)] ![(22167376615413/50000000000000 : ℝ), (13037662267627/100000000000000 : ℝ), (21313792244167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360204519/10000000000 : ℝ)|^1097 ≤ (22167376615413/50000000000000 : ℝ)^841
        have hw : |(5360204519/10000000000 : ℝ)|=(5360204519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1048696971/5000000000 : ℝ)|^1097 ≤ (13037662267627/100000000000000 : ℝ)^841
        have hw : |(-1048696971/5000000000 : ℝ)|=(1048696971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2600623473/5000000000 : ℝ)|^1097 ≤ (21313792244167/50000000000000 : ℝ)^841
        have hw : |(2600623473/5000000000 : ℝ)|=(2600623473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s2_2 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2680102071/5000000000 : ℝ)*x 0 + (5201247373/10000000000 : ℝ)*x 1 + (-52434847/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680102071/5000000000 : ℝ)^1097 ≤ (11083687290861/25000000000000 : ℝ)^841 := by
    have hnat : (2680102071 : ℕ)^1097*25000000000000^841 ≤ 11083687290861^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680102071 5000000000 11083687290861 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5201247373/10000000000 : ℝ)^1097 ≤ (21313794526567/50000000000000 : ℝ)^841 := by
    have hnat : (5201247373 : ℕ)^1097*50000000000000^841 ≤ 21313794526567^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201247373 10000000000 21313794526567 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52434847/250000000 : ℝ)^1097 ≤ (814853860307/6250000000000 : ℝ)^841 := by
    have hnat : (52434847 : ℕ)^1097*6250000000000^841 ≤ 814853860307^841*250000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52434847 250000000 814853860307 6250000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680102071/5000000000 : ℝ), (5201247373/10000000000 : ℝ), (-52434847/250000000 : ℝ)] ![(11083687290861/25000000000000 : ℝ), (21313794526567/50000000000000 : ℝ), (814853860307/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680102071/5000000000 : ℝ)|^1097 ≤ (11083687290861/25000000000000 : ℝ)^841
        have hw : |(2680102071/5000000000 : ℝ)|=(2680102071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5201247373/10000000000 : ℝ)|^1097 ≤ (21313794526567/50000000000000 : ℝ)^841
        have hw : |(5201247373/10000000000 : ℝ)|=(5201247373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-52434847/250000000 : ℝ)|^1097 ≤ (814853860307/6250000000000 : ℝ)^841
        have hw : |(-52434847/250000000 : ℝ)|=(52434847/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s2_3 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4300258591/10000000000 : ℝ)*x 0 + (4030279371/10000000000 : ℝ)*x 1 + (4586383537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300258591/10000000000 : ℝ)^1097 ≤ (33260631774237/100000000000000 : ℝ)^841 := by
    have hnat : (4300258591 : ℕ)^1097*100000000000000^841 ≤ 33260631774237^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300258591 10000000000 33260631774237 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4030279371/10000000000 : ℝ)^1097 ≤ (764080943193/2500000000000 : ℝ)^841 := by
    have hnat : (4030279371 : ℕ)^1097*2500000000000^841 ≤ 764080943193^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030279371 10000000000 764080943193 2500000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4586383537/10000000000 : ℝ)^1097 ≤ (1447045219307/4000000000000 : ℝ)^841 := by
    have hnat : (4586383537 : ℕ)^1097*4000000000000^841 ≤ 1447045219307^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4586383537 10000000000 1447045219307 4000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300258591/10000000000 : ℝ), (4030279371/10000000000 : ℝ), (4586383537/10000000000 : ℝ)] ![(33260631774237/100000000000000 : ℝ), (764080943193/2500000000000 : ℝ), (1447045219307/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300258591/10000000000 : ℝ)|^1097 ≤ (33260631774237/100000000000000 : ℝ)^841
        have hw : |(4300258591/10000000000 : ℝ)|=(4300258591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4030279371/10000000000 : ℝ)|^1097 ≤ (764080943193/2500000000000 : ℝ)^841
        have hw : |(4030279371/10000000000 : ℝ)|=(4030279371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4586383537/10000000000 : ℝ)|^1097 ≤ (1447045219307/4000000000000 : ℝ)^841
        have hw : |(4586383537/10000000000 : ℝ)|=(4586383537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s2_4 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-982564879/5000000000 : ℝ)*x 0 + (5202719651/10000000000 : ℝ)*x 1 + (5456915217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (982564879/5000000000 : ℝ)^1097 ≤ (2395134216533/20000000000000 : ℝ)^841 := by
    have hnat : (982564879 : ℕ)^1097*20000000000000^841 ≤ 2395134216533^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982564879 5000000000 2395134216533 20000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5202719651/10000000000 : ℝ)^1097 ≤ (21321664484813/50000000000000 : ℝ)^841 := by
    have hnat : (5202719651 : ℕ)^1097*50000000000000^841 ≤ 21321664484813^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202719651 10000000000 21321664484813 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456915217/10000000000 : ℝ)^1097 ≤ (22690499967639/50000000000000 : ℝ)^841 := by
    have hnat : (5456915217 : ℕ)^1097*50000000000000^841 ≤ 22690499967639^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456915217 10000000000 22690499967639 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-982564879/5000000000 : ℝ), (5202719651/10000000000 : ℝ), (5456915217/10000000000 : ℝ)] ![(2395134216533/20000000000000 : ℝ), (21321664484813/50000000000000 : ℝ), (22690499967639/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-982564879/5000000000 : ℝ)|^1097 ≤ (2395134216533/20000000000000 : ℝ)^841
        have hw : |(-982564879/5000000000 : ℝ)|=(982564879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5202719651/10000000000 : ℝ)|^1097 ≤ (21321664484813/50000000000000 : ℝ)^841
        have hw : |(5202719651/10000000000 : ℝ)|=(5202719651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456915217/10000000000 : ℝ)|^1097 ≤ (22690499967639/50000000000000 : ℝ)^841
        have hw : |(5456915217/10000000000 : ℝ)|=(5456915217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s2_5 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1323335623/2500000000 : ℝ)*x 0 + (-92086271/500000000 : ℝ)*x 1 + (5456915621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323335623/2500000000 : ℝ)^1097 ≤ (21807382490607/50000000000000 : ℝ)^841 := by
    have hnat : (1323335623 : ℕ)^1097*50000000000000^841 ≤ 21807382490607^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323335623 2500000000 21807382490607 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (92086271/500000000 : ℝ)^1097 ≤ (11004230685287/100000000000000 : ℝ)^841 := by
    have hnat : (92086271 : ℕ)^1097*100000000000000^841 ≤ 11004230685287^841*500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92086271 500000000 11004230685287 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456915621/10000000000 : ℝ)^1097 ≤ (45381004317747/100000000000000 : ℝ)^841 := by
    have hnat : (5456915621 : ℕ)^1097*100000000000000^841 ≤ 45381004317747^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456915621 10000000000 45381004317747 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323335623/2500000000 : ℝ), (-92086271/500000000 : ℝ), (5456915621/10000000000 : ℝ)] ![(21807382490607/50000000000000 : ℝ), (11004230685287/100000000000000 : ℝ), (45381004317747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323335623/2500000000 : ℝ)|^1097 ≤ (21807382490607/50000000000000 : ℝ)^841
        have hw : |(1323335623/2500000000 : ℝ)|=(1323335623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-92086271/500000000 : ℝ)|^1097 ≤ (11004230685287/100000000000000 : ℝ)^841
        have hw : |(-92086271/500000000 : ℝ)|=(92086271/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456915621/10000000000 : ℝ)|^1097 ≤ (45381004317747/100000000000000 : ℝ)^841
        have hw : |(5456915621/10000000000 : ℝ)|=(5456915621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s2_6 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2646671201/5000000000 : ℝ)*x 0 + (682114449/1250000000 : ℝ)*x 1 + (-115107849/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646671201/5000000000 : ℝ)^1097 ≤ (10903691003481/25000000000000 : ℝ)^841 := by
    have hnat : (2646671201 : ℕ)^1097*25000000000000^841 ≤ 10903691003481^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646671201 5000000000 10903691003481 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682114449/1250000000 : ℝ)^1097 ≤ (11345251000791/25000000000000 : ℝ)^841 := by
    have hnat : (682114449 : ℕ)^1097*25000000000000^841 ≤ 11345251000791^841*1250000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682114449 1250000000 11345251000791 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (115107849/625000000 : ℝ)^1097 ≤ (11004231963459/100000000000000 : ℝ)^841 := by
    have hnat : (115107849 : ℕ)^1097*100000000000000^841 ≤ 11004231963459^841*625000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115107849 625000000 11004231963459 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646671201/5000000000 : ℝ), (682114449/1250000000 : ℝ), (-115107849/625000000 : ℝ)] ![(10903691003481/25000000000000 : ℝ), (11345251000791/25000000000000 : ℝ), (11004231963459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646671201/5000000000 : ℝ)|^1097 ≤ (10903691003481/25000000000000 : ℝ)^841
        have hw : |(2646671201/5000000000 : ℝ)|=(2646671201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(682114449/1250000000 : ℝ)|^1097 ≤ (11345251000791/25000000000000 : ℝ)^841
        have hw : |(682114449/1250000000 : ℝ)|=(682114449/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-115107849/625000000 : ℝ)|^1097 ≤ (11004231963459/100000000000000 : ℝ)^841
        have hw : |(-115107849/625000000 : ℝ)|=(115107849/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s2_7 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4300357391/10000000000 : ℝ)*x 0 + (916639847/2000000000 : ℝ)*x 1 + (80669799/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300357391/10000000000 : ℝ)^1097 ≤ (33261628567323/100000000000000 : ℝ)^841 := by
    have hnat : (4300357391 : ℕ)^1097*100000000000000^841 ≤ 33261628567323^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300357391 10000000000 33261628567323 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (916639847/2000000000 : ℝ)^1097 ≤ (18071685738147/50000000000000 : ℝ)^841 := by
    have hnat : (916639847 : ℕ)^1097*50000000000000^841 ≤ 18071685738147^841*2000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916639847 2000000000 18071685738147 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80669799/200000000 : ℝ)^1097 ≤ (1529749997363/5000000000000 : ℝ)^841 := by
    have hnat : (80669799 : ℕ)^1097*5000000000000^841 ≤ 1529749997363^841*200000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80669799 200000000 1529749997363 5000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300357391/10000000000 : ℝ), (916639847/2000000000 : ℝ), (80669799/200000000 : ℝ)] ![(33261628567323/100000000000000 : ℝ), (18071685738147/50000000000000 : ℝ), (1529749997363/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300357391/10000000000 : ℝ)|^1097 ≤ (33261628567323/100000000000000 : ℝ)^841
        have hw : |(4300357391/10000000000 : ℝ)|=(4300357391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(916639847/2000000000 : ℝ)|^1097 ≤ (18071685738147/50000000000000 : ℝ)^841
        have hw : |(916639847/2000000000 : ℝ)|=(916639847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80669799/200000000 : ℝ)|^1097 ≤ (1529749997363/5000000000000 : ℝ)^841
        have hw : |(80669799/200000000 : ℝ)|=(80669799/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1428_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18853/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7643/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5181/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15803/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18853/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7643/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18853/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7643/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18853/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7643/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18853/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7643/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18853/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7643/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18853/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7643/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7643/100000 : ℝ) ^ (4387/1024 : ℝ) ≤ (1643242697371871/100000000000000000000 : ℝ) := by
    have hpowers : (7643/100000 : ℝ)^4387 ≤ (1643242697371871/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7643 : ℕ)^4387*100000000000000000000^1024 ≤ 1643242697371871^1024*100000^4387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7643 100000 1643242697371871 100000000000000000000 4387 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7643/100000 : ℝ)) (X := (1643242697371871/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18853/100000 : ℝ) ^ (4387/1024 : ℝ) ≤ (78632071654297299/100000000000000000000 : ℝ) := by
    have hpowers : (18853/100000 : ℝ)^4387 ≤ (78632071654297299/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18853 : ℕ)^4387*100000000000000000000^1024 ≤ 78632071654297299^1024*100000^4387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18853 100000 78632071654297299 100000000000000000000 4387 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18853/100000 : ℝ)) (X := (78632071654297299/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001643242697371871/50000000000000000000 : ℝ) ≤ (2500019177790359/2500000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (50001643242697371871/50000000000000000000 : ℝ)^1024 ≤ (2500019177790359/2500000000000000 : ℝ)^4387 := by
      have hnat : (50001643242697371871 : ℕ)^1024*2500000000000000^4387 ≤ 2500019177790359^4387*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001643242697371871 50000000000000000000 2500019177790359 2500000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500019177790359/2500000000000000 : ℝ)) (X := (50001643242697371871/50000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10008027531435166917/10000000000000000000 : ℝ) ≤ (10001873185348991/10000000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (10008027531435166917/10000000000000000000 : ℝ)^1024 ≤ (10001873185348991/10000000000000000 : ℝ)^4387 := by
      have hnat : (10008027531435166917 : ℕ)^1024*10000000000000000^4387 ≤ 10001873185348991^4387*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10008027531435166917 10000000000000000000 10001873185348991 10000000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001873185348991/10000000000000000 : ℝ)) (X := (10008027531435166917/10000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50078632071654297299/50000000000000000000 : ℝ) ≤ (5001834829768273/5000000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (50078632071654297299/50000000000000000000 : ℝ)^1024 ≤ (5001834829768273/5000000000000000 : ℝ)^4387 := by
      have hnat : (50078632071654297299 : ℕ)^1024*5000000000000000^4387 ≤ 5001834829768273^4387*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50078632071654297299 50000000000000000000 5001834829768273 5000000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001834829768273/5000000000000000 : ℝ)) (X := (50078632071654297299/50000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1643242697371871/100000000000000000000 : ℝ) ≤ ((11207339902768873183/11210000000000000000 : ℝ)+2*(359294837511/224200000000000 : ℝ)*(7643/100000 : ℝ))^(4387/1024 : ℝ) := by
    rw [show (11207339902768873183/11210000000000000000 : ℝ)+2*(359294837511/224200000000000 : ℝ)*(7643/100000 : ℝ)=(2500019177790359/2500000000000000 : ℝ) by norm_num, show 1+2*(1643242697371871/100000000000000000000 : ℝ)=(50001643242697371871/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(78632071654297299/100000000000000000000 : ℝ)+(1643242697371871/100000000000000000000 : ℝ) ≤ ((11207339902768873183/11210000000000000000 : ℝ)+(359294837511/224200000000000 : ℝ)*((18853/100000 : ℝ)+(7643/100000 : ℝ)))^(4387/1024 : ℝ) := by
    rw [show (11207339902768873183/11210000000000000000 : ℝ)+(359294837511/224200000000000 : ℝ)*((18853/100000 : ℝ)+(7643/100000 : ℝ))=(10001873185348991/10000000000000000 : ℝ) by norm_num, show 1+(78632071654297299/100000000000000000000 : ℝ)+(1643242697371871/100000000000000000000 : ℝ)=(10008027531435166917/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(78632071654297299/100000000000000000000 : ℝ) ≤ ((11207339902768873183/11210000000000000000 : ℝ)+2*(359294837511/224200000000000 : ℝ)*(18853/100000 : ℝ))^(4387/1024 : ℝ) := by
    rw [show (11207339902768873183/11210000000000000000 : ℝ)+2*(359294837511/224200000000000 : ℝ)*(18853/100000 : ℝ)=(5001834829768273/5000000000000000 : ℝ) by norm_num, show 1+2*(78632071654297299/100000000000000000000 : ℝ)=(50078632071654297299/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11207339902768873183/11210000000000000000 : ℝ)*(X 1 0+X 2 0)+(359294837511/224200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (7643/100000 : ℝ)) (hi := (18853/100000 : ℝ)) (c := (11207339902768873183/11210000000000000000 : ℝ)) (alpha := (359294837511/224200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11207339902768873183/11210000000000000000 : ℝ)*(X 0 1+X 2 1)+(359294837511/224200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (7643/100000 : ℝ)) (hi := (18853/100000 : ℝ)) (c := (11207339902768873183/11210000000000000000 : ℝ)) (alpha := (359294837511/224200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11207339902768873183/11210000000000000000 : ℝ)*(X 0 2+X 1 2)+(359294837511/224200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (7643/100000 : ℝ)) (hi := (18853/100000 : ℝ)) (c := (11207339902768873183/11210000000000000000 : ℝ)) (alpha := (359294837511/224200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-78603359/400000000 : ℝ)*X 0 0+(5458400019/10000000000 : ℝ)*X 0 1+(1040249409/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5360204519/10000000000 : ℝ)*X 1 0+(-1048696971/5000000000 : ℝ)*X 1 1+(2600623473/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2680102071/5000000000 : ℝ)*X 2 0+(5201247373/10000000000 : ℝ)*X 2 1+(-52434847/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4300258591/10000000000 : ℝ)*X 0 0+(4030279371/10000000000 : ℝ)*X 0 1+(4586383537/10000000000 : ℝ)*X 0 2+(4300258591/10000000000 : ℝ)*X 1 0+(4030279371/10000000000 : ℝ)*X 1 1+(4586383537/10000000000 : ℝ)*X 1 2+(4300258591/10000000000 : ℝ)*X 2 0+(4030279371/10000000000 : ℝ)*X 2 1+(4586383537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-982564879/5000000000 : ℝ)*X 0 0+(5202719651/10000000000 : ℝ)*X 0 1+(5456915217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323335623/2500000000 : ℝ)*X 1 0+(-92086271/500000000 : ℝ)*X 1 1+(5456915621/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646671201/5000000000 : ℝ)*X 2 0+(682114449/1250000000 : ℝ)*X 2 1+(-115107849/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4300357391/10000000000 : ℝ)*X 0 0+(916639847/2000000000 : ℝ)*X 0 1+(80669799/200000000 : ℝ)*X 0 2+(4300357391/10000000000 : ℝ)*X 1 0+(916639847/2000000000 : ℝ)*X 1 1+(80669799/200000000 : ℝ)*X 1 2+(4300357391/10000000000 : ℝ)*X 2 0+(916639847/2000000000 : ℝ)*X 2 1+(80669799/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (143358793930061385880156857/17515625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (574983481/50000000000000 : ℝ)*(base19) + (157089499/25000000000000 : ℝ)*(base23) + (66493413/50000000000000 : ℝ)*(lower2) + (126434727/50000000000000 : ℝ)*(upper3) + (56454713/100000000000000 : ℝ)*(upper5) + (177718651383793/6250000000000 : ℝ)*(major0) + (177718651383793/6250000000000 : ℝ)*(major1) + (177718651383793/6250000000000 : ℝ)*(major2) + (1944375162657273/50000000000000 : ℝ)*(sp0) + (777751872652543/20000000000000 : ℝ)*(sp1) + (1944379942435841/50000000000000 : ℝ)*(sp2) + (1798229117942151/100000000000000 : ℝ)*(sp3) + (2546978783/25000000000000 : ℝ)*(sp4) + (6940288761/100000000000000 : ℝ)*(sp7) + (14048719204929/781250000000 : ℝ)*(f.failure) + (3888760513229677/100000000000000 : ℝ)*(f.sum) + (13935034322627/2802500000000000000000000000 : ℝ)*base65 + (266377270610451881/70062500000000000000000000000000 : ℝ)*base68 + (508800533096014381/70062500000000000000000000000000 : ℝ)*base70 + (232750731794860619/70062500000000000000000000000000 : ℝ)*base71 + (1668943193277/2802500000000000000000000000 : ℝ)*base73 + (270310457802014381/70062500000000000000000000000000 : ℝ)*base76 + (150329842445076881/70062500000000000000000000000000 : ℝ)*base78 + (1275316230965451881/70062500000000000000000000000000 : ℝ)*base80 + (12313612593199/5605000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (373163/39062500000000000000 : ℝ)*base89 + (373163/39062500000000000000 : ℝ)*base91 + (373163/39062500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (152549169225747258199050987/14012500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1296475367/100000000000000 : ℝ)*(base19) + (368533343/25000000000000 : ℝ)*(base23) + (281346677/100000000000000 : ℝ)*(upper3) + (113812797/100000000000000 : ℝ)*(lower4) + (27121/16000000000 : ℝ)*(upper5) + (143827956298163/5000000000000 : ℝ)*(major0) + (143827956298163/5000000000000 : ℝ)*(major1) + (143827956298163/5000000000000 : ℝ)*(major2) + (18249618493/100000000000000 : ℝ)*(sp1) + (2573483581/12500000000000 : ℝ)*(sp2) + (983493538173637/25000000000000 : ℝ)*(sp4) + (245872162912543/6250000000000 : ℝ)*(sp5) + (245872005668283/6250000000000 : ℝ)*(sp6) + (909571868171833/50000000000000 : ℝ)*(sp7) + (909571868171833/50000000000000 : ℝ)*(f.failure) + (983493538173637/25000000000000 : ℝ)*(f.sum) + (1279426884019/280250000000000000000000000 : ℝ)*base66 + (203341061263387171/56050000000000000000000000000000 : ℝ)*base68 + (409214693079287171/56050000000000000000000000000000 : ℝ)*base70 + (765532734954937171/56050000000000000000000000000000 : ℝ)*base72 + (630655926919/560500000000000000000000000 : ℝ)*base74 + (179621713974787171/56050000000000000000000000000000 : ℝ)*base76 + (670085633254387171/56050000000000000000000000000000 : ℝ)*base78 + (36553189168012829/56050000000000000000000000000000 : ℝ)*base79 + (1248892451241/560500000000000000000000000 : ℝ)*base82 + (22471651/2500000000000000000000 : ℝ)*base89 + (22471651/2500000000000000000000 : ℝ)*base91 + (22471651/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1428_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18853/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7643/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5181/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15803/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1428_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1428_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5181/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15803/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1428_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1428_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1428_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5181/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15803/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1428_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1408_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:48:04.445141+00:00
-- url     : https://prove2.me/submissions/b6a2ec1c-9e5d-4a86-bfa5-c2d920a75cc8

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
theorem support_rectangle_w1408_s3_0 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-496775579/2500000000 : ℝ)*x 0 + (5419461517/10000000000 : ℝ)*x 1 + (523704449/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (496775579/2500000000 : ℝ)^273 ≤ (1211493702781/10000000000000 : ℝ)^209 := by
    have hnat : (496775579 : ℕ)^273*10000000000000^209 ≤ 1211493702781^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496775579 2500000000 1211493702781 10000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419461517/10000000000 : ℝ)^273 ≤ (44925007625389/100000000000000 : ℝ)^209 := by
    have hnat : (5419461517 : ℕ)^273*100000000000000^209 ≤ 44925007625389^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419461517 10000000000 44925007625389 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523704449/1000000000 : ℝ)^273 ≤ (10740013832583/25000000000000 : ℝ)^209 := by
    have hnat : (523704449 : ℕ)^273*25000000000000^209 ≤ 10740013832583^209*1000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523704449 1000000000 10740013832583 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-496775579/2500000000 : ℝ), (5419461517/10000000000 : ℝ), (523704449/1000000000 : ℝ)] ![(1211493702781/10000000000000 : ℝ), (44925007625389/100000000000000 : ℝ), (10740013832583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-496775579/2500000000 : ℝ)|^273 ≤ (1211493702781/10000000000000 : ℝ)^209
        have hw : |(-496775579/2500000000 : ℝ)|=(496775579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419461517/10000000000 : ℝ)|^273 ≤ (44925007625389/100000000000000 : ℝ)^209
        have hw : |(5419461517/10000000000 : ℝ)|=(5419461517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523704449/1000000000 : ℝ)|^273 ≤ (10740013832583/25000000000000 : ℝ)^209
        have hw : |(523704449/1000000000 : ℝ)|=(523704449/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s3_1 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (26751879/50000000 : ℝ)*x 0 + (-104009559/500000000 : ℝ)*x 1 + (2618522209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26751879/50000000 : ℝ)^273 ≤ (276115072751/625000000000 : ℝ)^209 := by
    have hnat : (26751879 : ℕ)^273*625000000000^209 ≤ 276115072751^209*50000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26751879 50000000 276115072751 625000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104009559/500000000 : ℝ)^273 ≤ (2572306756471/20000000000000 : ℝ)^209 := by
    have hnat : (104009559 : ℕ)^273*20000000000000^209 ≤ 2572306756471^209*500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104009559 500000000 2572306756471 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2618522209/5000000000 : ℝ)^273 ≤ (42960054558847/100000000000000 : ℝ)^209 := by
    have hnat : (2618522209 : ℕ)^273*100000000000000^209 ≤ 42960054558847^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618522209 5000000000 42960054558847 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26751879/50000000 : ℝ), (-104009559/500000000 : ℝ), (2618522209/5000000000 : ℝ)] ![(276115072751/625000000000 : ℝ), (2572306756471/20000000000000 : ℝ), (42960054558847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26751879/50000000 : ℝ)|^273 ≤ (276115072751/625000000000 : ℝ)^209
        have hw : |(26751879/50000000 : ℝ)|=(26751879/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-104009559/500000000 : ℝ)|^273 ≤ (2572306756471/20000000000000 : ℝ)^209
        have hw : |(-104009559/500000000 : ℝ)|=(104009559/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2618522209/5000000000 : ℝ)|^273 ≤ (42960054558847/100000000000000 : ℝ)^209
        have hw : |(2618522209/5000000000 : ℝ)|=(2618522209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s3_2 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5350375769/10000000000 : ℝ)*x 0 + (5237044507/10000000000 : ℝ)*x 1 + (-16251493/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350375769/10000000000 : ℝ)^273 ≤ (2761150706613/6250000000000 : ℝ)^209 := by
    have hnat : (5350375769 : ℕ)^273*6250000000000^209 ≤ 2761150706613^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350375769 10000000000 2761150706613 6250000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237044507/10000000000 : ℝ)^273 ≤ (5370006939061/12500000000000 : ℝ)^209 := by
    have hnat : (5237044507 : ℕ)^273*12500000000000^209 ≤ 5370006939061^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237044507 10000000000 5370006939061 12500000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16251493/78125000 : ℝ)^273 ≤ (2572306633713/20000000000000 : ℝ)^209 := by
    have hnat : (16251493 : ℕ)^273*20000000000000^209 ≤ 2572306633713^209*78125000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16251493 78125000 2572306633713 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350375769/10000000000 : ℝ), (5237044507/10000000000 : ℝ), (-16251493/78125000 : ℝ)] ![(2761150706613/6250000000000 : ℝ), (5370006939061/12500000000000 : ℝ), (2572306633713/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350375769/10000000000 : ℝ)|^273 ≤ (2761150706613/6250000000000 : ℝ)^209
        have hw : |(5350375769/10000000000 : ℝ)|=(5350375769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237044507/10000000000 : ℝ)|^273 ≤ (5370006939061/12500000000000 : ℝ)^209
        have hw : |(5237044507/10000000000 : ℝ)|=(5237044507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16251493/78125000 : ℝ)|^273 ≤ (2572306633713/20000000000000 : ℝ)^209
        have hw : |(-16251493/78125000 : ℝ)|=(16251493/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s3_3 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1077230899/2500000000 : ℝ)*x 0 + (1029290673/2500000000 : ℝ)*x 1 + (901751481/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077230899/2500000000 : ℝ)^273 ≤ (6659400985243/20000000000000 : ℝ)^209 := by
    have hnat : (1077230899 : ℕ)^273*20000000000000^209 ≤ 6659400985243^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077230899 2500000000 6659400985243 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029290673/2500000000 : ℝ)^273 ≤ (3137474467151/10000000000000 : ℝ)^209 := by
    have hnat : (1029290673 : ℕ)^273*10000000000000^209 ≤ 3137474467151^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029290673 2500000000 3137474467151 10000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901751481/2000000000 : ℝ)^273 ≤ (276001956167/781250000000 : ℝ)^209 := by
    have hnat : (901751481 : ℕ)^273*781250000000^209 ≤ 276001956167^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901751481 2000000000 276001956167 781250000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077230899/2500000000 : ℝ), (1029290673/2500000000 : ℝ), (901751481/2000000000 : ℝ)] ![(6659400985243/20000000000000 : ℝ), (3137474467151/10000000000000 : ℝ), (276001956167/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077230899/2500000000 : ℝ)|^273 ≤ (6659400985243/20000000000000 : ℝ)^209
        have hw : |(1077230899/2500000000 : ℝ)|=(1077230899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1029290673/2500000000 : ℝ)|^273 ≤ (3137474467151/10000000000000 : ℝ)^209
        have hw : |(1029290673/2500000000 : ℝ)|=(1029290673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901751481/2000000000 : ℝ)|^273 ≤ (276001956167/781250000000 : ℝ)^209
        have hw : |(901751481/2000000000 : ℝ)|=(901751481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s3_4 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-993559399/5000000000 : ℝ)*x 0 + (523777939/1000000000 : ℝ)*x 1 + (5418722129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (993559399/5000000000 : ℝ)^273 ≤ (6057534143203/50000000000000 : ℝ)^209 := by
    have hnat : (993559399 : ℕ)^273*50000000000000^209 ≤ 6057534143203^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993559399 5000000000 6057534143203 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523777939/1000000000 : ℝ)^273 ≤ (42967930002953/100000000000000 : ℝ)^209 := by
    have hnat : (523777939 : ℕ)^273*100000000000000^209 ≤ 42967930002953^209*1000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523777939 1000000000 42967930002953 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418722129/10000000000 : ℝ)^273 ≤ (44917001696853/100000000000000 : ℝ)^209 := by
    have hnat : (5418722129 : ℕ)^273*100000000000000^209 ≤ 44917001696853^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418722129 10000000000 44917001696853 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-993559399/5000000000 : ℝ), (523777939/1000000000 : ℝ), (5418722129/10000000000 : ℝ)] ![(6057534143203/50000000000000 : ℝ), (42967930002953/100000000000000 : ℝ), (44917001696853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-993559399/5000000000 : ℝ)|^273 ≤ (6057534143203/50000000000000 : ℝ)^209
        have hw : |(-993559399/5000000000 : ℝ)|=(993559399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523777939/1000000000 : ℝ)|^273 ≤ (42967930002953/100000000000000 : ℝ)^209
        have hw : |(523777939/1000000000 : ℝ)|=(523777939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418722129/10000000000 : ℝ)|^273 ≤ (44917001696853/100000000000000 : ℝ)^209
        have hw : |(5418722129/10000000000 : ℝ)|=(5418722129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s3_5 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5303052319/10000000000 : ℝ)*x 0 + (-237314117/1250000000 : ℝ)*x 1 + (2709361221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303052319/10000000000 : ℝ)^273 ≤ (43668694653777/100000000000000 : ℝ)^209 := by
    have hnat : (5303052319 : ℕ)^273*100000000000000^209 ≤ 43668694653777^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303052319 10000000000 43668694653777 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (237314117/1250000000 : ℝ)^273 ≤ (2853575061167/25000000000000 : ℝ)^209 := by
    have hnat : (237314117 : ℕ)^273*25000000000000^209 ≤ 2853575061167^209*1250000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237314117 1250000000 2853575061167 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709361221/5000000000 : ℝ)^273 ≤ (11229251271469/25000000000000 : ℝ)^209 := by
    have hnat : (2709361221 : ℕ)^273*25000000000000^209 ≤ 11229251271469^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709361221 5000000000 11229251271469 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303052319/10000000000 : ℝ), (-237314117/1250000000 : ℝ), (2709361221/5000000000 : ℝ)] ![(43668694653777/100000000000000 : ℝ), (2853575061167/25000000000000 : ℝ), (11229251271469/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303052319/10000000000 : ℝ)|^273 ≤ (43668694653777/100000000000000 : ℝ)^209
        have hw : |(5303052319/10000000000 : ℝ)|=(5303052319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-237314117/1250000000 : ℝ)|^273 ≤ (2853575061167/25000000000000 : ℝ)^209
        have hw : |(-237314117/1250000000 : ℝ)|=(237314117/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709361221/5000000000 : ℝ)|^273 ≤ (11229251271469/25000000000000 : ℝ)^209
        have hw : |(2709361221/5000000000 : ℝ)|=(2709361221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s3_6 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1325763281/2500000000 : ℝ)*x 0 + (2709360899/5000000000 : ℝ)*x 1 + (-949256361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325763281/2500000000 : ℝ)^273 ≤ (21834351656277/50000000000000 : ℝ)^209 := by
    have hnat : (1325763281 : ℕ)^273*50000000000000^209 ≤ 21834351656277^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325763281 2500000000 21834351656277 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709360899/5000000000 : ℝ)^273 ≤ (44916998112933/100000000000000 : ℝ)^209 := by
    have hnat : (2709360899 : ℕ)^273*100000000000000^209 ≤ 44916998112933^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709360899 5000000000 44916998112933 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (949256361/5000000000 : ℝ)^273 ≤ (5707149282031/50000000000000 : ℝ)^209 := by
    have hnat : (949256361 : ℕ)^273*50000000000000^209 ≤ 5707149282031^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949256361 5000000000 5707149282031 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325763281/2500000000 : ℝ), (2709360899/5000000000 : ℝ), (-949256361/5000000000 : ℝ)] ![(21834351656277/50000000000000 : ℝ), (44916998112933/100000000000000 : ℝ), (5707149282031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325763281/2500000000 : ℝ)|^273 ≤ (21834351656277/50000000000000 : ℝ)^209
        have hw : |(1325763281/2500000000 : ℝ)|=(1325763281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709360899/5000000000 : ℝ)|^273 ≤ (44916998112933/100000000000000 : ℝ)^209
        have hw : |(2709360899/5000000000 : ℝ)|=(2709360899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-949256361/5000000000 : ℝ)|^273 ≤ (5707149282031/50000000000000 : ℝ)^209
        have hw : |(-949256361/5000000000 : ℝ)|=(949256361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s3_7 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (172358369/400000000 : ℝ)*x 0 + (9014359/20000000 : ℝ)*x 1 + (823749761/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172358369/400000000 : ℝ)^273 ≤ (665947291141/2000000000000 : ℝ)^209 := by
    have hnat : (172358369 : ℕ)^273*2000000000000^209 ≤ 665947291141^209*400000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172358369 400000000 665947291141 2000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9014359/20000000 : ℝ)^273 ≤ (8828025407149/25000000000000 : ℝ)^209 := by
    have hnat : (9014359 : ℕ)^273*25000000000000^209 ≤ 8828025407149^209*20000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9014359 20000000 8828025407149 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (823749761/2000000000 : ℝ)^273 ≤ (6278106760813/20000000000000 : ℝ)^209 := by
    have hnat : (823749761 : ℕ)^273*20000000000000^209 ≤ 6278106760813^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823749761 2000000000 6278106760813 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172358369/400000000 : ℝ), (9014359/20000000 : ℝ), (823749761/2000000000 : ℝ)] ![(665947291141/2000000000000 : ℝ), (8828025407149/25000000000000 : ℝ), (6278106760813/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172358369/400000000 : ℝ)|^273 ≤ (665947291141/2000000000000 : ℝ)^209
        have hw : |(172358369/400000000 : ℝ)|=(172358369/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9014359/20000000 : ℝ)|^273 ≤ (8828025407149/25000000000000 : ℝ)^209
        have hw : |(9014359/20000000 : ℝ)|=(9014359/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(823749761/2000000000 : ℝ)|^273 ≤ (6278106760813/20000000000000 : ℝ)^209
        have hw : |(823749761/2000000000 : ℝ)|=(823749761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s3_8 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2097373/1000000000 : ℝ)*x 0 + (1429475859/2500000000 : ℝ)*x 1 + (3021152411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097373/1000000000 : ℝ)^273 ≤ (31733570627/100000000000000 : ℝ)^209 := by
    have hnat : (2097373 : ℕ)^273*100000000000000^209 ≤ 31733570627^209*1000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097373 1000000000 31733570627 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1429475859/2500000000 : ℝ)^273 ≤ (301146533829/625000000000 : ℝ)^209 := by
    have hnat : (1429475859 : ℕ)^273*625000000000^209 ≤ 301146533829^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1429475859 2500000000 301146533829 625000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3021152411/5000000000 : ℝ)^273 ≤ (25892410501249/50000000000000 : ℝ)^209 := by
    have hnat : (3021152411 : ℕ)^273*50000000000000^209 ≤ 25892410501249^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3021152411 5000000000 25892410501249 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2097373/1000000000 : ℝ), (1429475859/2500000000 : ℝ), (3021152411/5000000000 : ℝ)] ![(31733570627/100000000000000 : ℝ), (301146533829/625000000000 : ℝ), (25892410501249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2097373/1000000000 : ℝ)|^273 ≤ (31733570627/100000000000000 : ℝ)^209
        have hw : |(-2097373/1000000000 : ℝ)|=(2097373/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1429475859/2500000000 : ℝ)|^273 ≤ (301146533829/625000000000 : ℝ)^209
        have hw : |(1429475859/2500000000 : ℝ)|=(1429475859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3021152411/5000000000 : ℝ)|^273 ≤ (25892410501249/50000000000000 : ℝ)^209
        have hw : |(3021152411/5000000000 : ℝ)|=(3021152411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s3_9 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1040443501/10000000000 : ℝ)*x 0 + (-837792891/2000000000 : ℝ)*x 1 + (6995574189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040443501/10000000000 : ℝ)^273 ≤ (5203206442931/100000000000000 : ℝ)^209 := by
    have hnat : (1040443501 : ℕ)^273*100000000000000^209 ≤ 5203206442931^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040443501 10000000000 5203206442931 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (837792891/2000000000 : ℝ)^273 ≤ (16045680838209/50000000000000 : ℝ)^209 := by
    have hnat : (837792891 : ℕ)^273*50000000000000^209 ≤ 16045680838209^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837792891 2000000000 16045680838209 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6995574189/10000000000 : ℝ)^273 ≤ (31352715927889/50000000000000 : ℝ)^209 := by
    have hnat : (6995574189 : ℕ)^273*50000000000000^209 ≤ 31352715927889^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6995574189 10000000000 31352715927889 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040443501/10000000000 : ℝ), (-837792891/2000000000 : ℝ), (6995574189/10000000000 : ℝ)] ![(5203206442931/100000000000000 : ℝ), (16045680838209/50000000000000 : ℝ), (31352715927889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040443501/10000000000 : ℝ)|^273 ≤ (5203206442931/100000000000000 : ℝ)^209
        have hw : |(1040443501/10000000000 : ℝ)|=(1040443501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-837792891/2000000000 : ℝ)|^273 ≤ (16045680838209/50000000000000 : ℝ)^209
        have hw : |(-837792891/2000000000 : ℝ)|=(837792891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6995574189/10000000000 : ℝ)|^273 ≤ (31352715927889/50000000000000 : ℝ)^209
        have hw : |(6995574189/10000000000 : ℝ)|=(6995574189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s3_10 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1040451783/10000000000 : ℝ)*x 0 + (6995592439/10000000000 : ℝ)*x 1 + (-130904303/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040451783/10000000000 : ℝ)^273 ≤ (2601630271927/50000000000000 : ℝ)^209 := by
    have hnat : (1040451783 : ℕ)^273*50000000000000^209 ≤ 2601630271927^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040451783 10000000000 2601630271927 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6995592439/10000000000 : ℝ)^273 ≤ (31352822767231/50000000000000 : ℝ)^209 := by
    have hnat : (6995592439 : ℕ)^273*50000000000000^209 ≤ 31352822767231^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6995592439 10000000000 31352822767231 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130904303/312500000 : ℝ)^273 ≤ (32091093903109/100000000000000 : ℝ)^209 := by
    have hnat : (130904303 : ℕ)^273*100000000000000^209 ≤ 32091093903109^209*312500000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130904303 312500000 32091093903109 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040451783/10000000000 : ℝ), (6995592439/10000000000 : ℝ), (-130904303/312500000 : ℝ)] ![(2601630271927/50000000000000 : ℝ), (31352822767231/50000000000000 : ℝ), (32091093903109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040451783/10000000000 : ℝ)|^273 ≤ (2601630271927/50000000000000 : ℝ)^209
        have hw : |(1040451783/10000000000 : ℝ)|=(1040451783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6995592439/10000000000 : ℝ)|^273 ≤ (31352822767231/50000000000000 : ℝ)^209
        have hw : |(6995592439/10000000000 : ℝ)|=(6995592439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-130904303/312500000 : ℝ)|^273 ≤ (32091093903109/100000000000000 : ℝ)^209
        have hw : |(-130904303/312500000 : ℝ)|=(130904303/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s3_11 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (368392089/2500000000 : ℝ)*x 0 + (2830348441/5000000000 : ℝ)*x 1 + (2678379031/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (368392089/2500000000 : ℝ)^273 ≤ (8198012125977/100000000000000 : ℝ)^209 := by
    have hnat : (368392089 : ℕ)^273*100000000000000^209 ≤ 8198012125977^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368392089 2500000000 8198012125977 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2830348441/5000000000 : ℝ)^273 ≤ (9510945493443/20000000000000 : ℝ)^209 := by
    have hnat : (2830348441 : ℕ)^273*20000000000000^209 ≤ 9510945493443^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2830348441 5000000000 9510945493443 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2678379031/5000000000 : ℝ)^273 ≤ (22123630197479/50000000000000 : ℝ)^209 := by
    have hnat : (2678379031 : ℕ)^273*50000000000000^209 ≤ 22123630197479^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678379031 5000000000 22123630197479 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(368392089/2500000000 : ℝ), (2830348441/5000000000 : ℝ), (2678379031/5000000000 : ℝ)] ![(8198012125977/100000000000000 : ℝ), (9510945493443/20000000000000 : ℝ), (22123630197479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(368392089/2500000000 : ℝ)|^273 ≤ (8198012125977/100000000000000 : ℝ)^209
        have hw : |(368392089/2500000000 : ℝ)|=(368392089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2830348441/5000000000 : ℝ)|^273 ≤ (9510945493443/20000000000000 : ℝ)^209
        have hw : |(2830348441/5000000000 : ℝ)|=(2830348441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2678379031/5000000000 : ℝ)|^273 ≤ (22123630197479/50000000000000 : ℝ)^209
        have hw : |(2678379031/5000000000 : ℝ)|=(2678379031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1408_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7933/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2563/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1387/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7479/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7933/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2563/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7933/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2563/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7933/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2563/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7933/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2563/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7933/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2563/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7933/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2563/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2563/25000 : ℝ) ^ (4367/1024 : ℝ) ≤ (6045697747569659/100000000000000000000 : ℝ) := by
    have hpowers : (2563/25000 : ℝ)^4367 ≤ (6045697747569659/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2563 : ℕ)^4367*100000000000000000000^1024 ≤ 6045697747569659^1024*25000^4367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2563 25000 6045697747569659 100000000000000000000 4367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2563/25000 : ℝ)) (X := (6045697747569659/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7933/50000 : ℝ) ^ (4367/1024 : ℝ) ≤ (38929135523264697/100000000000000000000 : ℝ) := by
    have hpowers : (7933/50000 : ℝ)^4367 ≤ (38929135523264697/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7933 : ℕ)^4367*100000000000000000000^1024 ≤ 38929135523264697^1024*50000^4367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7933 50000 38929135523264697 100000000000000000000 4367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7933/50000 : ℝ)) (X := (38929135523264697/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006045697747569659/50000000000000000000 : ℝ) ≤ (10000283513075329/10000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (50006045697747569659/50000000000000000000 : ℝ)^1024 ≤ (10000283513075329/10000000000000000 : ℝ)^4367 := by
      have hnat : (50006045697747569659 : ℕ)^1024*10000000000000000^4367 ≤ 10000283513075329^4367*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006045697747569659 50000000000000000000 10000283513075329 10000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283513075329/10000000000000000 : ℝ)) (X := (50006045697747569659/50000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011243708317708589/25000000000000000000 : ℝ) ≤ (5000527207503917/5000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (25011243708317708589/25000000000000000000 : ℝ)^1024 ≤ (5000527207503917/5000000000000000 : ℝ)^4367 := by
      have hnat : (25011243708317708589 : ℕ)^1024*5000000000000000^4367 ≤ 5000527207503917^4367*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011243708317708589 25000000000000000000 5000527207503917 5000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000527207503917/5000000000000000 : ℝ)) (X := (25011243708317708589/25000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038929135523264697/50000000000000000000 : ℝ) ≤ (10001825316940339/10000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (50038929135523264697/50000000000000000000 : ℝ)^1024 ≤ (10001825316940339/10000000000000000 : ℝ)^4367 := by
      have hnat : (50038929135523264697 : ℕ)^1024*10000000000000000^4367 ≤ 10001825316940339^4367*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038929135523264697 50000000000000000000 10001825316940339 10000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001825316940339/10000000000000000 : ℝ)) (X := (50038929135523264697/50000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6045697747569659/100000000000000000000 : ℝ) ≤ ((28062892534590407243/28070000000000000000 : ℝ)+2*(154180386501/112280000000000 : ℝ)*(2563/25000 : ℝ))^(4367/1024 : ℝ) := by
    rw [show (28062892534590407243/28070000000000000000 : ℝ)+2*(154180386501/112280000000000 : ℝ)*(2563/25000 : ℝ)=(10000283513075329/10000000000000000 : ℝ) by norm_num, show 1+2*(6045697747569659/100000000000000000000 : ℝ)=(50006045697747569659/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38929135523264697/100000000000000000000 : ℝ)+(6045697747569659/100000000000000000000 : ℝ) ≤ ((28062892534590407243/28070000000000000000 : ℝ)+(154180386501/112280000000000 : ℝ)*((7933/50000 : ℝ)+(2563/25000 : ℝ)))^(4367/1024 : ℝ) := by
    rw [show (28062892534590407243/28070000000000000000 : ℝ)+(154180386501/112280000000000 : ℝ)*((7933/50000 : ℝ)+(2563/25000 : ℝ))=(5000527207503917/5000000000000000 : ℝ) by norm_num, show 1+(38929135523264697/100000000000000000000 : ℝ)+(6045697747569659/100000000000000000000 : ℝ)=(25011243708317708589/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38929135523264697/100000000000000000000 : ℝ) ≤ ((28062892534590407243/28070000000000000000 : ℝ)+2*(154180386501/112280000000000 : ℝ)*(7933/50000 : ℝ))^(4367/1024 : ℝ) := by
    rw [show (28062892534590407243/28070000000000000000 : ℝ)+2*(154180386501/112280000000000 : ℝ)*(7933/50000 : ℝ)=(10001825316940339/10000000000000000 : ℝ) by norm_num, show 1+2*(38929135523264697/100000000000000000000 : ℝ)=(50038929135523264697/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28062892534590407243/28070000000000000000 : ℝ)*(X 1 0+X 2 0)+(154180386501/112280000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (2563/25000 : ℝ)) (hi := (7933/50000 : ℝ)) (c := (28062892534590407243/28070000000000000000 : ℝ)) (alpha := (154180386501/112280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28062892534590407243/28070000000000000000 : ℝ)*(X 0 1+X 2 1)+(154180386501/112280000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (2563/25000 : ℝ)) (hi := (7933/50000 : ℝ)) (c := (28062892534590407243/28070000000000000000 : ℝ)) (alpha := (154180386501/112280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28062892534590407243/28070000000000000000 : ℝ)*(X 0 2+X 1 2)+(154180386501/112280000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (2563/25000 : ℝ)) (hi := (7933/50000 : ℝ)) (c := (28062892534590407243/28070000000000000000 : ℝ)) (alpha := (154180386501/112280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-496775579/2500000000 : ℝ)*X 0 0+(5419461517/10000000000 : ℝ)*X 0 1+(523704449/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((26751879/50000000 : ℝ)*X 1 0+(-104009559/500000000 : ℝ)*X 1 1+(2618522209/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350375769/10000000000 : ℝ)*X 2 0+(5237044507/10000000000 : ℝ)*X 2 1+(-16251493/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1077230899/2500000000 : ℝ)*X 0 0+(1029290673/2500000000 : ℝ)*X 0 1+(901751481/2000000000 : ℝ)*X 0 2+(1077230899/2500000000 : ℝ)*X 1 0+(1029290673/2500000000 : ℝ)*X 1 1+(901751481/2000000000 : ℝ)*X 1 2+(1077230899/2500000000 : ℝ)*X 2 0+(1029290673/2500000000 : ℝ)*X 2 1+(901751481/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-993559399/5000000000 : ℝ)*X 0 0+(523777939/1000000000 : ℝ)*X 0 1+(5418722129/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303052319/10000000000 : ℝ)*X 1 0+(-237314117/1250000000 : ℝ)*X 1 1+(2709361221/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325763281/2500000000 : ℝ)*X 2 0+(2709360899/5000000000 : ℝ)*X 2 1+(-949256361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((172358369/400000000 : ℝ)*X 0 0+(9014359/20000000 : ℝ)*X 0 1+(823749761/2000000000 : ℝ)*X 0 2+(172358369/400000000 : ℝ)*X 1 0+(9014359/20000000 : ℝ)*X 1 1+(823749761/2000000000 : ℝ)*X 1 2+(172358369/400000000 : ℝ)*X 2 0+(9014359/20000000 : ℝ)*X 2 1+(823749761/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2097373/1000000000 : ℝ)*X 0 0+(1429475859/2500000000 : ℝ)*X 0 1+(3021152411/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1040443501/10000000000 : ℝ)*X 1 0+(-837792891/2000000000 : ℝ)*X 1 1+(6995574189/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1040451783/10000000000 : ℝ)*X 2 0+(6995592439/10000000000 : ℝ)*X 2 1+(-130904303/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((368392089/2500000000 : ℝ)*X 0 0+(2830348441/5000000000 : ℝ)*X 0 1+(2678379031/5000000000 : ℝ)*X 0 2+(368392089/2500000000 : ℝ)*X 1 0+(2830348441/5000000000 : ℝ)*X 1 1+(2678379031/5000000000 : ℝ)*X 1 2+(368392089/2500000000 : ℝ)*X 2 0+(2830348441/5000000000 : ℝ)*X 2 1+(2678379031/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s3_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3905642967198278730477329607/350875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7527851/100000000000000 : ℝ)*(lower5) + (1004451494281339/25000000000000 : ℝ)*(major0) + (1004451494281339/25000000000000 : ℝ)*(major1) + (1004451494281339/25000000000000 : ℝ)*(major2) + (2740973728234023/50000000000000 : ℝ)*(sp0) + (342621597345189/6250000000000 : ℝ)*(sp1) + (1096389650484929/20000000000000 : ℝ)*(sp2) + (255366144720971/10000000000000 : ℝ)*(sp3) + (559574223/20000000000000 : ℝ)*(sp5) + (112917149/100000000000000 : ℝ)*(sp6) + (1539099931/100000000000000 : ℝ)*(sp8) + (320086919/50000000000000 : ℝ)*(sp9) + (630226183/100000000000000 : ℝ)*(sp10) + (228086923/20000000000000 : ℝ)*(sp11) + (102146503505773/4000000000000 : ℝ)*(f.failure) + (5481948995567977/100000000000000 : ℝ)*(f.sum) + (346450013803/140350000000000000000000000 : ℝ)*base66 + (7514701261951088377/701750000000000000000000000000000 : ℝ)*base67 + (7058357409556588377/701750000000000000000000000000000 : ℝ)*base69 + (6541364626044838377/701750000000000000000000000000000 : ℝ)*base71 + (19403567628411/1403500000000000000000000000 : ℝ)*base74 + (7606370530418088377/701750000000000000000000000000000 : ℝ)*base75 + (5007287865312588377/701750000000000000000000000000000 : ℝ)*base77 + (13137002574278088377/701750000000000000000000000000000 : ℝ)*base79 + (182828765981/28070000000000000000000000 : ℝ)*base82 + (668601/400000000000000000000 : ℝ)*base89 + (668601/400000000000000000000 : ℝ)*base91 + (668601/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (136922440390484140053097713/87718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (149220469/100000000000000 : ℝ)*(lower5) + (253158511414903/6250000000000 : ℝ)*(major0) + (253158511414903/6250000000000 : ℝ)*(major1) + (253158511414903/6250000000000 : ℝ)*(major2) + (3416059/2500000000000 : ℝ)*(sp0) + (1199874441/25000000000000 : ℝ)*(sp1) + (2763302308709831/50000000000000 : ℝ)*(sp4) + (5526601783923191/100000000000000 : ℝ)*(sp5) + (1381651398248717/25000000000000 : ℝ)*(sp6) + (2574463930426951/100000000000000 : ℝ)*(sp7) + (2100076867/100000000000000 : ℝ)*(sp8) + (270717933/100000000000000 : ℝ)*(sp9) + (1261144021/100000000000000 : ℝ)*(sp10) + (305736039/20000000000000 : ℝ)*(sp11) + (1287232729553573/50000000000000 : ℝ)*(f.failure) + (5526606854138889/100000000000000 : ℝ)*(f.sum) + (746590372881/2807000000000000000000000000 : ℝ)*base65 + (166290061878282571/175437500000000000000000000000000 : ℝ)*base68 + (519283875828595071/175437500000000000000000000000000 : ℝ)*base70 + (7027712491991404929/175437500000000000000000000000000 : ℝ)*base71 + (15585372758729/2807000000000000000000000000 : ℝ)*base74 + (1465367643004342429/175437500000000000000000000000000 : ℝ)*base75 + (899950349866967429/175437500000000000000000000000000 : ℝ)*base77 + (1722900135696904929/175437500000000000000000000000000 : ℝ)*base79 + (3405288467493/2807000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1437201/5000000000000000000000 : ℝ)*base89 + (1437201/5000000000000000000000 : ℝ)*base91 + (1437201/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1408_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7933/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2563/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1387/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7479/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1408_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1408_s4_0 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-62128627/312500000 : ℝ)*x 0 + (5410899183/10000000000 : ℝ)*x 1 + (5244939649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (62128627/312500000 : ℝ)^273 ≤ (12123010887927/100000000000000 : ℝ)^209 := by
    have hnat : (62128627 : ℕ)^273*100000000000000^209 ≤ 12123010887927^209*312500000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62128627 312500000 12123010887927 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410899183/10000000000 : ℝ)^273 ≤ (44832317079351/100000000000000 : ℝ)^209 := by
    have hnat : (5410899183 : ℕ)^273*100000000000000^209 ≤ 44832317079351^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410899183 10000000000 44832317079351 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244939649/10000000000 : ℝ)^273 ≤ (10761168003913/25000000000000 : ℝ)^209 := by
    have hnat : (5244939649 : ℕ)^273*25000000000000^209 ≤ 10761168003913^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244939649 10000000000 10761168003913 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-62128627/312500000 : ℝ), (5410899183/10000000000 : ℝ), (5244939649/10000000000 : ℝ)] ![(12123010887927/100000000000000 : ℝ), (44832317079351/100000000000000 : ℝ), (10761168003913/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-62128627/312500000 : ℝ)|^273 ≤ (12123010887927/100000000000000 : ℝ)^209
        have hw : |(-62128627/312500000 : ℝ)|=(62128627/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410899183/10000000000 : ℝ)|^273 ≤ (44832317079351/100000000000000 : ℝ)^209
        have hw : |(5410899183/10000000000 : ℝ)|=(5410899183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244939649/10000000000 : ℝ)|^273 ≤ (10761168003913/25000000000000 : ℝ)^209
        have hw : |(5244939649/10000000000 : ℝ)|=(5244939649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s4_1 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5348171473/10000000000 : ℝ)*x 0 + (-41453053/200000000 : ℝ)*x 1 + (65561751/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348171473/10000000000 : ℝ)^273 ≤ (11038659566953/25000000000000 : ℝ)^209 := by
    have hnat : (5348171473 : ℕ)^273*25000000000000^209 ≤ 11038659566953^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348171473 10000000000 11038659566953 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41453053/200000000 : ℝ)^273 ≤ (12800685083417/100000000000000 : ℝ)^209 := by
    have hnat : (41453053 : ℕ)^273*100000000000000^209 ≤ 12800685083417^209*200000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41453053 200000000 12800685083417 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65561751/125000000 : ℝ)^273 ≤ (43044676635977/100000000000000 : ℝ)^209 := by
    have hnat : (65561751 : ℕ)^273*100000000000000^209 ≤ 43044676635977^209*125000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65561751 125000000 43044676635977 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348171473/10000000000 : ℝ), (-41453053/200000000 : ℝ), (65561751/125000000 : ℝ)] ![(11038659566953/25000000000000 : ℝ), (12800685083417/100000000000000 : ℝ), (43044676635977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348171473/10000000000 : ℝ)|^273 ≤ (11038659566953/25000000000000 : ℝ)^209
        have hw : |(5348171473/10000000000 : ℝ)|=(5348171473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41453053/200000000 : ℝ)|^273 ≤ (12800685083417/100000000000000 : ℝ)^209
        have hw : |(-41453053/200000000 : ℝ)|=(41453053/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65561751/125000000 : ℝ)|^273 ≤ (43044676635977/100000000000000 : ℝ)^209
        have hw : |(65561751/125000000 : ℝ)|=(65561751/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s4_2 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (668521449/1250000000 : ℝ)*x 0 + (5244939611/10000000000 : ℝ)*x 1 + (-2072653113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668521449/1250000000 : ℝ)^273 ≤ (4415463955113/10000000000000 : ℝ)^209 := by
    have hnat : (668521449 : ℕ)^273*10000000000000^209 ≤ 4415463955113^209*1250000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668521449 1250000000 4415463955113 10000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244939611/10000000000 : ℝ)^273 ≤ (43044671608291/100000000000000 : ℝ)^209 := by
    have hnat : (5244939611 : ℕ)^273*100000000000000^209 ≤ 43044671608291^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244939611 10000000000 43044671608291 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072653113/10000000000 : ℝ)^273 ≤ (3200172204633/25000000000000 : ℝ)^209 := by
    have hnat : (2072653113 : ℕ)^273*25000000000000^209 ≤ 3200172204633^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072653113 10000000000 3200172204633 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668521449/1250000000 : ℝ), (5244939611/10000000000 : ℝ), (-2072653113/10000000000 : ℝ)] ![(4415463955113/10000000000000 : ℝ), (43044671608291/100000000000000 : ℝ), (3200172204633/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668521449/1250000000 : ℝ)|^273 ≤ (4415463955113/10000000000000 : ℝ)^209
        have hw : |(668521449/1250000000 : ℝ)|=(668521449/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244939611/10000000000 : ℝ)|^273 ≤ (43044671608291/100000000000000 : ℝ)^209
        have hw : |(5244939611/10000000000 : ℝ)|=(5244939611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2072653113/10000000000 : ℝ)|^273 ≤ (3200172204633/25000000000000 : ℝ)^209
        have hw : |(-2072653113/10000000000 : ℝ)|=(2072653113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s4_3 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4309542713/10000000000 : ℝ)*x 0 + (4134752617/10000000000 : ℝ)*x 1 + (4491017657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309542713/10000000000 : ℝ)^273 ≤ (33303254278697/100000000000000 : ℝ)^209 := by
    have hnat : (4309542713 : ℕ)^273*100000000000000^209 ≤ 33303254278697^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309542713 10000000000 33303254278697 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4134752617/10000000000 : ℝ)^273 ≤ (31549949566639/100000000000000 : ℝ)^209 := by
    have hnat : (4134752617 : ℕ)^273*100000000000000^209 ≤ 31549949566639^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134752617 10000000000 31549949566639 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491017657/10000000000 : ℝ)^273 ≤ (8786699036759/25000000000000 : ℝ)^209 := by
    have hnat : (4491017657 : ℕ)^273*25000000000000^209 ≤ 8786699036759^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491017657 10000000000 8786699036759 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309542713/10000000000 : ℝ), (4134752617/10000000000 : ℝ), (4491017657/10000000000 : ℝ)] ![(33303254278697/100000000000000 : ℝ), (31549949566639/100000000000000 : ℝ), (8786699036759/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309542713/10000000000 : ℝ)|^273 ≤ (33303254278697/100000000000000 : ℝ)^209
        have hw : |(4309542713/10000000000 : ℝ)|=(4309542713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4134752617/10000000000 : ℝ)|^273 ≤ (31549949566639/100000000000000 : ℝ)^209
        have hw : |(4134752617/10000000000 : ℝ)|=(4134752617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491017657/10000000000 : ℝ)|^273 ≤ (8786699036759/25000000000000 : ℝ)^209
        have hw : |(4491017657/10000000000 : ℝ)|=(4491017657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s4_4 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1988128303/10000000000 : ℝ)*x 0 + (262277411/500000000 : ℝ)*x 1 + (5410287361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1988128303/10000000000 : ℝ)^273 ≤ (12123108371507/100000000000000 : ℝ)^209 := by
    have hnat : (1988128303 : ℕ)^273*100000000000000^209 ≤ 12123108371507^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988128303 10000000000 12123108371507 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262277411/500000000 : ℝ)^273 ≤ (43051196019927/100000000000000 : ℝ)^209 := by
    have hnat : (262277411 : ℕ)^273*100000000000000^209 ≤ 43051196019927^209*500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262277411 500000000 43051196019927 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410287361/10000000000 : ℝ)^273 ≤ (44825695590161/100000000000000 : ℝ)^209 := by
    have hnat : (5410287361 : ℕ)^273*100000000000000^209 ≤ 44825695590161^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410287361 10000000000 44825695590161 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1988128303/10000000000 : ℝ), (262277411/500000000 : ℝ), (5410287361/10000000000 : ℝ)] ![(12123108371507/100000000000000 : ℝ), (43051196019927/100000000000000 : ℝ), (44825695590161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1988128303/10000000000 : ℝ)|^273 ≤ (12123108371507/100000000000000 : ℝ)^209
        have hw : |(-1988128303/10000000000 : ℝ)|=(1988128303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262277411/500000000 : ℝ)|^273 ≤ (43051196019927/100000000000000 : ℝ)^209
        have hw : |(262277411/500000000 : ℝ)|=(262277411/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410287361/10000000000 : ℝ)|^273 ≤ (44825695590161/100000000000000 : ℝ)^209
        have hw : |(5410287361/10000000000 : ℝ)|=(5410287361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s4_5 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1061023493/2000000000 : ℝ)*x 0 + (-381460933/2000000000 : ℝ)*x 1 + (1082057509/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061023493/2000000000 : ℝ)^273 ≤ (43690909193103/100000000000000 : ℝ)^209 := by
    have hnat : (1061023493 : ℕ)^273*100000000000000^209 ≤ 43690909193103^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061023493 2000000000 43690909193103 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (381460933/2000000000 : ℝ)^273 ≤ (2296678643359/20000000000000 : ℝ)^209 := by
    have hnat : (381460933 : ℕ)^273*20000000000000^209 ≤ 2296678643359^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381460933 2000000000 2296678643359 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082057509/2000000000 : ℝ)^273 ≤ (1120642439537/2500000000000 : ℝ)^209 := by
    have hnat : (1082057509 : ℕ)^273*2500000000000^209 ≤ 1120642439537^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082057509 2000000000 1120642439537 2500000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061023493/2000000000 : ℝ), (-381460933/2000000000 : ℝ), (1082057509/2000000000 : ℝ)] ![(43690909193103/100000000000000 : ℝ), (2296678643359/20000000000000 : ℝ), (1120642439537/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061023493/2000000000 : ℝ)|^273 ≤ (43690909193103/100000000000000 : ℝ)^209
        have hw : |(1061023493/2000000000 : ℝ)|=(1061023493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-381460933/2000000000 : ℝ)|^273 ≤ (2296678643359/20000000000000 : ℝ)^209
        have hw : |(-381460933/2000000000 : ℝ)|=(381460933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082057509/2000000000 : ℝ)|^273 ≤ (1120642439537/2500000000000 : ℝ)^209
        have hw : |(1082057509/2000000000 : ℝ)|=(1082057509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s4_6 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (106102349/200000000 : ℝ)*x 0 + (5410287433/10000000000 : ℝ)*x 1 + (-1907304839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106102349/200000000 : ℝ)^273 ≤ (2184545451587/5000000000000 : ℝ)^209 := by
    have hnat : (106102349 : ℕ)^273*5000000000000^209 ≤ 2184545451587^209*200000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106102349 200000000 2184545451587 5000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410287433/10000000000 : ℝ)^273 ≤ (44825696369373/100000000000000 : ℝ)^209 := by
    have hnat : (5410287433 : ℕ)^273*100000000000000^209 ≤ 44825696369373^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410287433 10000000000 44825696369373 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1907304839/10000000000 : ℝ)^273 ≤ (2870848646301/25000000000000 : ℝ)^209 := by
    have hnat : (1907304839 : ℕ)^273*25000000000000^209 ≤ 2870848646301^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1907304839 10000000000 2870848646301 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106102349/200000000 : ℝ), (5410287433/10000000000 : ℝ), (-1907304839/10000000000 : ℝ)] ![(2184545451587/5000000000000 : ℝ), (44825696369373/100000000000000 : ℝ), (2870848646301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106102349/200000000 : ℝ)|^273 ≤ (2184545451587/5000000000000 : ℝ)^209
        have hw : |(106102349/200000000 : ℝ)|=(106102349/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410287433/10000000000 : ℝ)|^273 ≤ (44825696369373/100000000000000 : ℝ)^209
        have hw : |(5410287433/10000000000 : ℝ)|=(5410287433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1907304839/10000000000 : ℝ)|^273 ≤ (2870848646301/25000000000000 : ℝ)^209
        have hw : |(-1907304839/10000000000 : ℝ)|=(1907304839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s4_7 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (861913851/2000000000 : ℝ)*x 0 + (2244855531/5000000000 : ℝ)*x 1 + (4136065699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861913851/2000000000 : ℝ)^273 ≤ (260183767181/781250000000 : ℝ)^209 := by
    have hnat : (861913851 : ℕ)^273*781250000000^209 ≤ 260183767181^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861913851 2000000000 260183767181 781250000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244855531/5000000000 : ℝ)^273 ≤ (35133440067847/100000000000000 : ℝ)^209 := by
    have hnat : (2244855531 : ℕ)^273*100000000000000^209 ≤ 35133440067847^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244855531 5000000000 35133440067847 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4136065699/10000000000 : ℝ)^273 ≤ (252504301781/800000000000 : ℝ)^209 := by
    have hnat : (4136065699 : ℕ)^273*800000000000^209 ≤ 252504301781^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4136065699 10000000000 252504301781 800000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861913851/2000000000 : ℝ), (2244855531/5000000000 : ℝ), (4136065699/10000000000 : ℝ)] ![(260183767181/781250000000 : ℝ), (35133440067847/100000000000000 : ℝ), (252504301781/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861913851/2000000000 : ℝ)|^273 ≤ (260183767181/781250000000 : ℝ)^209
        have hw : |(861913851/2000000000 : ℝ)|=(861913851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244855531/5000000000 : ℝ)|^273 ≤ (35133440067847/100000000000000 : ℝ)^209
        have hw : |(2244855531/5000000000 : ℝ)|=(2244855531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4136065699/10000000000 : ℝ)|^273 ≤ (252504301781/800000000000 : ℝ)^209
        have hw : |(4136065699/10000000000 : ℝ)|=(4136065699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1408_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7479/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1387/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2253/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14779/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7479/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1387/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7479/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1387/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7479/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1387/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7479/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1387/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7479/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1387/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7479/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1387/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (1387/12500 : ℝ) ^ (4367/1024 : ℝ) ≤ (4235850161335457/50000000000000000000 : ℝ) := by
    have hpowers : (1387/12500 : ℝ)^4367 ≤ (4235850161335457/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1387 : ℕ)^4367*50000000000000000000^1024 ≤ 4235850161335457^1024*12500^4367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1387 12500 4235850161335457 50000000000000000000 4367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1387/12500 : ℝ)) (X := (4235850161335457/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7479/50000 : ℝ) ^ (4367/1024 : ℝ) ≤ (15138947697396807/50000000000000000000 : ℝ) := by
    have hpowers : (7479/50000 : ℝ)^4367 ≤ (15138947697396807/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7479 : ℕ)^4367*50000000000000000000^1024 ≤ 15138947697396807^1024*50000^4367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7479 50000 15138947697396807 50000000000000000000 4367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7479/50000 : ℝ)) (X := (15138947697396807/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004235850161335457/25000000000000000000 : ℝ) ≤ (250009931828021/250000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (25004235850161335457/25000000000000000000 : ℝ)^1024 ≤ (250009931828021/250000000000000 : ℝ)^4367 := by
      have hnat : (25004235850161335457 : ℕ)^1024*250000000000000^4367 ≤ 250009931828021^4367*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004235850161335457 25000000000000000000 250009931828021 250000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250009931828021/250000000000000 : ℝ)) (X := (25004235850161335457/25000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252421849732341533/6250000000000000000 : ℝ) ≤ (2500227122178881/2500000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (6252421849732341533/6250000000000000000 : ℝ)^1024 ≤ (2500227122178881/2500000000000000 : ℝ)^4367 := by
      have hnat : (6252421849732341533 : ℕ)^1024*2500000000000000^4367 ≤ 2500227122178881^4367*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252421849732341533 6250000000000000000 2500227122178881 2500000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500227122178881/2500000000000000 : ℝ)) (X := (6252421849732341533/6250000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015138947697396807/25000000000000000000 : ℝ) ≤ (156272182879847/156250000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (25015138947697396807/25000000000000000000 : ℝ)^1024 ≤ (156272182879847/156250000000000 : ℝ)^4367 := by
      have hnat : (25015138947697396807 : ℕ)^1024*156250000000000^4367 ≤ 156272182879847^4367*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015138947697396807 25000000000000000000 156272182879847 156250000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156272182879847/156250000000000 : ℝ)) (X := (25015138947697396807/25000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4235850161335457/50000000000000000000 : ℝ) ≤ ((2413136835769716047/2413750000000000000 : ℝ)+2*(127803898671/96550000000000 : ℝ)*(1387/12500 : ℝ))^(4367/1024 : ℝ) := by
    rw [show (2413136835769716047/2413750000000000000 : ℝ)+2*(127803898671/96550000000000 : ℝ)*(1387/12500 : ℝ)=(250009931828021/250000000000000 : ℝ) by norm_num, show 1+2*(4235850161335457/50000000000000000000 : ℝ)=(25004235850161335457/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15138947697396807/50000000000000000000 : ℝ)+(4235850161335457/50000000000000000000 : ℝ) ≤ ((2413136835769716047/2413750000000000000 : ℝ)+(127803898671/96550000000000 : ℝ)*((7479/50000 : ℝ)+(1387/12500 : ℝ)))^(4367/1024 : ℝ) := by
    rw [show (2413136835769716047/2413750000000000000 : ℝ)+(127803898671/96550000000000 : ℝ)*((7479/50000 : ℝ)+(1387/12500 : ℝ))=(2500227122178881/2500000000000000 : ℝ) by norm_num, show 1+(15138947697396807/50000000000000000000 : ℝ)+(4235850161335457/50000000000000000000 : ℝ)=(6252421849732341533/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15138947697396807/50000000000000000000 : ℝ) ≤ ((2413136835769716047/2413750000000000000 : ℝ)+2*(127803898671/96550000000000 : ℝ)*(7479/50000 : ℝ))^(4367/1024 : ℝ) := by
    rw [show (2413136835769716047/2413750000000000000 : ℝ)+2*(127803898671/96550000000000 : ℝ)*(7479/50000 : ℝ)=(156272182879847/156250000000000 : ℝ) by norm_num, show 1+2*(15138947697396807/50000000000000000000 : ℝ)=(25015138947697396807/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2413136835769716047/2413750000000000000 : ℝ)*(X 1 0+X 2 0)+(127803898671/96550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (1387/12500 : ℝ)) (hi := (7479/50000 : ℝ)) (c := (2413136835769716047/2413750000000000000 : ℝ)) (alpha := (127803898671/96550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2413136835769716047/2413750000000000000 : ℝ)*(X 0 1+X 2 1)+(127803898671/96550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (1387/12500 : ℝ)) (hi := (7479/50000 : ℝ)) (c := (2413136835769716047/2413750000000000000 : ℝ)) (alpha := (127803898671/96550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2413136835769716047/2413750000000000000 : ℝ)*(X 0 2+X 1 2)+(127803898671/96550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (1387/12500 : ℝ)) (hi := (7479/50000 : ℝ)) (c := (2413136835769716047/2413750000000000000 : ℝ)) (alpha := (127803898671/96550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-62128627/312500000 : ℝ)*X 0 0+(5410899183/10000000000 : ℝ)*X 0 1+(5244939649/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348171473/10000000000 : ℝ)*X 1 0+(-41453053/200000000 : ℝ)*X 1 1+(65561751/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668521449/1250000000 : ℝ)*X 2 0+(5244939611/10000000000 : ℝ)*X 2 1+(-2072653113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4309542713/10000000000 : ℝ)*X 0 0+(4134752617/10000000000 : ℝ)*X 0 1+(4491017657/10000000000 : ℝ)*X 0 2+(4309542713/10000000000 : ℝ)*X 1 0+(4134752617/10000000000 : ℝ)*X 1 1+(4491017657/10000000000 : ℝ)*X 1 2+(4309542713/10000000000 : ℝ)*X 2 0+(4134752617/10000000000 : ℝ)*X 2 1+(4491017657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1988128303/10000000000 : ℝ)*X 0 0+(262277411/500000000 : ℝ)*X 0 1+(5410287361/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061023493/2000000000 : ℝ)*X 1 0+(-381460933/2000000000 : ℝ)*X 1 1+(1082057509/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((106102349/200000000 : ℝ)*X 2 0+(5410287433/10000000000 : ℝ)*X 2 1+(-1907304839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((861913851/2000000000 : ℝ)*X 0 0+(2244855531/5000000000 : ℝ)*X 0 1+(4136065699/10000000000 : ℝ)*X 0 2+(861913851/2000000000 : ℝ)*X 1 0+(2244855531/5000000000 : ℝ)*X 1 1+(4136065699/10000000000 : ℝ)*X 1 2+(861913851/2000000000 : ℝ)*X 2 0+(2244855531/5000000000 : ℝ)*X 2 1+(4136065699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (312530436663939693234143583/60343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29752851/25000000000000 : ℝ)*(base15) + (3921913/2000000000000 : ℝ)*(base29) + (5568477/6250000000000 : ℝ)*(upper2) + (47344969/50000000000000 : ℝ)*(upper3) + (2931339/6250000000000 : ℝ)*(upper4) + (2208117413854969/50000000000000 : ℝ)*(major0) + (1104058755951397/25000000000000 : ℝ)*(major1) + (1104058755951397/25000000000000 : ℝ)*(major2) + (3012785614305283/50000000000000 : ℝ)*(sp0) + (753196364187939/12500000000000 : ℝ)*(sp1) + (3012778718254963/50000000000000 : ℝ)*(sp2) + (175431163901939/6250000000000 : ℝ)*(sp3) + (6798002497/50000000000000 : ℝ)*(sp6) + (11965309/50000000000000 : ℝ)*(sp7) + (1403449323180821/50000000000000 : ℝ)*(f.failure) + (3012785614305283/50000000000000 : ℝ)*(f.sum) + (16432565221497/4827500000000000000000000000 : ℝ)*base66 + (683612676222419841/60343750000000000000000000000000 : ℝ)*base68 + (3710403303648732341/60343750000000000000000000000000 : ℝ)*base70 + (355729154649287457/120687500000000000000000000000000 : ℝ)*base72 + (5149831553637/4827500000000000000000000000 : ℝ)*base74 + (265391953100142659/60343750000000000000000000000000 : ℝ)*base75 + (10065286459911537457/120687500000000000000000000000000 : ℝ)*base78 + (702882749195544841/60343750000000000000000000000000 : ℝ)*base80 + (56644407044671/2413750000000000000000000000 : ℝ)*base82 + (1/25000000000000 : ℝ)*base87 + (29725377/5000000000000000000000 : ℝ)*base89 + (29725377/5000000000000000000000 : ℝ)*base91 + (29725377/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16467886296752424304983/4827500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1378237/400000000000 : ℝ)*(base19) + (83088559/20000000000000 : ℝ)*(base23) + (9130337/12500000000000 : ℝ)*(upper2) + (24316683/50000000000000 : ℝ)*(upper3) + (123632749/100000000000000 : ℝ)*(upper5) + (278059161922047/6250000000000 : ℝ)*(major0) + (278059161922047/6250000000000 : ℝ)*(major1) + (278059161922047/6250000000000 : ℝ)*(major2) + (2675591859/20000000000000 : ℝ)*(sp1) + (3630851463/50000000000000 : ℝ)*(sp2) + (3035101698195017/50000000000000 : ℝ)*(sp4) + (6070189673871489/100000000000000 : ℝ)*(sp5) + (6070195719244313/100000000000000 : ℝ)*(sp6) + (14138448357033/500000000000 : ℝ)*(sp7) + (14138448357033/500000000000 : ℝ)*(f.failure) + (3035101698195017/50000000000000 : ℝ)*(f.sum) + (6704113602003/4827500000000000000000000000 : ℝ)*base66 + (40782313143524291/15085937500000000000000000000000 : ℝ)*base68 + (5934370133651917/7542968750000000000000000000000 : ℝ)*base69 + (101775984037586791/15085937500000000000000000000000 : ℝ)*base72 + (31020690578391/9655000000000000000000000000 : ℝ)*base74 + (330139272696154543/30171875000000000000000000000000 : ℝ)*base75 + (89752332325754333/7542968750000000000000000000000 : ℝ)*base78 + (355982448831935793/30171875000000000000000000000000 : ℝ)*base79 + (5080050681341/9655000000000000000000000000 : ℝ)*base82 + (265221/50000000000000000000 : ℝ)*base89 + (265221/50000000000000000000 : ℝ)*base91 + (265221/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1408_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7479/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1387/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2253/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14779/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1408_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1408_s5_0 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1988271691/10000000000 : ℝ)*x 0 + (5409516827/10000000000 : ℝ)*x 1 + (5246219519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1988271691/10000000000 : ℝ)^273 ≤ (12124250469959/100000000000000 : ℝ)^209 := by
    have hnat : (1988271691 : ℕ)^273*100000000000000^209 ≤ 12124250469959^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988271691 10000000000 12124250469959 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409516827/10000000000 : ℝ)^273 ≤ (44817356754751/100000000000000 : ℝ)^209 := by
    have hnat : (5409516827 : ℕ)^273*100000000000000^209 ≤ 44817356754751^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409516827 10000000000 44817356754751 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246219519/10000000000 : ℝ)^273 ≤ (43058392749903/100000000000000 : ℝ)^209 := by
    have hnat : (5246219519 : ℕ)^273*100000000000000^209 ≤ 43058392749903^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246219519 10000000000 43058392749903 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1988271691/10000000000 : ℝ), (5409516827/10000000000 : ℝ), (5246219519/10000000000 : ℝ)] ![(12124250469959/100000000000000 : ℝ), (44817356754751/100000000000000 : ℝ), (43058392749903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1988271691/10000000000 : ℝ)|^273 ≤ (12124250469959/100000000000000 : ℝ)^209
        have hw : |(-1988271691/10000000000 : ℝ)|=(1988271691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409516827/10000000000 : ℝ)|^273 ≤ (44817356754751/100000000000000 : ℝ)^209
        have hw : |(5409516827/10000000000 : ℝ)|=(5409516827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246219519/10000000000 : ℝ)|^273 ≤ (43058392749903/100000000000000 : ℝ)^209
        have hw : |(5246219519/10000000000 : ℝ)|=(5246219519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s5_1 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5347816149/10000000000 : ℝ)*x 0 + (-414285529/2000000000 : ℝ)*x 1 + (5246219257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347816149/10000000000 : ℝ)^273 ≤ (11037701606673/25000000000000 : ℝ)^209 := by
    have hnat : (5347816149 : ℕ)^273*25000000000000^209 ≤ 11037701606673^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347816149 10000000000 11037701606673 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (414285529/2000000000 : ℝ)^273 ≤ (12790803612383/100000000000000 : ℝ)^209 := by
    have hnat : (414285529 : ℕ)^273*100000000000000^209 ≤ 12790803612383^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414285529 2000000000 12790803612383 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246219257/10000000000 : ℝ)^273 ≤ (861167798821/2000000000000 : ℝ)^209 := by
    have hnat : (5246219257 : ℕ)^273*2000000000000^209 ≤ 861167798821^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246219257 10000000000 861167798821 2000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347816149/10000000000 : ℝ), (-414285529/2000000000 : ℝ), (5246219257/10000000000 : ℝ)] ![(11037701606673/25000000000000 : ℝ), (12790803612383/100000000000000 : ℝ), (861167798821/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347816149/10000000000 : ℝ)|^273 ≤ (11037701606673/25000000000000 : ℝ)^209
        have hw : |(5347816149/10000000000 : ℝ)|=(5347816149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-414285529/2000000000 : ℝ)|^273 ≤ (12790803612383/100000000000000 : ℝ)^209
        have hw : |(-414285529/2000000000 : ℝ)|=(414285529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246219257/10000000000 : ℝ)|^273 ≤ (861167798821/2000000000000 : ℝ)^209
        have hw : |(5246219257/10000000000 : ℝ)|=(5246219257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s5_2 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (66847699/125000000 : ℝ)*x 0 + (5246219327/10000000000 : ℝ)*x 1 + (-103571393/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66847699/125000000 : ℝ)^273 ≤ (11037700989291/25000000000000 : ℝ)^209 := by
    have hnat : (66847699 : ℕ)^273*25000000000000^209 ≤ 11037700989291^209*125000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66847699 125000000 11037700989291 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246219327/10000000000 : ℝ)^273 ≤ (43058390691507/100000000000000 : ℝ)^209 := by
    have hnat : (5246219327 : ℕ)^273*100000000000000^209 ≤ 43058390691507^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246219327 10000000000 43058390691507 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103571393/500000000 : ℝ)^273 ≤ (6395402673259/50000000000000 : ℝ)^209 := by
    have hnat : (103571393 : ℕ)^273*50000000000000^209 ≤ 6395402673259^209*500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103571393 500000000 6395402673259 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66847699/125000000 : ℝ), (5246219327/10000000000 : ℝ), (-103571393/500000000 : ℝ)] ![(11037700989291/25000000000000 : ℝ), (43058390691507/100000000000000 : ℝ), (6395402673259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66847699/125000000 : ℝ)|^273 ≤ (11037700989291/25000000000000 : ℝ)^209
        have hw : |(66847699/125000000 : ℝ)|=(66847699/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246219327/10000000000 : ℝ)|^273 ≤ (43058390691507/100000000000000 : ℝ)^209
        have hw : |(5246219327/10000000000 : ℝ)|=(5246219327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103571393/500000000 : ℝ)|^273 ≤ (6395402673259/50000000000000 : ℝ)^209
        have hw : |(-103571393/500000000 : ℝ)|=(103571393/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s5_3 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2154818693/5000000000 : ℝ)*x 0 + (4137598727/10000000000 : ℝ)*x 1 + (2244074309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154818693/5000000000 : ℝ)^273 ≤ (16652104964987/50000000000000 : ℝ)^209 := by
    have hnat : (2154818693 : ℕ)^273*50000000000000^209 ≤ 16652104964987^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154818693 5000000000 16652104964987 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4137598727/10000000000 : ℝ)^273 ≤ (6315663960443/20000000000000 : ℝ)^209 := by
    have hnat : (4137598727 : ℕ)^273*20000000000000^209 ≤ 6315663960443^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137598727 10000000000 6315663960443 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244074309/5000000000 : ℝ)^273 ≤ (35117470250043/100000000000000 : ℝ)^209 := by
    have hnat : (2244074309 : ℕ)^273*100000000000000^209 ≤ 35117470250043^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244074309 5000000000 35117470250043 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154818693/5000000000 : ℝ), (4137598727/10000000000 : ℝ), (2244074309/5000000000 : ℝ)] ![(16652104964987/50000000000000 : ℝ), (6315663960443/20000000000000 : ℝ), (35117470250043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154818693/5000000000 : ℝ)|^273 ≤ (16652104964987/50000000000000 : ℝ)^209
        have hw : |(2154818693/5000000000 : ℝ)|=(2154818693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4137598727/10000000000 : ℝ)|^273 ≤ (6315663960443/20000000000000 : ℝ)^209
        have hw : |(4137598727/10000000000 : ℝ)|=(4137598727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2244074309/5000000000 : ℝ)|^273 ≤ (35117470250043/100000000000000 : ℝ)^209
        have hw : |(2244074309/5000000000 : ℝ)|=(2244074309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s5_4 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1988283727/10000000000 : ℝ)*x 0 + (5246808793/10000000000 : ℝ)*x 1 + (5408924181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1988283727/10000000000 : ℝ)^273 ≤ (12124346338941/100000000000000 : ℝ)^209 := by
    have hnat : (1988283727 : ℕ)^273*100000000000000^209 ≤ 12124346338941^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988283727 10000000000 12124346338941 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246808793/10000000000 : ℝ)^273 ≤ (43064710354849/100000000000000 : ℝ)^209 := by
    have hnat : (5246808793 : ℕ)^273*100000000000000^209 ≤ 43064710354849^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246808793 10000000000 43064710354849 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408924181/10000000000 : ℝ)^273 ≤ (22405471648809/50000000000000 : ℝ)^209 := by
    have hnat : (5408924181 : ℕ)^273*50000000000000^209 ≤ 22405471648809^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408924181 10000000000 22405471648809 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1988283727/10000000000 : ℝ), (5246808793/10000000000 : ℝ), (5408924181/10000000000 : ℝ)] ![(12124346338941/100000000000000 : ℝ), (43064710354849/100000000000000 : ℝ), (22405471648809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1988283727/10000000000 : ℝ)|^273 ≤ (12124346338941/100000000000000 : ℝ)^209
        have hw : |(-1988283727/10000000000 : ℝ)|=(1988283727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246808793/10000000000 : ℝ)|^273 ≤ (43064710354849/100000000000000 : ℝ)^209
        have hw : |(5246808793/10000000000 : ℝ)|=(5246808793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408924181/10000000000 : ℝ)|^273 ≤ (22405471648809/50000000000000 : ℝ)^209
        have hw : |(5408924181/10000000000 : ℝ)|=(5408924181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s5_5 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2652725953/5000000000 : ℝ)*x 0 + (-954361553/5000000000 : ℝ)*x 1 + (5408924181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652725953/5000000000 : ℝ)^273 ≤ (43694506985867/100000000000000 : ℝ)^209 := by
    have hnat : (2652725953 : ℕ)^273*100000000000000^209 ≤ 43694506985867^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652725953 5000000000 43694506985867 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (954361553/5000000000 : ℝ)^273 ≤ (1149454969811/10000000000000 : ℝ)^209 := by
    have hnat : (954361553 : ℕ)^273*10000000000000^209 ≤ 1149454969811^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954361553 5000000000 1149454969811 10000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408924181/10000000000 : ℝ)^273 ≤ (22405471648809/50000000000000 : ℝ)^209 := by
    have hnat : (5408924181 : ℕ)^273*50000000000000^209 ≤ 22405471648809^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408924181 10000000000 22405471648809 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652725953/5000000000 : ℝ), (-954361553/5000000000 : ℝ), (5408924181/10000000000 : ℝ)] ![(43694506985867/100000000000000 : ℝ), (1149454969811/10000000000000 : ℝ), (22405471648809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652725953/5000000000 : ℝ)|^273 ≤ (43694506985867/100000000000000 : ℝ)^209
        have hw : |(2652725953/5000000000 : ℝ)|=(2652725953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-954361553/5000000000 : ℝ)|^273 ≤ (1149454969811/10000000000000 : ℝ)^209
        have hw : |(-954361553/5000000000 : ℝ)|=(954361553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408924181/10000000000 : ℝ)|^273 ≤ (22405471648809/50000000000000 : ℝ)^209
        have hw : |(5408924181/10000000000 : ℝ)|=(5408924181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s5_6 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (41448843/78125000 : ℝ)*x 0 + (5408924183/10000000000 : ℝ)*x 1 + (-954361553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41448843/78125000 : ℝ)^273 ≤ (43694506964351/100000000000000 : ℝ)^209 := by
    have hnat : (41448843 : ℕ)^273*100000000000000^209 ≤ 43694506964351^209*78125000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41448843 78125000 43694506964351 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408924183/10000000000 : ℝ)^273 ≤ (22405471659631/50000000000000 : ℝ)^209 := by
    have hnat : (5408924183 : ℕ)^273*50000000000000^209 ≤ 22405471659631^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408924183 10000000000 22405471659631 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (954361553/5000000000 : ℝ)^273 ≤ (1149454969811/10000000000000 : ℝ)^209 := by
    have hnat : (954361553 : ℕ)^273*10000000000000^209 ≤ 1149454969811^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954361553 5000000000 1149454969811 10000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41448843/78125000 : ℝ), (5408924183/10000000000 : ℝ), (-954361553/5000000000 : ℝ)] ![(43694506964351/100000000000000 : ℝ), (22405471659631/50000000000000 : ℝ), (1149454969811/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41448843/78125000 : ℝ)|^273 ≤ (43694506964351/100000000000000 : ℝ)^209
        have hw : |(41448843/78125000 : ℝ)|=(41448843/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408924183/10000000000 : ℝ)|^273 ≤ (22405471659631/50000000000000 : ℝ)^209
        have hw : |(5408924183/10000000000 : ℝ)|=(5408924183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-954361553/5000000000 : ℝ)|^273 ≤ (1149454969811/10000000000000 : ℝ)^209
        have hw : |(-954361553/5000000000 : ℝ)|=(954361553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s5_7 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4309662883/10000000000 : ℝ)*x 0 + (2243441637/5000000000 : ℝ)*x 1 + (827774009/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309662883/10000000000 : ℝ)^273 ≤ (33304467303721/100000000000000 : ℝ)^209 := by
    have hnat : (4309662883 : ℕ)^273*100000000000000^209 ≤ 33304467303721^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309662883 10000000000 33304467303721 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243441637/5000000000 : ℝ)^273 ≤ (17552269176829/50000000000000 : ℝ)^209 := by
    have hnat : (2243441637 : ℕ)^273*50000000000000^209 ≤ 17552269176829^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243441637 5000000000 17552269176829 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (827774009/2000000000 : ℝ)^273 ≤ (31590994325549/100000000000000 : ℝ)^209 := by
    have hnat : (827774009 : ℕ)^273*100000000000000^209 ≤ 31590994325549^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827774009 2000000000 31590994325549 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309662883/10000000000 : ℝ), (2243441637/5000000000 : ℝ), (827774009/2000000000 : ℝ)] ![(33304467303721/100000000000000 : ℝ), (17552269176829/50000000000000 : ℝ), (31590994325549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309662883/10000000000 : ℝ)|^273 ≤ (33304467303721/100000000000000 : ℝ)^209
        have hw : |(4309662883/10000000000 : ℝ)|=(4309662883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243441637/5000000000 : ℝ)|^273 ≤ (17552269176829/50000000000000 : ℝ)^209
        have hw : |(2243441637/5000000000 : ℝ)|=(2243441637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(827774009/2000000000 : ℝ)|^273 ≤ (31590994325549/100000000000000 : ℝ)^209
        have hw : |(827774009/2000000000 : ℝ)|=(827774009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1408_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14779/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2253/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2823/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (59/400 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14779/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2253/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14779/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2253/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14779/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2253/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14779/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2253/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14779/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2253/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14779/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2253/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2253/20000 : ℝ) ^ (4367/1024 : ℝ) ≤ (9035806602545861/100000000000000000000 : ℝ) := by
    have hpowers : (2253/20000 : ℝ)^4367 ≤ (9035806602545861/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2253 : ℕ)^4367*100000000000000000000^1024 ≤ 9035806602545861^1024*20000^4367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2253 20000 9035806602545861 100000000000000000000 4367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2253/20000 : ℝ)) (X := (9035806602545861/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14779/100000 : ℝ) ^ (4367/1024 : ℝ) ≤ (14381297172577333/50000000000000000000 : ℝ) := by
    have hpowers : (14779/100000 : ℝ)^4367 ≤ (14381297172577333/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14779 : ℕ)^4367*50000000000000000000^1024 ≤ 14381297172577333^1024*100000^4367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14779 100000 14381297172577333 50000000000000000000 4367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14779/100000 : ℝ)) (X := (14381297172577333/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009035806602545861/50000000000000000000 : ℝ) ≤ (10000423724571501/10000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (50009035806602545861/50000000000000000000 : ℝ)^1024 ≤ (10000423724571501/10000000000000000 : ℝ)^4367 := by
      have hnat : (50009035806602545861 : ℕ)^1024*10000000000000000^4367 ≤ 10000423724571501^4367*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009035806602545861 50000000000000000000 10000423724571501 10000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000423724571501/10000000000000000 : ℝ)) (X := (50009035806602545861/50000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037798400947700527/100000000000000000000 : ℝ) ≤ (1250110773883811/1250000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (100037798400947700527/100000000000000000000 : ℝ)^1024 ≤ (1250110773883811/1250000000000000 : ℝ)^4367 := by
      have hnat : (100037798400947700527 : ℕ)^1024*1250000000000000^4367 ≤ 1250110773883811^4367*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037798400947700527 100000000000000000000 1250110773883811 1250000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250110773883811/1250000000000000 : ℝ)) (X := (100037798400947700527/100000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014381297172577333/25000000000000000000 : ℝ) ≤ (400053946302779/400000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (25014381297172577333/25000000000000000000 : ℝ)^1024 ≤ (400053946302779/400000000000000 : ℝ)^4367 := by
      have hnat : (25014381297172577333 : ℕ)^1024*400000000000000^4367 ≤ 400053946302779^4367*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014381297172577333 25000000000000000000 400053946302779 400000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400053946302779/400000000000000 : ℝ)) (X := (25014381297172577333/25000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9035806602545861/100000000000000000000 : ℝ) ≤ ((8782767399480519351/8785000000000000000 : ℝ)+2*(462466498987/351400000000000 : ℝ)*(2253/20000 : ℝ))^(4367/1024 : ℝ) := by
    rw [show (8782767399480519351/8785000000000000000 : ℝ)+2*(462466498987/351400000000000 : ℝ)*(2253/20000 : ℝ)=(10000423724571501/10000000000000000 : ℝ) by norm_num, show 1+2*(9035806602545861/100000000000000000000 : ℝ)=(50009035806602545861/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14381297172577333/50000000000000000000 : ℝ)+(9035806602545861/100000000000000000000 : ℝ) ≤ ((8782767399480519351/8785000000000000000 : ℝ)+(462466498987/351400000000000 : ℝ)*((14779/100000 : ℝ)+(2253/20000 : ℝ)))^(4367/1024 : ℝ) := by
    rw [show (8782767399480519351/8785000000000000000 : ℝ)+(462466498987/351400000000000 : ℝ)*((14779/100000 : ℝ)+(2253/20000 : ℝ))=(1250110773883811/1250000000000000 : ℝ) by norm_num, show 1+(14381297172577333/50000000000000000000 : ℝ)+(9035806602545861/100000000000000000000 : ℝ)=(100037798400947700527/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14381297172577333/50000000000000000000 : ℝ) ≤ ((8782767399480519351/8785000000000000000 : ℝ)+2*(462466498987/351400000000000 : ℝ)*(14779/100000 : ℝ))^(4367/1024 : ℝ) := by
    rw [show (8782767399480519351/8785000000000000000 : ℝ)+2*(462466498987/351400000000000 : ℝ)*(14779/100000 : ℝ)=(400053946302779/400000000000000 : ℝ) by norm_num, show 1+2*(14381297172577333/50000000000000000000 : ℝ)=(25014381297172577333/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8782767399480519351/8785000000000000000 : ℝ)*(X 1 0+X 2 0)+(462466498987/351400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (2253/20000 : ℝ)) (hi := (14779/100000 : ℝ)) (c := (8782767399480519351/8785000000000000000 : ℝ)) (alpha := (462466498987/351400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8782767399480519351/8785000000000000000 : ℝ)*(X 0 1+X 2 1)+(462466498987/351400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (2253/20000 : ℝ)) (hi := (14779/100000 : ℝ)) (c := (8782767399480519351/8785000000000000000 : ℝ)) (alpha := (462466498987/351400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8782767399480519351/8785000000000000000 : ℝ)*(X 0 2+X 1 2)+(462466498987/351400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (2253/20000 : ℝ)) (hi := (14779/100000 : ℝ)) (c := (8782767399480519351/8785000000000000000 : ℝ)) (alpha := (462466498987/351400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1988271691/10000000000 : ℝ)*X 0 0+(5409516827/10000000000 : ℝ)*X 0 1+(5246219519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347816149/10000000000 : ℝ)*X 1 0+(-414285529/2000000000 : ℝ)*X 1 1+(5246219257/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66847699/125000000 : ℝ)*X 2 0+(5246219327/10000000000 : ℝ)*X 2 1+(-103571393/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2154818693/5000000000 : ℝ)*X 0 0+(4137598727/10000000000 : ℝ)*X 0 1+(2244074309/5000000000 : ℝ)*X 0 2+(2154818693/5000000000 : ℝ)*X 1 0+(4137598727/10000000000 : ℝ)*X 1 1+(2244074309/5000000000 : ℝ)*X 1 2+(2154818693/5000000000 : ℝ)*X 2 0+(4137598727/10000000000 : ℝ)*X 2 1+(2244074309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1988283727/10000000000 : ℝ)*X 0 0+(5246808793/10000000000 : ℝ)*X 0 1+(5408924181/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652725953/5000000000 : ℝ)*X 1 0+(-954361553/5000000000 : ℝ)*X 1 1+(5408924181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41448843/78125000 : ℝ)*X 2 0+(5408924183/10000000000 : ℝ)*X 2 1+(-954361553/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4309662883/10000000000 : ℝ)*X 0 0+(2243441637/5000000000 : ℝ)*X 0 1+(827774009/2000000000 : ℝ)*X 0 2+(4309662883/10000000000 : ℝ)*X 1 0+(2243441637/5000000000 : ℝ)*X 1 1+(827774009/2000000000 : ℝ)*X 1 2+(4309662883/10000000000 : ℝ)*X 2 0+(2243441637/5000000000 : ℝ)*X 2 1+(827774009/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1685718321588031953241251051/219625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (98466771/10000000000000 : ℝ)*(base19) + (986551849/100000000000000 : ℝ)*(base23) + (543687/20000000000000 : ℝ)*(lower2) + (143962117/100000000000000 : ℝ)*(lower4) + (116550297/100000000000000 : ℝ)*(lower5) + (2244131522495567/50000000000000 : ℝ)*(major0) + (2244131522495567/50000000000000 : ℝ)*(major1) + (2244131522495567/50000000000000 : ℝ)*(major2) + (191369632918517/3125000000000 : ℝ)*(sp0) + (6123846176888943/100000000000000 : ℝ)*(sp1) + (1530961543751201/25000000000000 : ℝ)*(sp2) + (2852670011214269/100000000000000 : ℝ)*(sp3) + (1890816411/10000000000000 : ℝ)*(sp4) + (1082670421/12500000000000 : ℝ)*(sp7) + (2852678672577637/100000000000000 : ℝ)*(f.failure) + (6123847161556653/100000000000000 : ℝ)*(f.sum) + (52560780151011/8785000000000000000000000000 : ℝ)*base66 + (1224387654064307983/439250000000000000000000000000000 : ℝ)*base68 + (1943419055063057983/439250000000000000000000000000000 : ℝ)*base70 + (1056801379915307983/439250000000000000000000000000000 : ℝ)*base72 + (13456041619971/8785000000000000000000000000 : ℝ)*base74 + (4241324122565692017/439250000000000000000000000000000 : ℝ)*base75 + (8503292061655557983/439250000000000000000000000000000 : ℝ)*base78 + (3772832305678192017/439250000000000000000000000000000 : ℝ)*base79 + (8320311240459/8785000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2767569/10000000000000000000000 : ℝ)*base89 + (2767569/10000000000000000000000 : ℝ)*base91 + (2767569/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1214949964578755138823/549062500000000000000000000 : ℝ) := by norm_num
    linear_combination (192912363/50000000000000 : ℝ)*(base19) + (20652229/5000000000000 : ℝ)*(base23) + (23272341/50000000000000 : ℝ)*(upper3) + (13279129/100000000000000 : ℝ)*(lower4) + (22700241/50000000000000 : ℝ)*(upper5) + (35319920018639/781250000000 : ℝ)*(major0) + (35319920018639/781250000000 : ℝ)*(major1) + (35319920018639/781250000000 : ℝ)*(major2) + (4013104547/50000000000000 : ℝ)*(sp1) + (2147952017/25000000000000 : ℝ)*(sp2) + (6168445547426003/100000000000000 : ℝ)*(sp4) + (6168437135392183/100000000000000 : ℝ)*(sp5) + (1542109135643339/25000000000000 : ℝ)*(sp6) + (1436726951793259/50000000000000 : ℝ)*(sp7) + (1436726951793259/50000000000000 : ℝ)*(f.failure) + (6168445547426003/100000000000000 : ℝ)*(f.sum) + (29316002804853/8785000000000000000000000000 : ℝ)*base66 + (122779958262888719/27453125000000000000000000000000 : ℝ)*base68 + (95030732185642531/27453125000000000000000000000000 : ℝ)*base69 + (62876908443094703/13726562500000000000000000000000 : ℝ)*base71 + (2452939410009/274531250000000000000000000 : ℝ)*base74 + (159281888027888719/27453125000000000000000000000000 : ℝ)*base76 + (52087794903563453/13726562500000000000000000000000 : ℝ)*base77 + (27285328350800543/3431640625000000000000000000000 : ℝ)*base80 + (21636176752219/4392500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (21115583/5000000000000000000000 : ℝ)*base89 + (21115583/5000000000000000000000 : ℝ)*base91 + (21115583/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1408_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14779/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2253/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (59/400 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1408_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1408_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7933/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2563/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (59/400 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1408_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1408_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1408_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7933/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2563/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (59/400 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1408_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

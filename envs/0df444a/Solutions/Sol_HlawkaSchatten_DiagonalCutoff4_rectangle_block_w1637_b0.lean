-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1637_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:08:39.66103+00:00
-- url     : https://prove2.me/submissions/ab99217b-959d-4b66-851f-d1e976062025

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
theorem support_rectangle_w1637_s0_0 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-94734043/625000000 : ℝ)*x 0 + (1450409271/2500000000 : ℝ)*x 1 + (2456293331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94734043/625000000 : ℝ)^4867 ≤ (9168470793411/100000000000000 : ℝ)^3843 := by
    have hnat : (94734043 : ℕ)^4867*100000000000000^3843 ≤ 9168470793411^3843*625000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94734043 625000000 9168470793411 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1450409271/2500000000 : ℝ)^4867 ≤ (50181841671081/100000000000000 : ℝ)^3843 := by
    have hnat : (1450409271 : ℕ)^4867*100000000000000^3843 ≤ 50181841671081^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1450409271 2500000000 50181841671081 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2456293331/5000000000 : ℝ)^4867 ≤ (2540605470389/6250000000000 : ℝ)^3843 := by
    have hnat : (2456293331 : ℕ)^4867*6250000000000^3843 ≤ 2540605470389^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2456293331 5000000000 2540605470389 6250000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-94734043/625000000 : ℝ), (1450409271/2500000000 : ℝ), (2456293331/5000000000 : ℝ)] ![(9168470793411/100000000000000 : ℝ), (50181841671081/100000000000000 : ℝ), (2540605470389/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-94734043/625000000 : ℝ)|^4867 ≤ (9168470793411/100000000000000 : ℝ)^3843
        have hw : |(-94734043/625000000 : ℝ)|=(94734043/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1450409271/2500000000 : ℝ)|^4867 ≤ (50181841671081/100000000000000 : ℝ)^3843
        have hw : |(1450409271/2500000000 : ℝ)|=(1450409271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2456293331/5000000000 : ℝ)|^4867 ≤ (2540605470389/6250000000000 : ℝ)^3843
        have hw : |(2456293331/5000000000 : ℝ)|=(2456293331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s0_1 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (544272531/1000000000 : ℝ)*x 0 + (-501273239/2500000000 : ℝ)*x 1 + (982517661/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544272531/1000000000 : ℝ)^4867 ≤ (46283101717779/100000000000000 : ℝ)^3843 := by
    have hnat : (544272531 : ℕ)^4867*100000000000000^3843 ≤ 46283101717779^3843*1000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544272531 1000000000 46283101717779 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501273239/2500000000 : ℝ)^4867 ≤ (13067193517127/100000000000000 : ℝ)^3843 := by
    have hnat : (501273239 : ℕ)^4867*100000000000000^3843 ≤ 13067193517127^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501273239 2500000000 13067193517127 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (982517661/2000000000 : ℝ)^4867 ≤ (40649704743939/100000000000000 : ℝ)^3843 := by
    have hnat : (982517661 : ℕ)^4867*100000000000000^3843 ≤ 40649704743939^3843*2000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982517661 2000000000 40649704743939 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544272531/1000000000 : ℝ), (-501273239/2500000000 : ℝ), (982517661/2000000000 : ℝ)] ![(46283101717779/100000000000000 : ℝ), (13067193517127/100000000000000 : ℝ), (40649704743939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544272531/1000000000 : ℝ)|^4867 ≤ (46283101717779/100000000000000 : ℝ)^3843
        have hw : |(544272531/1000000000 : ℝ)|=(544272531/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-501273239/2500000000 : ℝ)|^4867 ≤ (13067193517127/100000000000000 : ℝ)^3843
        have hw : |(-501273239/2500000000 : ℝ)|=(501273239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(982517661/2000000000 : ℝ)|^4867 ≤ (40649704743939/100000000000000 : ℝ)^3843
        have hw : |(982517661/2000000000 : ℝ)|=(982517661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s0_2 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5442726833/10000000000 : ℝ)*x 0 + (307036677/625000000 : ℝ)*x 1 + (-50127321/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5442726833/10000000000 : ℝ)^4867 ≤ (46283118119783/100000000000000 : ℝ)^3843 := by
    have hnat : (5442726833 : ℕ)^4867*100000000000000^3843 ≤ 46283118119783^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442726833 10000000000 46283118119783 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (307036677/625000000 : ℝ)^4867 ≤ (2540605581733/6250000000000 : ℝ)^3843 := by
    have hnat : (307036677 : ℕ)^4867*6250000000000^3843 ≤ 2540605581733^3843*625000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307036677 625000000 2540605581733 6250000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50127321/250000000 : ℝ)^4867 ≤ (13067192559719/100000000000000 : ℝ)^3843 := by
    have hnat : (50127321 : ℕ)^4867*100000000000000^3843 ≤ 13067192559719^3843*250000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50127321 250000000 13067192559719 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5442726833/10000000000 : ℝ), (307036677/625000000 : ℝ), (-50127321/250000000 : ℝ)] ![(46283118119783/100000000000000 : ℝ), (2540605581733/6250000000000 : ℝ), (13067192559719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5442726833/10000000000 : ℝ)|^4867 ≤ (46283118119783/100000000000000 : ℝ)^3843
        have hw : |(5442726833/10000000000 : ℝ)|=(5442726833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(307036677/625000000 : ℝ)|^4867 ≤ (2540605581733/6250000000000 : ℝ)^3843
        have hw : |(307036677/625000000 : ℝ)|=(307036677/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-50127321/250000000 : ℝ)|^4867 ≤ (13067192559719/100000000000000 : ℝ)^3843
        have hw : |(-50127321/250000000 : ℝ)|=(50127321/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s0_3 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4096745133/10000000000 : ℝ)*x 0 + (615907451/2000000000 : ℝ)*x 1 + (213684131/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4096745133/10000000000 : ℝ)^4867 ≤ (8074395527377/25000000000000 : ℝ)^3843 := by
    have hnat : (4096745133 : ℕ)^4867*25000000000000^3843 ≤ 8074395527377^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4096745133 10000000000 8074395527377 25000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (615907451/2000000000 : ℝ)^4867 ≤ (11250143766147/50000000000000 : ℝ)^3843 := by
    have hnat : (615907451 : ℕ)^4867*50000000000000^3843 ≤ 11250143766147^3843*2000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615907451 2000000000 11250143766147 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (213684131/400000000 : ℝ)^4867 ≤ (45202130339253/100000000000000 : ℝ)^3843 := by
    have hnat : (213684131 : ℕ)^4867*100000000000000^3843 ≤ 45202130339253^3843*400000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213684131 400000000 45202130339253 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4096745133/10000000000 : ℝ), (615907451/2000000000 : ℝ), (213684131/400000000 : ℝ)] ![(8074395527377/25000000000000 : ℝ), (11250143766147/50000000000000 : ℝ), (45202130339253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4096745133/10000000000 : ℝ)|^4867 ≤ (8074395527377/25000000000000 : ℝ)^3843
        have hw : |(4096745133/10000000000 : ℝ)|=(4096745133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(615907451/2000000000 : ℝ)|^4867 ≤ (11250143766147/50000000000000 : ℝ)^3843
        have hw : |(615907451/2000000000 : ℝ)|=(615907451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(213684131/400000000 : ℝ)|^4867 ≤ (45202130339253/100000000000000 : ℝ)^3843
        have hw : |(213684131/400000000 : ℝ)|=(213684131/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s0_4 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-759096329/5000000000 : ℝ)*x 0 + (493479293/1000000000 : ℝ)*x 1 + (1444664091/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (759096329/5000000000 : ℝ)^4867 ≤ (1837445540761/20000000000000 : ℝ)^3843 := by
    have hnat : (759096329 : ℕ)^4867*20000000000000^3843 ≤ 1837445540761^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      759096329 5000000000 1837445540761 20000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (493479293/1000000000 : ℝ)^4867 ≤ (40882536702031/100000000000000 : ℝ)^3843 := by
    have hnat : (493479293 : ℕ)^4867*100000000000000^3843 ≤ 40882536702031^3843*1000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493479293 1000000000 40882536702031 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1444664091/2500000000 : ℝ)^4867 ≤ (49930235576423/100000000000000 : ℝ)^3843 := by
    have hnat : (1444664091 : ℕ)^4867*100000000000000^3843 ≤ 49930235576423^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1444664091 2500000000 49930235576423 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-759096329/5000000000 : ℝ), (493479293/1000000000 : ℝ), (1444664091/2500000000 : ℝ)] ![(1837445540761/20000000000000 : ℝ), (40882536702031/100000000000000 : ℝ), (49930235576423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-759096329/5000000000 : ℝ)|^4867 ≤ (1837445540761/20000000000000 : ℝ)^3843
        have hw : |(-759096329/5000000000 : ℝ)|=(759096329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(493479293/1000000000 : ℝ)|^4867 ≤ (40882536702031/100000000000000 : ℝ)^3843
        have hw : |(493479293/1000000000 : ℝ)|=(493479293/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1444664091/2500000000 : ℝ)|^4867 ≤ (49930235576423/100000000000000 : ℝ)^3843
        have hw : |(1444664091/2500000000 : ℝ)|=(1444664091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s0_5 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (130000781/250000000 : ℝ)*x 0 + (-284755949/2500000000 : ℝ)*x 1 + (5778656613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130000781/250000000 : ℝ)^4867 ≤ (8737019835839/20000000000000 : ℝ)^3843 := by
    have hnat : (130000781 : ℕ)^4867*20000000000000^3843 ≤ 8737019835839^3843*250000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130000781 250000000 8737019835839 20000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284755949/2500000000 : ℝ)^4867 ≤ (6384662507267/100000000000000 : ℝ)^3843 := by
    have hnat : (284755949 : ℕ)^4867*100000000000000^3843 ≤ 6384662507267^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284755949 2500000000 6384662507267 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5778656613/10000000000 : ℝ)^4867 ≤ (1997209532047/4000000000000 : ℝ)^3843 := by
    have hnat : (5778656613 : ℕ)^4867*4000000000000^3843 ≤ 1997209532047^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5778656613 10000000000 1997209532047 4000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(130000781/250000000 : ℝ), (-284755949/2500000000 : ℝ), (5778656613/10000000000 : ℝ)] ![(8737019835839/20000000000000 : ℝ), (6384662507267/100000000000000 : ℝ), (1997209532047/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(130000781/250000000 : ℝ)|^4867 ≤ (8737019835839/20000000000000 : ℝ)^3843
        have hw : |(130000781/250000000 : ℝ)|=(130000781/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-284755949/2500000000 : ℝ)|^4867 ≤ (6384662507267/100000000000000 : ℝ)^3843
        have hw : |(-284755949/2500000000 : ℝ)|=(284755949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5778656613/10000000000 : ℝ)|^4867 ≤ (1997209532047/4000000000000 : ℝ)^3843
        have hw : |(5778656613/10000000000 : ℝ)|=(5778656613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s0_6 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1300007783/2500000000 : ℝ)*x 0 + (1155731339/2000000000 : ℝ)*x 1 + (-142377979/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1300007783/2500000000 : ℝ)^4867 ≤ (5460637253767/12500000000000 : ℝ)^3843 := by
    have hnat : (1300007783 : ℕ)^4867*12500000000000^3843 ≤ 5460637253767^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300007783 2500000000 5460637253767 12500000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1155731339/2000000000 : ℝ)^4867 ≤ (49930239198483/100000000000000 : ℝ)^3843 := by
    have hnat : (1155731339 : ℕ)^4867*100000000000000^3843 ≤ 49930239198483^3843*2000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155731339 2000000000 49930239198483 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (142377979/1250000000 : ℝ)^4867 ≤ (638466276283/10000000000000 : ℝ)^3843 := by
    have hnat : (142377979 : ℕ)^4867*10000000000000^3843 ≤ 638466276283^3843*1250000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142377979 1250000000 638466276283 10000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1300007783/2500000000 : ℝ), (1155731339/2000000000 : ℝ), (-142377979/1250000000 : ℝ)] ![(5460637253767/12500000000000 : ℝ), (49930239198483/100000000000000 : ℝ), (638466276283/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1300007783/2500000000 : ℝ)|^4867 ≤ (5460637253767/12500000000000 : ℝ)^3843
        have hw : |(1300007783/2500000000 : ℝ)|=(1300007783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1155731339/2000000000 : ℝ)|^4867 ≤ (49930239198483/100000000000000 : ℝ)^3843
        have hw : |(1155731339/2000000000 : ℝ)|=(1155731339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-142377979/1250000000 : ℝ)|^4867 ≤ (638466276283/10000000000000 : ℝ)^3843
        have hw : |(-142377979/1250000000 : ℝ)|=(142377979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s0_7 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4102976437/10000000000 : ℝ)*x 0 + (5285590843/10000000000 : ℝ)*x 1 + (627603837/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4102976437/10000000000 : ℝ)^4867 ≤ (16179905276079/50000000000000 : ℝ)^3843 := by
    have hnat : (4102976437 : ℕ)^4867*50000000000000^3843 ≤ 16179905276079^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4102976437 10000000000 16179905276079 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5285590843/10000000000 : ℝ)^4867 ≤ (44597392048877/100000000000000 : ℝ)^3843 := by
    have hnat : (5285590843 : ℕ)^4867*100000000000000^3843 ≤ 44597392048877^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285590843 10000000000 44597392048877 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627603837/2000000000 : ℝ)^4867 ≤ (5760699346931/25000000000000 : ℝ)^3843 := by
    have hnat : (627603837 : ℕ)^4867*25000000000000^3843 ≤ 5760699346931^3843*2000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627603837 2000000000 5760699346931 25000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4102976437/10000000000 : ℝ), (5285590843/10000000000 : ℝ), (627603837/2000000000 : ℝ)] ![(16179905276079/50000000000000 : ℝ), (44597392048877/100000000000000 : ℝ), (5760699346931/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4102976437/10000000000 : ℝ)|^4867 ≤ (16179905276079/50000000000000 : ℝ)^3843
        have hw : |(4102976437/10000000000 : ℝ)|=(4102976437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5285590843/10000000000 : ℝ)|^4867 ≤ (44597392048877/100000000000000 : ℝ)^3843
        have hw : |(5285590843/10000000000 : ℝ)|=(5285590843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(627603837/2000000000 : ℝ)|^4867 ≤ (5760699346931/25000000000000 : ℝ)^3843
        have hw : |(627603837/2000000000 : ℝ)|=(627603837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1637_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11077897/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4587/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23637/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4863/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4863 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4863*1^1024 ≤ 0^1024*1^4863 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4863 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4863/1024 : ℝ) ≤ (257752904447667401/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4863 ≤ (257752904447667401/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4863*20000000000000000000^1024 ≤ 257752904447667401^1024*5^4863 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 257752904447667401 20000000000000000000 4863 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (257752904447667401/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4863/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4863 := by
      have hnat : (1 : ℕ)^1024*1^4863 ≤ 1^4863*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4863 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20257752904447667401/20000000000000000000 : ℝ) ≤ (10027000468767363/10000000000000000 : ℝ) ^ (4863/1024 : ℝ) := by
    have hpowers : (20257752904447667401/20000000000000000000 : ℝ)^1024 ≤ (10027000468767363/10000000000000000 : ℝ)^4863 := by
      have hnat : (20257752904447667401 : ℕ)^1024*10000000000000000^4863 ≤ 10027000468767363^4863*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20257752904447667401 20000000000000000000 10027000468767363 10000000000000000 1024 4863 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10027000468767363/10000000000000000 : ℝ)) (X := (20257752904447667401/20000000000000000000 : ℝ)) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10257752904447667401/10000000000000000000 : ℝ) ≤ (5027000468767363/5000000000000000 : ℝ) ^ (4863/1024 : ℝ) := by
    have hpowers : (10257752904447667401/10000000000000000000 : ℝ)^1024 ≤ (5027000468767363/5000000000000000 : ℝ)^4863 := by
      have hnat : (10257752904447667401 : ℕ)^1024*5000000000000000^4863 ≤ 5027000468767363^4863*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10257752904447667401 10000000000000000000 5027000468767363 5000000000000000 1024 4863 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5027000468767363/5000000000000000 : ℝ)) (X := (10257752904447667401/10000000000000000000 : ℝ)) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(27000468767363/4000000000000000 : ℝ)*(0 : ℝ))^(4863/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27000468767363/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(257752904447667401/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(27000468767363/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4863/1024 : ℝ) := by
    rw [show (1 : ℝ)+(27000468767363/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10027000468767363/10000000000000000 : ℝ) by norm_num, show 1+(257752904447667401/20000000000000000000 : ℝ)+(0 : ℝ)=(20257752904447667401/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(257752904447667401/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(27000468767363/4000000000000000 : ℝ)*(2/5 : ℝ))^(4863/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27000468767363/4000000000000000 : ℝ)*(2/5 : ℝ)=(5027000468767363/5000000000000000 : ℝ) by norm_num, show 1+2*(257752904447667401/20000000000000000000 : ℝ)=(10257752904447667401/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(27000468767363/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4863/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27000468767363/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(27000468767363/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4863/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27000468767363/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(27000468767363/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4863/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27000468767363/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-94734043/625000000 : ℝ)*X 0 0+(1450409271/2500000000 : ℝ)*X 0 1+(2456293331/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((544272531/1000000000 : ℝ)*X 1 0+(-501273239/2500000000 : ℝ)*X 1 1+(982517661/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5442726833/10000000000 : ℝ)*X 2 0+(307036677/625000000 : ℝ)*X 2 1+(-50127321/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4096745133/10000000000 : ℝ)*X 0 0+(615907451/2000000000 : ℝ)*X 0 1+(213684131/400000000 : ℝ)*X 0 2+(4096745133/10000000000 : ℝ)*X 1 0+(615907451/2000000000 : ℝ)*X 1 1+(213684131/400000000 : ℝ)*X 1 2+(4096745133/10000000000 : ℝ)*X 2 0+(615907451/2000000000 : ℝ)*X 2 1+(213684131/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-759096329/5000000000 : ℝ)*X 0 0+(493479293/1000000000 : ℝ)*X 0 1+(1444664091/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((130000781/250000000 : ℝ)*X 1 0+(-284755949/2500000000 : ℝ)*X 1 1+(5778656613/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1300007783/2500000000 : ℝ)*X 2 0+(1155731339/2000000000 : ℝ)*X 2 1+(-142377979/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4102976437/10000000000 : ℝ)*X 0 0+(5285590843/10000000000 : ℝ)*X 0 1+(627603837/2000000000 : ℝ)*X 0 2+(4102976437/10000000000 : ℝ)*X 1 0+(5285590843/10000000000 : ℝ)*X 1 1+(627603837/2000000000 : ℝ)*X 1 2+(4102976437/10000000000 : ℝ)*X 2 0+(5285590843/10000000000 : ℝ)*X 2 1+(627603837/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (367402713963802613451693/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1576287929/100000000000000 : ℝ)*(base19) + (187510589/10000000000000 : ℝ)*(base23) + (45656309/25000000000000 : ℝ)*(upper3) + (8670229/100000000000000 : ℝ)*(upper4) + (287238713/100000000000000 : ℝ)*(upper5) + (783397477650363/100000000000000 : ℝ)*(major0) + (783397477650363/100000000000000 : ℝ)*(major1) + (783397477650363/100000000000000 : ℝ)*(major2) + (224960615809677/20000000000000 : ℝ)*(sp0) + (562405393639381/50000000000000 : ℝ)*(sp1) + (1124810488460801/100000000000000 : ℝ)*(sp2) + (220989579989779/50000000000000 : ℝ)*(sp3) + (4642259153/50000000000000 : ℝ)*(sp4) + (1562792771/50000000000000 : ℝ)*(sp7) + (4419822855651/1000000000000 : ℝ)*(f.failure) + (1124812363566691/100000000000000 : ℝ)*(f.sum) + (704944331502769/200000000000000000000000000000 : ℝ)*base65 + (2196607653102769/400000000000000000000000000000 : ℝ)*base67 + (949794290097231/400000000000000000000000000000 : ℝ)*base70 + (2686919584302769/400000000000000000000000000000 : ℝ)*base71 + (857367154702769/200000000000000000000000000000 : ℝ)*base73 + (837790447502769/400000000000000000000000000000 : ℝ)*base75 + (883516779102769/400000000000000000000000000000 : ℝ)*base77 + (2120573048302769/400000000000000000000000000000 : ℝ)*base79 + (345269923502769/200000000000000000000000000000 : ℝ)*base81 + (41553/6250000000000000000 : ℝ)*base90 + (41553/6250000000000000000 : ℝ)*base92 + (41553/6250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (399620441325524937211737/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (407134931/25000000000000 : ℝ)*(base19) + (64873787/4000000000000 : ℝ)*(base23) + (29188869/25000000000000 : ℝ)*(base32) + (57614443/20000000000000 : ℝ)*(upper3) + (45089967/25000000000000 : ℝ)*(upper5) + (825333636325233/100000000000000 : ℝ)*(major0) + (825333636325233/100000000000000 : ℝ)*(major1) + (825333636325233/100000000000000 : ℝ)*(major2) + (61902947/1250000000000 : ℝ)*(sp1) + (5336090827/100000000000000 : ℝ)*(sp2) + (29625622646061/2500000000000 : ℝ)*(sp4) + (1185018325066957/100000000000000 : ℝ)*(sp5) + (592508973953469/50000000000000 : ℝ)*(sp6) + (232820991819457/50000000000000 : ℝ)*(sp7) + (465642100394389/100000000000000 : ℝ)*(f.failure) + (29625622646061/2500000000000 : ℝ)*(f.sum) + (402712295829421/200000000000000000000000000000 : ℝ)*base66 + (1718744997029421/400000000000000000000000000000 : ℝ)*base68 + (413639183770579/400000000000000000000000000000 : ℝ)*base69 + (1289256195429421/400000000000000000000000000000 : ℝ)*base72 + (1116269350229421/200000000000000000000000000000 : ℝ)*base74 + (2077294928629421/400000000000000000000000000000 : ℝ)*base76 + (412330833770579/400000000000000000000000000000 : ℝ)*base77 + (2111101306629421/400000000000000000000000000000 : ℝ)*base80 + (521027515029421/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (5530067/625000000000000000000 : ℝ)*base90 + (5530067/625000000000000000000 : ℝ)*base92 + (5530067/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1637_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11077897/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4587/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23637/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1637_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1637_s1_0 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-325419429/2000000000 : ℝ)*x 0 + (5506394911/10000000000 : ℝ)*x 1 + (2567786741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (325419429/2000000000 : ℝ)^4867 ≤ (10029699141589/100000000000000 : ℝ)^3843 := by
    have hnat : (325419429 : ℕ)^4867*100000000000000^3843 ≤ 10029699141589^3843*2000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325419429 2000000000 10029699141589 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5506394911/10000000000 : ℝ)^4867 ≤ (46969859422789/100000000000000 : ℝ)^3843 := by
    have hnat : (5506394911 : ℕ)^4867*100000000000000^3843 ≤ 46969859422789^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506394911 10000000000 46969859422789 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2567786741/5000000000 : ℝ)^4867 ≤ (43000441431019/100000000000000 : ℝ)^3843 := by
    have hnat : (2567786741 : ℕ)^4867*100000000000000^3843 ≤ 43000441431019^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567786741 5000000000 43000441431019 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-325419429/2000000000 : ℝ), (5506394911/10000000000 : ℝ), (2567786741/5000000000 : ℝ)] ![(10029699141589/100000000000000 : ℝ), (46969859422789/100000000000000 : ℝ), (43000441431019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-325419429/2000000000 : ℝ)|^4867 ≤ (10029699141589/100000000000000 : ℝ)^3843
        have hw : |(-325419429/2000000000 : ℝ)|=(325419429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5506394911/10000000000 : ℝ)|^4867 ≤ (46969859422789/100000000000000 : ℝ)^3843
        have hw : |(5506394911/10000000000 : ℝ)|=(5506394911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2567786741/5000000000 : ℝ)|^4867 ≤ (43000441431019/100000000000000 : ℝ)^3843
        have hw : |(2567786741/5000000000 : ℝ)|=(2567786741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s1_1 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2682098359/5000000000 : ℝ)*x 0 + (-182022223/1000000000 : ℝ)*x 1 + (2567786633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682098359/5000000000 : ℝ)^4867 ≤ (45439016655587/100000000000000 : ℝ)^3843 := by
    have hnat : (2682098359 : ℕ)^4867*100000000000000^3843 ≤ 45439016655587^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682098359 5000000000 45439016655587 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182022223/1000000000 : ℝ)^4867 ≤ (11560544191057/100000000000000 : ℝ)^3843 := by
    have hnat : (182022223 : ℕ)^4867*100000000000000^3843 ≤ 11560544191057^3843*1000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182022223 1000000000 11560544191057 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2567786633/5000000000 : ℝ)^4867 ≤ (43000439140527/100000000000000 : ℝ)^3843 := by
    have hnat : (2567786633 : ℕ)^4867*100000000000000^3843 ≤ 43000439140527^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567786633 5000000000 43000439140527 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682098359/5000000000 : ℝ), (-182022223/1000000000 : ℝ), (2567786633/5000000000 : ℝ)] ![(45439016655587/100000000000000 : ℝ), (11560544191057/100000000000000 : ℝ), (43000439140527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682098359/5000000000 : ℝ)|^4867 ≤ (45439016655587/100000000000000 : ℝ)^3843
        have hw : |(2682098359/5000000000 : ℝ)|=(2682098359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-182022223/1000000000 : ℝ)|^4867 ≤ (11560544191057/100000000000000 : ℝ)^3843
        have hw : |(-182022223/1000000000 : ℝ)|=(182022223/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2567786633/5000000000 : ℝ)|^4867 ≤ (43000439140527/100000000000000 : ℝ)^3843
        have hw : |(2567786633/5000000000 : ℝ)|=(2567786633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s1_2 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167631179/312500000 : ℝ)*x 0 + (513557207/1000000000 : ℝ)*x 1 + (-91011123/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167631179/312500000 : ℝ)^4867 ≤ (22719513745389/50000000000000 : ℝ)^3843 := by
    have hnat : (167631179 : ℕ)^4867*50000000000000^3843 ≤ 22719513745389^3843*312500000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167631179 312500000 22719513745389 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513557207/1000000000 : ℝ)^4867 ≤ (5375053307249/12500000000000 : ℝ)^3843 := by
    have hnat : (513557207 : ℕ)^4867*12500000000000^3843 ≤ 5375053307249^3843*1000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513557207 1000000000 5375053307249 12500000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91011123/500000000 : ℝ)^4867 ≤ (11560546041061/100000000000000 : ℝ)^3843 := by
    have hnat : (91011123 : ℕ)^4867*100000000000000^3843 ≤ 11560546041061^3843*500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91011123 500000000 11560546041061 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167631179/312500000 : ℝ), (513557207/1000000000 : ℝ), (-91011123/500000000 : ℝ)] ![(22719513745389/50000000000000 : ℝ), (5375053307249/12500000000000 : ℝ), (11560546041061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167631179/312500000 : ℝ)|^4867 ≤ (22719513745389/50000000000000 : ℝ)^3843
        have hw : |(167631179/312500000 : ℝ)|=(167631179/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(513557207/1000000000 : ℝ)|^4867 ≤ (5375053307249/12500000000000 : ℝ)^3843
        have hw : |(513557207/1000000000 : ℝ)|=(513557207/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-91011123/500000000 : ℝ)|^4867 ≤ (11560546041061/100000000000000 : ℝ)^3843
        have hw : |(-91011123/500000000 : ℝ)|=(91011123/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s1_3 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (522791753/1250000000 : ℝ)*x 0 + (3730105251/10000000000 : ℝ)*x 1 + (467382067/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522791753/1250000000 : ℝ)^4867 ≤ (16577251238483/50000000000000 : ℝ)^3843 := by
    have hnat : (522791753 : ℕ)^4867*50000000000000^3843 ≤ 16577251238483^3843*1250000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522791753 1250000000 16577251238483 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3730105251/10000000000 : ℝ)^4867 ≤ (14340772142557/50000000000000 : ℝ)^3843 := by
    have hnat : (3730105251 : ℕ)^4867*50000000000000^3843 ≤ 14340772142557^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3730105251 10000000000 14340772142557 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467382067/1000000000 : ℝ)^4867 ≤ (7632790643863/20000000000000 : ℝ)^3843 := by
    have hnat : (467382067 : ℕ)^4867*20000000000000^3843 ≤ 7632790643863^3843*1000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467382067 1000000000 7632790643863 20000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522791753/1250000000 : ℝ), (3730105251/10000000000 : ℝ), (467382067/1000000000 : ℝ)] ![(16577251238483/50000000000000 : ℝ), (14340772142557/50000000000000 : ℝ), (7632790643863/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522791753/1250000000 : ℝ)|^4867 ≤ (16577251238483/50000000000000 : ℝ)^3843
        have hw : |(522791753/1250000000 : ℝ)|=(522791753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3730105251/10000000000 : ℝ)|^4867 ≤ (14340772142557/50000000000000 : ℝ)^3843
        have hw : |(3730105251/10000000000 : ℝ)|=(3730105251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(467382067/1000000000 : ℝ)|^4867 ≤ (7632790643863/20000000000000 : ℝ)^3843
        have hw : |(467382067/1000000000 : ℝ)|=(467382067/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s1_4 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-406818039/2500000000 : ℝ)*x 0 + (2569708271/5000000000 : ℝ)*x 1 + (687811921/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (406818039/2500000000 : ℝ)^4867 ≤ (2507766353229/25000000000000 : ℝ)^3843 := by
    have hnat : (406818039 : ℕ)^4867*25000000000000^3843 ≤ 2507766353229^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406818039 2500000000 2507766353229 25000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569708271/5000000000 : ℝ)^4867 ≤ (43041197790237/100000000000000 : ℝ)^3843 := by
    have hnat : (2569708271 : ℕ)^4867*100000000000000^3843 ≤ 43041197790237^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569708271 5000000000 43041197790237 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (687811921/1250000000 : ℝ)^4867 ≤ (9385547356303/20000000000000 : ℝ)^3843 := by
    have hnat : (687811921 : ℕ)^4867*20000000000000^3843 ≤ 9385547356303^3843*1250000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687811921 1250000000 9385547356303 20000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-406818039/2500000000 : ℝ), (2569708271/5000000000 : ℝ), (687811921/1250000000 : ℝ)] ![(2507766353229/25000000000000 : ℝ), (43041197790237/100000000000000 : ℝ), (9385547356303/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-406818039/2500000000 : ℝ)|^4867 ≤ (2507766353229/25000000000000 : ℝ)^3843
        have hw : |(-406818039/2500000000 : ℝ)|=(406818039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569708271/5000000000 : ℝ)|^4867 ≤ (43041197790237/100000000000000 : ℝ)^3843
        have hw : |(2569708271/5000000000 : ℝ)|=(2569708271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(687811921/1250000000 : ℝ)|^4867 ≤ (9385547356303/20000000000000 : ℝ)^3843
        have hw : |(687811921/1250000000 : ℝ)|=(687811921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s1_5 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053037987/2000000000 : ℝ)*x 0 + (-726649893/5000000000 : ℝ)*x 1 + (5502495359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053037987/2000000000 : ℝ)^4867 ≤ (11094876078293/25000000000000 : ℝ)^3843 := by
    have hnat : (1053037987 : ℕ)^4867*25000000000000^3843 ≤ 11094876078293^3843*2000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053037987 2000000000 11094876078293 25000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (726649893/5000000000 : ℝ)^4867 ≤ (4346379492829/50000000000000 : ℝ)^3843 := by
    have hnat : (726649893 : ℕ)^4867*50000000000000^3843 ≤ 4346379492829^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726649893 5000000000 4346379492829 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5502495359/10000000000 : ℝ)^4867 ≤ (46927736684307/100000000000000 : ℝ)^3843 := by
    have hnat : (5502495359 : ℕ)^4867*100000000000000^3843 ≤ 46927736684307^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502495359 10000000000 46927736684307 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053037987/2000000000 : ℝ), (-726649893/5000000000 : ℝ), (5502495359/10000000000 : ℝ)] ![(11094876078293/25000000000000 : ℝ), (4346379492829/50000000000000 : ℝ), (46927736684307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053037987/2000000000 : ℝ)|^4867 ≤ (11094876078293/25000000000000 : ℝ)^3843
        have hw : |(1053037987/2000000000 : ℝ)|=(1053037987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-726649893/5000000000 : ℝ)|^4867 ≤ (4346379492829/50000000000000 : ℝ)^3843
        have hw : |(-726649893/5000000000 : ℝ)|=(726649893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5502495359/10000000000 : ℝ)|^4867 ≤ (46927736684307/100000000000000 : ℝ)^3843
        have hw : |(5502495359/10000000000 : ℝ)|=(5502495359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s1_6 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263259491/500000000 : ℝ)*x 0 + (2751247769/5000000000 : ℝ)*x 1 + (-363324923/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263259491/500000000 : ℝ)^4867 ≤ (44379503085571/100000000000000 : ℝ)^3843 := by
    have hnat : (263259491 : ℕ)^4867*100000000000000^3843 ≤ 44379503085571^3843*500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263259491 500000000 44379503085571 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2751247769/5000000000 : ℝ)^4867 ≤ (5865967327209/12500000000000 : ℝ)^3843 := by
    have hnat : (2751247769 : ℕ)^4867*12500000000000^3843 ≤ 5865967327209^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751247769 5000000000 5865967327209 12500000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (363324923/2500000000 : ℝ)^4867 ≤ (869275827359/10000000000000 : ℝ)^3843 := by
    have hnat : (363324923 : ℕ)^4867*10000000000000^3843 ≤ 869275827359^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363324923 2500000000 869275827359 10000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263259491/500000000 : ℝ), (2751247769/5000000000 : ℝ), (-363324923/2500000000 : ℝ)] ![(44379503085571/100000000000000 : ℝ), (5865967327209/12500000000000 : ℝ), (869275827359/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263259491/500000000 : ℝ)|^4867 ≤ (44379503085571/100000000000000 : ℝ)^3843
        have hw : |(263259491/500000000 : ℝ)|=(263259491/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2751247769/5000000000 : ℝ)|^4867 ≤ (5865967327209/12500000000000 : ℝ)^3843
        have hw : |(2751247769/5000000000 : ℝ)|=(2751247769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-363324923/2500000000 : ℝ)|^4867 ≤ (869275827359/10000000000000 : ℝ)^3843
        have hw : |(-363324923/2500000000 : ℝ)|=(363324923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s1_7 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4182776409/10000000000 : ℝ)*x 0 + (2332019567/5000000000 : ℝ)*x 1 + (3740030151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4182776409/10000000000 : ℝ)^4867 ≤ (16579471945573/50000000000000 : ℝ)^3843 := by
    have hnat : (4182776409 : ℕ)^4867*50000000000000^3843 ≤ 16579471945573^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4182776409 10000000000 16579471945573 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2332019567/5000000000 : ℝ)^4867 ≤ (38062828307139/100000000000000 : ℝ)^3843 := by
    have hnat : (2332019567 : ℕ)^4867*100000000000000^3843 ≤ 38062828307139^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2332019567 5000000000 38062828307139 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3740030151/10000000000 : ℝ)^4867 ≤ (14389113893501/50000000000000 : ℝ)^3843 := by
    have hnat : (3740030151 : ℕ)^4867*50000000000000^3843 ≤ 14389113893501^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3740030151 10000000000 14389113893501 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4182776409/10000000000 : ℝ), (2332019567/5000000000 : ℝ), (3740030151/10000000000 : ℝ)] ![(16579471945573/50000000000000 : ℝ), (38062828307139/100000000000000 : ℝ), (14389113893501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4182776409/10000000000 : ℝ)|^4867 ≤ (16579471945573/50000000000000 : ℝ)^3843
        have hw : |(4182776409/10000000000 : ℝ)|=(4182776409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2332019567/5000000000 : ℝ)|^4867 ≤ (38062828307139/100000000000000 : ℝ)^3843
        have hw : |(2332019567/5000000000 : ℝ)|=(2332019567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3740030151/10000000000 : ℝ)|^4867 ≤ (14389113893501/50000000000000 : ℝ)^3843
        have hw : |(3740030151/10000000000 : ℝ)|=(3740030151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1637_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11077897/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23637/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4587/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2393/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4361/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23637/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4587/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23637/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4587/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23637/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4587/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23637/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4587/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23637/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4587/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23637/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4587/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4587/100000 : ℝ) ^ (4863/1024 : ℝ) ≤ (44011747881557/100000000000000000000 : ℝ) := by
    have hpowers : (4587/100000 : ℝ)^4863 ≤ (44011747881557/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4587 : ℕ)^4863*100000000000000000000^1024 ≤ 44011747881557^1024*100000^4863 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4587 100000 44011747881557 100000000000000000000 4863 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4587/100000 : ℝ)) (X := (44011747881557/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23637/100000 : ℝ) ^ (4863/1024 : ℝ) ≤ (105968164873053537/100000000000000000000 : ℝ) := by
    have hpowers : (23637/100000 : ℝ)^4863 ≤ (105968164873053537/100000000000000000000 : ℝ)^1024 := by
      have hnat : (23637 : ℕ)^4863*100000000000000000000^1024 ≤ 105968164873053537^1024*100000^4863 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23637 100000 105968164873053537 100000000000000000000 4863 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23637/100000 : ℝ)) (X := (105968164873053537/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000044011747881557/50000000000000000000 : ℝ) ≤ (200000037070133/200000000000000 : ℝ) ^ (4863/1024 : ℝ) := by
    have hpowers : (50000044011747881557/50000000000000000000 : ℝ)^1024 ≤ (200000037070133/200000000000000 : ℝ)^4863 := by
      have hnat : (50000044011747881557 : ℕ)^1024*200000000000000^4863 ≤ 200000037070133^4863*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000044011747881557 50000000000000000000 200000037070133 200000000000000 1024 4863 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200000037070133/200000000000000 : ℝ)) (X := (50000044011747881557/50000000000000000000 : ℝ)) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50053006088310467547/50000000000000000000 : ℝ) ≤ (5001115680367303/5000000000000000 : ℝ) ^ (4863/1024 : ℝ) := by
    have hpowers : (50053006088310467547/50000000000000000000 : ℝ)^1024 ≤ (5001115680367303/5000000000000000 : ℝ)^4863 := by
      have hnat : (50053006088310467547 : ℕ)^1024*5000000000000000^4863 ≤ 5001115680367303^4863*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50053006088310467547 50000000000000000000 5001115680367303 5000000000000000 1024 4863 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001115680367303/5000000000000000 : ℝ)) (X := (50053006088310467547/50000000000000000000 : ℝ)) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50105968164873053537/50000000000000000000 : ℝ) ≤ (5002230433981281/5000000000000000 : ℝ) ^ (4863/1024 : ℝ) := by
    have hpowers : (50105968164873053537/50000000000000000000 : ℝ)^1024 ≤ (5002230433981281/5000000000000000 : ℝ)^4863 := by
      have hnat : (50105968164873053537 : ℕ)^1024*5000000000000000^4863 ≤ 5002230433981281^4863*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50105968164873053537 50000000000000000000 5002230433981281 5000000000000000 1024 4863 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002230433981281/5000000000000000 : ℝ)) (X := (50105968164873053537/50000000000000000000 : ℝ)) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(44011747881557/100000000000000000000 : ℝ) ≤ ((15873298484166034513/15875000000000000000 : ℝ)+2*(557376806989/476250000000000 : ℝ)*(4587/100000 : ℝ))^(4863/1024 : ℝ) := by
    rw [show (15873298484166034513/15875000000000000000 : ℝ)+2*(557376806989/476250000000000 : ℝ)*(4587/100000 : ℝ)=(200000037070133/200000000000000 : ℝ) by norm_num, show 1+2*(44011747881557/100000000000000000000 : ℝ)=(50000044011747881557/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(105968164873053537/100000000000000000000 : ℝ)+(44011747881557/100000000000000000000 : ℝ) ≤ ((15873298484166034513/15875000000000000000 : ℝ)+(557376806989/476250000000000 : ℝ)*((23637/100000 : ℝ)+(4587/100000 : ℝ)))^(4863/1024 : ℝ) := by
    rw [show (15873298484166034513/15875000000000000000 : ℝ)+(557376806989/476250000000000 : ℝ)*((23637/100000 : ℝ)+(4587/100000 : ℝ))=(5001115680367303/5000000000000000 : ℝ) by norm_num, show 1+(105968164873053537/100000000000000000000 : ℝ)+(44011747881557/100000000000000000000 : ℝ)=(50053006088310467547/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(105968164873053537/100000000000000000000 : ℝ) ≤ ((15873298484166034513/15875000000000000000 : ℝ)+2*(557376806989/476250000000000 : ℝ)*(23637/100000 : ℝ))^(4863/1024 : ℝ) := by
    rw [show (15873298484166034513/15875000000000000000 : ℝ)+2*(557376806989/476250000000000 : ℝ)*(23637/100000 : ℝ)=(5002230433981281/5000000000000000 : ℝ) by norm_num, show 1+2*(105968164873053537/100000000000000000000 : ℝ)=(50105968164873053537/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15873298484166034513/15875000000000000000 : ℝ)*(X 1 0+X 2 0)+(557376806989/476250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4863/1024 : ℝ)) (lo := (4587/100000 : ℝ)) (hi := (23637/100000 : ℝ)) (c := (15873298484166034513/15875000000000000000 : ℝ)) (alpha := (557376806989/476250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15873298484166034513/15875000000000000000 : ℝ)*(X 0 1+X 2 1)+(557376806989/476250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4863/1024 : ℝ)) (lo := (4587/100000 : ℝ)) (hi := (23637/100000 : ℝ)) (c := (15873298484166034513/15875000000000000000 : ℝ)) (alpha := (557376806989/476250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15873298484166034513/15875000000000000000 : ℝ)*(X 0 2+X 1 2)+(557376806989/476250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4863/1024 : ℝ)) (lo := (4587/100000 : ℝ)) (hi := (23637/100000 : ℝ)) (c := (15873298484166034513/15875000000000000000 : ℝ)) (alpha := (557376806989/476250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-325419429/2000000000 : ℝ)*X 0 0+(5506394911/10000000000 : ℝ)*X 0 1+(2567786741/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2682098359/5000000000 : ℝ)*X 1 0+(-182022223/1000000000 : ℝ)*X 1 1+(2567786633/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167631179/312500000 : ℝ)*X 2 0+(513557207/1000000000 : ℝ)*X 2 1+(-91011123/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((522791753/1250000000 : ℝ)*X 0 0+(3730105251/10000000000 : ℝ)*X 0 1+(467382067/1000000000 : ℝ)*X 0 2+(522791753/1250000000 : ℝ)*X 1 0+(3730105251/10000000000 : ℝ)*X 1 1+(467382067/1000000000 : ℝ)*X 1 2+(522791753/1250000000 : ℝ)*X 2 0+(3730105251/10000000000 : ℝ)*X 2 1+(467382067/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-406818039/2500000000 : ℝ)*X 0 0+(2569708271/5000000000 : ℝ)*X 0 1+(687811921/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1053037987/2000000000 : ℝ)*X 1 0+(-726649893/5000000000 : ℝ)*X 1 1+(5502495359/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((263259491/500000000 : ℝ)*X 2 0+(2751247769/5000000000 : ℝ)*X 2 1+(-363324923/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4182776409/10000000000 : ℝ)*X 0 0+(2332019567/5000000000 : ℝ)*X 0 1+(3740030151/10000000000 : ℝ)*X 0 2+(4182776409/10000000000 : ℝ)*X 1 0+(2332019567/5000000000 : ℝ)*X 1 1+(3740030151/10000000000 : ℝ)*X 1 2+(4182776409/10000000000 : ℝ)*X 2 0+(2332019567/5000000000 : ℝ)*X 2 1+(3740030151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36750660796372148158989233/3175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (587238603/100000000000000 : ℝ)*(base1) + (762822897/50000000000000 : ℝ)*(base19) + (1016699699/50000000000000 : ℝ)*(base23) + (2999091/1562500000000 : ℝ)*(upper3) + (33208261/25000000000000 : ℝ)*(upper5) + (7512745678853/400000000000 : ℝ)*(major0) + (7512745678853/400000000000 : ℝ)*(major1) + (7512745678853/400000000000 : ℝ)*(major2) + (337090052403963/12500000000000 : ℝ)*(sp0) + (337090436821891/12500000000000 : ℝ)*(sp1) + (674180746705381/25000000000000 : ℝ)*(sp2) + (132455456721127/12500000000000 : ℝ)*(sp3) + (5188227823/100000000000000 : ℝ)*(sp4) + (1596182119/50000000000000 : ℝ)*(sp7) + (1059647433371859/100000000000000 : ℝ)*(f.failure) + (2696725020220923/100000000000000 : ℝ)*(f.sum) + (109131993617/38100000000000000000000000 : ℝ)*base65 + (48877612009439233/19050000000000000000000000000000 : ℝ)*base68 + (33690830955960767/19050000000000000000000000000000 : ℝ)*base69 + (146514574446960767/19050000000000000000000000000000 : ℝ)*base71 + (21055588021/9525000000000000000000000 : ℝ)*base74 + (84687093149160767/19050000000000000000000000000000 : ℝ)*base75 + (135841477276560767/19050000000000000000000000000000 : ℝ)*base77 + (12738395552939233/19050000000000000000000000000000 : ℝ)*base80 + (93393212801/38100000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4200523/625000000000000000000 : ℝ)*base89 + (4200523/625000000000000000000 : ℝ)*base91 + (4200523/625000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1131739903279391860380249259/198437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1107488353/100000000000000 : ℝ)*(base19) + (539536953/50000000000000 : ℝ)*(base23) + (3139/31250000000 : ℝ)*(upper2) + (849663/625000000000 : ℝ)*(upper3) + (72222729/50000000000000 : ℝ)*(upper5) + (479557923601519/25000000000000 : ℝ)*(major0) + (479557923601519/25000000000000 : ℝ)*(major1) + (479557923601519/25000000000000 : ℝ)*(major2) + (9802312999/100000000000000 : ℝ)*(sp1) + (523784171/5000000000000 : ℝ)*(sp2) + (2754222761729151/100000000000000 : ℝ)*(sp4) + (1377105925963899/50000000000000 : ℝ)*(sp5) + (110168448278873/4000000000000 : ℝ)*(sp6) + (270560109243613/25000000000000 : ℝ)*(sp7) + (270560109243613/25000000000000 : ℝ)*(f.failure) + (2754222761729151/100000000000000 : ℝ)*(f.sum) + (29103892374541/5953125000000000000000000000 : ℝ)*base65 + (2185200282787474259/1190625000000000000000000000000000 : ℝ)*base68 + (6307582122806275741/1190625000000000000000000000000000 : ℝ)*base69 + (4031132768868775741/1190625000000000000000000000000000 : ℝ)*base71 + (41749490520461/23812500000000000000000000000 : ℝ)*base74 + (11928877973156275741/1190625000000000000000000000000000 : ℝ)*base75 + (8308761634218775741/1190625000000000000000000000000000 : ℝ)*base77 + (7299268518562474259/1190625000000000000000000000000000 : ℝ)*base80 + (29625220389541/5953125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1028139/156250000000000000000 : ℝ)*base90 + (1028139/156250000000000000000 : ℝ)*base92 + (1028139/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1637_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11077897/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23637/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4587/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2393/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4361/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1637_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1637_s2_0 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1637712301/10000000000 : ℝ)*x 0 + (5455855219/10000000000 : ℝ)*x 1 + (323695441/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1637712301/10000000000 : ℝ)^4867 ≤ (10112639992011/100000000000000 : ℝ)^3843 := by
    have hnat : (1637712301 : ℕ)^4867*100000000000000^3843 ≤ 10112639992011^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1637712301 10000000000 10112639992011 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5455855219/10000000000 : ℝ)^4867 ≤ (1160613754211/2500000000000 : ℝ)^3843 := by
    have hnat : (5455855219 : ℕ)^4867*2500000000000^3843 ≤ 1160613754211^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455855219 10000000000 1160613754211 2500000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323695441/625000000 : ℝ)^4867 ≤ (43462809825947/100000000000000 : ℝ)^3843 := by
    have hnat : (323695441 : ℕ)^4867*100000000000000^3843 ≤ 43462809825947^3843*625000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323695441 625000000 43462809825947 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1637712301/10000000000 : ℝ), (5455855219/10000000000 : ℝ), (323695441/625000000 : ℝ)] ![(10112639992011/100000000000000 : ℝ), (1160613754211/2500000000000 : ℝ), (43462809825947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1637712301/10000000000 : ℝ)|^4867 ≤ (10112639992011/100000000000000 : ℝ)^3843
        have hw : |(-1637712301/10000000000 : ℝ)|=(1637712301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5455855219/10000000000 : ℝ)|^4867 ≤ (1160613754211/2500000000000 : ℝ)^3843
        have hw : |(5455855219/10000000000 : ℝ)|=(5455855219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323695441/625000000 : ℝ)|^4867 ≤ (43462809825947/100000000000000 : ℝ)^3843
        have hw : |(323695441/625000000 : ℝ)|=(323695441/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s2_1 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070176189/2000000000 : ℝ)*x 0 + (-890187249/5000000000 : ℝ)*x 1 + (5179127777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070176189/2000000000 : ℝ)^4867 ≤ (5662026686377/12500000000000 : ℝ)^3843 := by
    have hnat : (1070176189 : ℕ)^4867*12500000000000^3843 ≤ 5662026686377^3843*2000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070176189 2000000000 5662026686377 12500000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (890187249/5000000000 : ℝ)^4867 ≤ (11240969006261/100000000000000 : ℝ)^3843 := by
    have hnat : (890187249 : ℕ)^4867*100000000000000^3843 ≤ 11240969006261^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890187249 5000000000 11240969006261 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179127777/10000000000 : ℝ)^4867 ≤ (21731408744373/50000000000000 : ℝ)^3843 := by
    have hnat : (5179127777 : ℕ)^4867*50000000000000^3843 ≤ 21731408744373^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179127777 10000000000 21731408744373 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070176189/2000000000 : ℝ), (-890187249/5000000000 : ℝ), (5179127777/10000000000 : ℝ)] ![(5662026686377/12500000000000 : ℝ), (11240969006261/100000000000000 : ℝ), (21731408744373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070176189/2000000000 : ℝ)|^4867 ≤ (5662026686377/12500000000000 : ℝ)^3843
        have hw : |(1070176189/2000000000 : ℝ)|=(1070176189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-890187249/5000000000 : ℝ)|^4867 ≤ (11240969006261/100000000000000 : ℝ)^3843
        have hw : |(-890187249/5000000000 : ℝ)|=(890187249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179127777/10000000000 : ℝ)|^4867 ≤ (21731408744373/50000000000000 : ℝ)^3843
        have hw : |(5179127777/10000000000 : ℝ)|=(5179127777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s2_2 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675441777/5000000000 : ℝ)*x 0 + (64739081/125000000 : ℝ)*x 1 + (-445093181/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675441777/5000000000 : ℝ)^4867 ≤ (45296241461609/100000000000000 : ℝ)^3843 := by
    have hnat : (2675441777 : ℕ)^4867*100000000000000^3843 ≤ 45296241461609^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675441777 5000000000 45296241461609 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64739081/125000000 : ℝ)^4867 ≤ (4346280370421/10000000000000 : ℝ)^3843 := by
    have hnat : (64739081 : ℕ)^4867*10000000000000^3843 ≤ 4346280370421^3843*125000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64739081 125000000 4346280370421 10000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (445093181/2500000000 : ℝ)^4867 ≤ (5620477410507/50000000000000 : ℝ)^3843 := by
    have hnat : (445093181 : ℕ)^4867*50000000000000^3843 ≤ 5620477410507^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445093181 2500000000 5620477410507 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675441777/5000000000 : ℝ), (64739081/125000000 : ℝ), (-445093181/2500000000 : ℝ)] ![(45296241461609/100000000000000 : ℝ), (4346280370421/10000000000000 : ℝ), (5620477410507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675441777/5000000000 : ℝ)|^4867 ≤ (45296241461609/100000000000000 : ℝ)^3843
        have hw : |(2675441777/5000000000 : ℝ)|=(2675441777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64739081/125000000 : ℝ)|^4867 ≤ (4346280370421/10000000000000 : ℝ)^3843
        have hw : |(64739081/125000000 : ℝ)|=(64739081/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-445093181/2500000000 : ℝ)|^4867 ≤ (5620477410507/50000000000000 : ℝ)^3843
        have hw : |(-445093181/2500000000 : ℝ)|=(445093181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s2_3 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2095110779/5000000000 : ℝ)*x 0 + (962257543/2500000000 : ℝ)*x 1 + (2276642041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095110779/5000000000 : ℝ)^4867 ≤ (6646741950047/20000000000000 : ℝ)^3843 := by
    have hnat : (2095110779 : ℕ)^4867*20000000000000^3843 ≤ 6646741950047^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095110779 5000000000 6646741950047 20000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (962257543/2500000000 : ℝ)^4867 ≤ (14922261796237/50000000000000 : ℝ)^3843 := by
    have hnat : (962257543 : ℕ)^4867*50000000000000^3843 ≤ 14922261796237^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962257543 2500000000 14922261796237 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2276642041/5000000000 : ℝ)^4867 ≤ (18460883318353/50000000000000 : ℝ)^3843 := by
    have hnat : (2276642041 : ℕ)^4867*50000000000000^3843 ≤ 18460883318353^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276642041 5000000000 18460883318353 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2095110779/5000000000 : ℝ), (962257543/2500000000 : ℝ), (2276642041/5000000000 : ℝ)] ![(6646741950047/20000000000000 : ℝ), (14922261796237/50000000000000 : ℝ), (18460883318353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2095110779/5000000000 : ℝ)|^4867 ≤ (6646741950047/20000000000000 : ℝ)^3843
        have hw : |(2095110779/5000000000 : ℝ)|=(2095110779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(962257543/2500000000 : ℝ)|^4867 ≤ (14922261796237/50000000000000 : ℝ)^3843
        have hw : |(962257543/2500000000 : ℝ)|=(962257543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2276642041/5000000000 : ℝ)|^4867 ≤ (18460883318353/50000000000000 : ℝ)^3843
        have hw : |(2276642041/5000000000 : ℝ)|=(2276642041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s2_4 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-327556767/2000000000 : ℝ)*x 0 + (1295318593/2500000000 : ℝ)*x 1 + (2726842669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327556767/2000000000 : ℝ)^4867 ≤ (10113199405501/100000000000000 : ℝ)^3843 := by
    have hnat : (327556767 : ℕ)^4867*100000000000000^3843 ≤ 10113199405501^3843*2000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327556767 2000000000 10113199405501 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295318593/2500000000 : ℝ)^4867 ≤ (5435704099383/12500000000000 : ℝ)^3843 := by
    have hnat : (1295318593 : ℕ)^4867*12500000000000^3843 ≤ 5435704099383^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295318593 2500000000 5435704099383 12500000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2726842669/5000000000 : ℝ)^4867 ≤ (23200583893763/50000000000000 : ℝ)^3843 := by
    have hnat : (2726842669 : ℕ)^4867*50000000000000^3843 ≤ 23200583893763^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726842669 5000000000 23200583893763 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-327556767/2000000000 : ℝ), (1295318593/2500000000 : ℝ), (2726842669/5000000000 : ℝ)] ![(10113199405501/100000000000000 : ℝ), (5435704099383/12500000000000 : ℝ), (23200583893763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-327556767/2000000000 : ℝ)|^4867 ≤ (10113199405501/100000000000000 : ℝ)^3843
        have hw : |(-327556767/2000000000 : ℝ)|=(327556767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295318593/2500000000 : ℝ)|^4867 ≤ (5435704099383/12500000000000 : ℝ)^3843
        have hw : |(1295318593/2500000000 : ℝ)|=(1295318593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2726842669/5000000000 : ℝ)|^4867 ≤ (23200583893763/50000000000000 : ℝ)^3843
        have hw : |(2726842669/5000000000 : ℝ)|=(2726842669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s2_5 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319267551/2500000000 : ℝ)*x 0 + (-1505814741/10000000000 : ℝ)*x 1 + (5453685549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319267551/2500000000 : ℝ)^4867 ≤ (44506361800501/100000000000000 : ℝ)^3843 := by
    have hnat : (1319267551 : ℕ)^4867*100000000000000^3843 ≤ 44506361800501^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319267551 2500000000 44506361800501 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1505814741/10000000000 : ℝ)^4867 ≤ (9092468112633/100000000000000 : ℝ)^3843 := by
    have hnat : (1505814741 : ℕ)^4867*100000000000000^3843 ≤ 9092468112633^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1505814741 10000000000 9092468112633 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453685549/10000000000 : ℝ)^4867 ≤ (46401170061117/100000000000000 : ℝ)^3843 := by
    have hnat : (5453685549 : ℕ)^4867*100000000000000^3843 ≤ 46401170061117^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453685549 10000000000 46401170061117 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319267551/2500000000 : ℝ), (-1505814741/10000000000 : ℝ), (5453685549/10000000000 : ℝ)] ![(44506361800501/100000000000000 : ℝ), (9092468112633/100000000000000 : ℝ), (46401170061117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319267551/2500000000 : ℝ)|^4867 ≤ (44506361800501/100000000000000 : ℝ)^3843
        have hw : |(1319267551/2500000000 : ℝ)|=(1319267551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1505814741/10000000000 : ℝ)|^4867 ≤ (9092468112633/100000000000000 : ℝ)^3843
        have hw : |(-1505814741/10000000000 : ℝ)|=(1505814741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453685549/10000000000 : ℝ)|^4867 ≤ (46401170061117/100000000000000 : ℝ)^3843
        have hw : |(5453685549/10000000000 : ℝ)|=(5453685549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s2_6 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20613559/39062500 : ℝ)*x 0 + (5453684663/10000000000 : ℝ)*x 1 + (-752907367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20613559/39062500 : ℝ)^4867 ≤ (2781648213349/6250000000000 : ℝ)^3843 := by
    have hnat : (20613559 : ℕ)^4867*6250000000000^3843 ≤ 2781648213349^3843*39062500^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20613559 39062500 2781648213349 6250000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453684663/10000000000 : ℝ)^4867 ≤ (2900072532137/6250000000000 : ℝ)^3843 := by
    have hnat : (5453684663 : ℕ)^4867*6250000000000^3843 ≤ 2900072532137^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453684663 10000000000 2900072532137 6250000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (752907367/5000000000 : ℝ)^4867 ≤ (9092468059103/100000000000000 : ℝ)^3843 := by
    have hnat : (752907367 : ℕ)^4867*100000000000000^3843 ≤ 9092468059103^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752907367 5000000000 9092468059103 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20613559/39062500 : ℝ), (5453684663/10000000000 : ℝ), (-752907367/5000000000 : ℝ)] ![(2781648213349/6250000000000 : ℝ), (2900072532137/6250000000000 : ℝ), (9092468059103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20613559/39062500 : ℝ)|^4867 ≤ (2781648213349/6250000000000 : ℝ)^3843
        have hw : |(20613559/39062500 : ℝ)|=(20613559/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453684663/10000000000 : ℝ)|^4867 ≤ (2900072532137/6250000000000 : ℝ)^3843
        have hw : |(5453684663/10000000000 : ℝ)|=(5453684663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-752907367/5000000000 : ℝ)|^4867 ≤ (9092468059103/100000000000000 : ℝ)^3843
        have hw : |(-752907367/5000000000 : ℝ)|=(752907367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s2_7 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (209520281/500000000 : ℝ)*x 0 + (4547821697/10000000000 : ℝ)*x 1 + (770910487/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209520281/500000000 : ℝ)^4867 ≤ (33235558590861/100000000000000 : ℝ)^3843 := by
    have hnat : (209520281 : ℕ)^4867*100000000000000^3843 ≤ 33235558590861^3843*500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209520281 500000000 33235558590861 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4547821697/10000000000 : ℝ)^4867 ≤ (36865679721343/100000000000000 : ℝ)^3843 := by
    have hnat : (4547821697 : ℕ)^4867*100000000000000^3843 ≤ 36865679721343^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4547821697 10000000000 36865679721343 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (770910487/2000000000 : ℝ)^4867 ≤ (3737345209879/12500000000000 : ℝ)^3843 := by
    have hnat : (770910487 : ℕ)^4867*12500000000000^3843 ≤ 3737345209879^3843*2000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770910487 2000000000 3737345209879 12500000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209520281/500000000 : ℝ), (4547821697/10000000000 : ℝ), (770910487/2000000000 : ℝ)] ![(33235558590861/100000000000000 : ℝ), (36865679721343/100000000000000 : ℝ), (3737345209879/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209520281/500000000 : ℝ)|^4867 ≤ (33235558590861/100000000000000 : ℝ)^3843
        have hw : |(209520281/500000000 : ℝ)|=(209520281/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4547821697/10000000000 : ℝ)|^4867 ≤ (36865679721343/100000000000000 : ℝ)^3843
        have hw : |(4547821697/10000000000 : ℝ)|=(4547821697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(770910487/2000000000 : ℝ)|^4867 ≤ (3737345209879/12500000000000 : ℝ)^3843
        have hw : |(770910487/2000000000 : ℝ)|=(770910487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1637_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11077897/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4361/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2393/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10513/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1639/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4361/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2393/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4361/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2393/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4361/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2393/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4361/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2393/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4361/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2393/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4361/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2393/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2393/25000 : ℝ) ^ (4863/1024 : ℝ) ≤ (1447964424865939/100000000000000000000 : ℝ) := by
    have hpowers : (2393/25000 : ℝ)^4863 ≤ (1447964424865939/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2393 : ℕ)^4863*100000000000000000000^1024 ≤ 1447964424865939^1024*25000^4863 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2393 25000 1447964424865939 100000000000000000000 4863 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2393/25000 : ℝ)) (X := (1447964424865939/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4361/25000 : ℝ) ^ (4863/1024 : ℝ) ≤ (25035683380334323/100000000000000000000 : ℝ) := by
    have hpowers : (4361/25000 : ℝ)^4863 ≤ (25035683380334323/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4361 : ℕ)^4863*100000000000000000000^1024 ≤ 25035683380334323^1024*25000^4863 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4361 25000 25035683380334323 100000000000000000000 4863 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4361/25000 : ℝ)) (X := (25035683380334323/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001447964424865939/50000000000000000000 : ℝ) ≤ (625003811172689/625000000000000 : ℝ) ^ (4863/1024 : ℝ) := by
    have hpowers : (50001447964424865939/50000000000000000000 : ℝ)^1024 ≤ (625003811172689/625000000000000 : ℝ)^4863 := by
      have hnat : (50001447964424865939 : ℕ)^1024*625000000000000^4863 ≤ 625003811172689^4863*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001447964424865939 50000000000000000000 625003811172689 625000000000000 1024 4863 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625003811172689/625000000000000 : ℝ)) (X := (50001447964424865939/50000000000000000000 : ℝ)) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013241823902600131/50000000000000000000 : ℝ) ≤ (10000557606845351/10000000000000000 : ℝ) ^ (4863/1024 : ℝ) := by
    have hpowers : (50013241823902600131/50000000000000000000 : ℝ)^1024 ≤ (10000557606845351/10000000000000000 : ℝ)^4863 := by
      have hnat : (50013241823902600131 : ℕ)^1024*10000000000000000^4863 ≤ 10000557606845351^4863*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013241823902600131 50000000000000000000 10000557606845351 10000000000000000 1024 4863 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000557606845351/10000000000000000 : ℝ)) (X := (50013241823902600131/50000000000000000000 : ℝ)) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025035683380334323/50000000000000000000 : ℝ) ≤ (5000527117463839/5000000000000000 : ℝ) ^ (4863/1024 : ℝ) := by
    have hpowers : (50025035683380334323/50000000000000000000 : ℝ)^1024 ≤ (5000527117463839/5000000000000000 : ℝ)^4863 := by
      have hnat : (50025035683380334323 : ℕ)^1024*5000000000000000^4863 ≤ 5000527117463839^4863*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025035683380334323 50000000000000000000 5000527117463839 5000000000000000 1024 4863 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000527117463839/5000000000000000 : ℝ)) (X := (50025035683380334323/50000000000000000000 : ℝ)) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1447964424865939/100000000000000000000 : ℝ) ≤ ((655924771473453807/656000000000000000 : ℝ)+2*(165542694109/262400000000000 : ℝ)*(2393/25000 : ℝ))^(4863/1024 : ℝ) := by
    rw [show (655924771473453807/656000000000000000 : ℝ)+2*(165542694109/262400000000000 : ℝ)*(2393/25000 : ℝ)=(625003811172689/625000000000000 : ℝ) by norm_num, show 1+2*(1447964424865939/100000000000000000000 : ℝ)=(50001447964424865939/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25035683380334323/100000000000000000000 : ℝ)+(1447964424865939/100000000000000000000 : ℝ) ≤ ((655924771473453807/656000000000000000 : ℝ)+(165542694109/262400000000000 : ℝ)*((4361/25000 : ℝ)+(2393/25000 : ℝ)))^(4863/1024 : ℝ) := by
    rw [show (655924771473453807/656000000000000000 : ℝ)+(165542694109/262400000000000 : ℝ)*((4361/25000 : ℝ)+(2393/25000 : ℝ))=(10000557606845351/10000000000000000 : ℝ) by norm_num, show 1+(25035683380334323/100000000000000000000 : ℝ)+(1447964424865939/100000000000000000000 : ℝ)=(50013241823902600131/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25035683380334323/100000000000000000000 : ℝ) ≤ ((655924771473453807/656000000000000000 : ℝ)+2*(165542694109/262400000000000 : ℝ)*(4361/25000 : ℝ))^(4863/1024 : ℝ) := by
    rw [show (655924771473453807/656000000000000000 : ℝ)+2*(165542694109/262400000000000 : ℝ)*(4361/25000 : ℝ)=(5000527117463839/5000000000000000 : ℝ) by norm_num, show 1+2*(25035683380334323/100000000000000000000 : ℝ)=(50025035683380334323/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (655924771473453807/656000000000000000 : ℝ)*(X 1 0+X 2 0)+(165542694109/262400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4863/1024 : ℝ)) (lo := (2393/25000 : ℝ)) (hi := (4361/25000 : ℝ)) (c := (655924771473453807/656000000000000000 : ℝ)) (alpha := (165542694109/262400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (655924771473453807/656000000000000000 : ℝ)*(X 0 1+X 2 1)+(165542694109/262400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4863/1024 : ℝ)) (lo := (2393/25000 : ℝ)) (hi := (4361/25000 : ℝ)) (c := (655924771473453807/656000000000000000 : ℝ)) (alpha := (165542694109/262400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (655924771473453807/656000000000000000 : ℝ)*(X 0 2+X 1 2)+(165542694109/262400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4863/1024 : ℝ)) (lo := (2393/25000 : ℝ)) (hi := (4361/25000 : ℝ)) (c := (655924771473453807/656000000000000000 : ℝ)) (alpha := (165542694109/262400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1637712301/10000000000 : ℝ)*X 0 0+(5455855219/10000000000 : ℝ)*X 0 1+(323695441/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070176189/2000000000 : ℝ)*X 1 0+(-890187249/5000000000 : ℝ)*X 1 1+(5179127777/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675441777/5000000000 : ℝ)*X 2 0+(64739081/125000000 : ℝ)*X 2 1+(-445093181/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2095110779/5000000000 : ℝ)*X 0 0+(962257543/2500000000 : ℝ)*X 0 1+(2276642041/5000000000 : ℝ)*X 0 2+(2095110779/5000000000 : ℝ)*X 1 0+(962257543/2500000000 : ℝ)*X 1 1+(2276642041/5000000000 : ℝ)*X 1 2+(2095110779/5000000000 : ℝ)*X 2 0+(962257543/2500000000 : ℝ)*X 2 1+(2276642041/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-327556767/2000000000 : ℝ)*X 0 0+(1295318593/2500000000 : ℝ)*X 0 1+(2726842669/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319267551/2500000000 : ℝ)*X 1 0+(-1505814741/10000000000 : ℝ)*X 1 1+(5453685549/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((20613559/39062500 : ℝ)*X 2 0+(5453684663/10000000000 : ℝ)*X 2 1+(-752907367/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((209520281/500000000 : ℝ)*X 0 0+(4547821697/10000000000 : ℝ)*X 0 1+(770910487/2000000000 : ℝ)*X 0 2+(209520281/500000000 : ℝ)*X 1 0+(4547821697/10000000000 : ℝ)*X 1 1+(770910487/2000000000 : ℝ)*X 1 2+(209520281/500000000 : ℝ)*X 2 0+(4547821697/10000000000 : ℝ)*X 2 1+(770910487/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25868032160479205470935909/4100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18464291/100000000000000 : ℝ)*(base19) + (1835442383/100000000000000 : ℝ)*(base23) + (102901101/100000000000000 : ℝ)*(upper4) + (490885427/100000000000000 : ℝ)*(upper5) + (314602929779757/12500000000000 : ℝ)*(major0) + (314602929779757/12500000000000 : ℝ)*(major1) + (314602929779757/12500000000000 : ℝ)*(major2) + (3613661102228989/100000000000000 : ℝ)*(sp0) + (225854431101079/6250000000000 : ℝ)*(sp1) + (225855438087441/6250000000000 : ℝ)*(sp2) + (283990038434861/20000000000000 : ℝ)*(sp3) + (554852249/2000000000000 : ℝ)*(sp4) + (3585751977/20000000000000 : ℝ)*(sp5) + (1525830231/20000000000000 : ℝ)*(sp7) + (70997891066273/5000000000000 : ℝ)*(f.failure) + (22585555280259/625000000000 : ℝ)*(f.sum) + (6914411564127/1640000000000000000000000000 : ℝ)*base66 + (72302458016767399/8200000000000000000000000000000 : ℝ)*base67 + (81502083666167399/8200000000000000000000000000000 : ℝ)*base69 + (16713478659967399/8200000000000000000000000000000 : ℝ)*base71 + (17921918807/1640000000000000000000000000 : ℝ)*base74 + (30712435692367399/8200000000000000000000000000000 : ℝ)*base75 + (61576301827167399/8200000000000000000000000000000 : ℝ)*base77 + (87597689326967399/8200000000000000000000000000000 : ℝ)*base79 + (3828190749727/1640000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (32119/31250000000000000000 : ℝ)*base90 + (32119/31250000000000000000 : ℝ)*base92 + (32119/31250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (136540795062276596683863/13120000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1105249601/100000000000000 : ℝ)*(base19) + (2256312383/100000000000000 : ℝ)*(base23) + (39155247/20000000000000 : ℝ)*(upper3) + (103858597/50000000000000 : ℝ)*(lower4) + (2556682704569729/100000000000000 : ℝ)*(major0) + (2556682704569729/100000000000000 : ℝ)*(major1) + (2556682704569729/100000000000000 : ℝ)*(major2) + (13992005353/100000000000000 : ℝ)*(sp1) + (2922952403/12500000000000 : ℝ)*(sp2) + (403129029/25000000000000 : ℝ)*(sp3) + (1835459590358151/50000000000000 : ℝ)*(sp4) + (917726020865337/25000000000000 : ℝ)*(sp5) + (734178708156939/20000000000000 : ℝ)*(sp6) + (144244426900461/10000000000000 : ℝ)*(sp7) + (721222940760363/50000000000000 : ℝ)*(f.failure) + (1835459590358151/50000000000000 : ℝ)*(f.sum) + (55418030878499/13120000000000000000000000000 : ℝ)*base66 + (190379754211439197/65600000000000000000000000000000 : ℝ)*base68 + (268014450025360803/65600000000000000000000000000000 : ℝ)*base69 + (153021614430160803/65600000000000000000000000000000 : ℝ)*base71 + (9360240728739/13120000000000000000000000000 : ℝ)*base74 + (688936718833839197/65600000000000000000000000000000 : ℝ)*base76 + (92822375584239197/65600000000000000000000000000000 : ℝ)*base78 + (124049445146960803/65600000000000000000000000000000 : ℝ)*base79 + (66733238971741/13120000000000000000000000000 : ℝ)*base81 + (128389/312500000000000000000 : ℝ)*base90 + (128389/312500000000000000000 : ℝ)*base92 + (128389/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1637_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11077897/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4361/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2393/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10513/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1639/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1637_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1637_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11077897/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10513/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1639/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1637_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1637_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1637_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11077897/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10513/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1639/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1637_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

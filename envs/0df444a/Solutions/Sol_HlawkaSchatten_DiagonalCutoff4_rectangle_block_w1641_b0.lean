-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1641_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:11:15.003844+00:00
-- url     : https://prove2.me/submissions/1006f2a0-c454-42cb-bcda-cb2c36bd0b15

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
theorem support_rectangle_w1641_s0_0 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-75429071/500000000 : ℝ)*x 0 + (5796558749/10000000000 : ℝ)*x 1 + (4915378721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (75429071/500000000 : ℝ)^4883 ≤ (11415867831/125000000000 : ℝ)^3859 := by
    have hnat : (75429071 : ℕ)^4883*125000000000^3859 ≤ 11415867831^3859*500000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75429071 500000000 11415867831 125000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5796558749/10000000000 : ℝ)^4883 ≤ (2507821314429/5000000000000 : ℝ)^3859 := by
    have hnat : (5796558749 : ℕ)^4883*5000000000000^3859 ≤ 2507821314429^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5796558749 10000000000 2507821314429 5000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4915378721/10000000000 : ℝ)^4883 ≤ (31805374557/78125000000 : ℝ)^3859 := by
    have hnat : (4915378721 : ℕ)^4883*78125000000^3859 ≤ 31805374557^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4915378721 10000000000 31805374557 78125000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-75429071/500000000 : ℝ), (5796558749/10000000000 : ℝ), (4915378721/10000000000 : ℝ)] ![(11415867831/125000000000 : ℝ), (2507821314429/5000000000000 : ℝ), (31805374557/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-75429071/500000000 : ℝ)|^4883 ≤ (11415867831/125000000000 : ℝ)^3859
        have hw : |(-75429071/500000000 : ℝ)|=(75429071/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5796558749/10000000000 : ℝ)|^4883 ≤ (2507821314429/5000000000000 : ℝ)^3859
        have hw : |(5796558749/10000000000 : ℝ)|=(5796558749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4915378721/10000000000 : ℝ)|^4883 ≤ (31805374557/78125000000 : ℝ)^3859
        have hw : |(4915378721/10000000000 : ℝ)|=(4915378721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s0_1 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (680140121/1250000000 : ℝ)*x 0 + (-1993190441/10000000000 : ℝ)*x 1 + (98307603/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (680140121/1250000000 : ℝ)^4883 ≤ (11574235618609/25000000000000 : ℝ)^3859 := by
    have hnat : (680140121 : ℕ)^4883*25000000000000^3859 ≤ 11574235618609^3859*1250000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680140121 1250000000 11574235618609 25000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1993190441/10000000000 : ℝ)^4883 ≤ (812010193777/6250000000000 : ℝ)^3859 := by
    have hnat : (1993190441 : ℕ)^4883*6250000000000^3859 ≤ 812010193777^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993190441 10000000000 812010193777 6250000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (98307603/200000000 : ℝ)^4883 ≤ (636107725141/1562500000000 : ℝ)^3859 := by
    have hnat : (98307603 : ℕ)^4883*1562500000000^3859 ≤ 636107725141^3859*200000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98307603 200000000 636107725141 1562500000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(680140121/1250000000 : ℝ), (-1993190441/10000000000 : ℝ), (98307603/200000000 : ℝ)] ![(11574235618609/25000000000000 : ℝ), (812010193777/6250000000000 : ℝ), (636107725141/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(680140121/1250000000 : ℝ)|^4883 ≤ (11574235618609/25000000000000 : ℝ)^3859
        have hw : |(680140121/1250000000 : ℝ)|=(680140121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1993190441/10000000000 : ℝ)|^4883 ≤ (812010193777/6250000000000 : ℝ)^3859
        have hw : |(-1993190441/10000000000 : ℝ)|=(1993190441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(98307603/200000000 : ℝ)|^4883 ≤ (636107725141/1562500000000 : ℝ)^3859
        have hw : |(98307603/200000000 : ℝ)|=(98307603/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s0_2 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5441122981/10000000000 : ℝ)*x 0 + (4915378613/10000000000 : ℝ)*x 1 + (-996594883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5441122981/10000000000 : ℝ)^4883 ≤ (11574241036867/25000000000000 : ℝ)^3859 := by
    have hnat : (5441122981 : ℕ)^4883*25000000000000^3859 ≤ 11574241036867^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441122981 10000000000 11574241036867 25000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4915378613/10000000000 : ℝ)^4883 ≤ (40710878301109/100000000000000 : ℝ)^3859 := by
    have hnat : (4915378613 : ℕ)^4883*100000000000000^3859 ≤ 40710878301109^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4915378613 10000000000 40710878301109 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (996594883/5000000000 : ℝ)^4883 ≤ (3248039383271/25000000000000 : ℝ)^3859 := by
    have hnat : (996594883 : ℕ)^4883*25000000000000^3859 ≤ 3248039383271^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996594883 5000000000 3248039383271 25000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5441122981/10000000000 : ℝ), (4915378613/10000000000 : ℝ), (-996594883/5000000000 : ℝ)] ![(11574241036867/25000000000000 : ℝ), (40710878301109/100000000000000 : ℝ), (3248039383271/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5441122981/10000000000 : ℝ)|^4883 ≤ (11574241036867/25000000000000 : ℝ)^3859
        have hw : |(5441122981/10000000000 : ℝ)|=(5441122981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4915378613/10000000000 : ℝ)|^4883 ≤ (40710878301109/100000000000000 : ℝ)^3859
        have hw : |(4915378613/10000000000 : ℝ)|=(4915378613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-996594883/5000000000 : ℝ)|^4883 ≤ (3248039383271/25000000000000 : ℝ)^3859
        have hw : |(-996594883/5000000000 : ℝ)|=(996594883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s0_3 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (818969673/2000000000 : ℝ)*x 0 + (3080449297/10000000000 : ℝ)*x 1 + (533445037/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (818969673/2000000000 : ℝ)^4883 ≤ (4038812594737/12500000000000 : ℝ)^3859 := by
    have hnat : (818969673 : ℕ)^4883*12500000000000^3859 ≤ 4038812594737^3859*2000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      818969673 2000000000 4038812594737 12500000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3080449297/10000000000 : ℝ)^4883 ≤ (11269013773103/50000000000000 : ℝ)^3859 := by
    have hnat : (3080449297 : ℕ)^4883*50000000000000^3859 ≤ 11269013773103^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3080449297 10000000000 11269013773103 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (533445037/1000000000 : ℝ)^4883 ≤ (1806058867281/4000000000000 : ℝ)^3859 := by
    have hnat : (533445037 : ℕ)^4883*4000000000000^3859 ≤ 1806058867281^3859*1000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533445037 1000000000 1806058867281 4000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(818969673/2000000000 : ℝ), (3080449297/10000000000 : ℝ), (533445037/1000000000 : ℝ)] ![(4038812594737/12500000000000 : ℝ), (11269013773103/50000000000000 : ℝ), (1806058867281/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(818969673/2000000000 : ℝ)|^4883 ≤ (4038812594737/12500000000000 : ℝ)^3859
        have hw : |(818969673/2000000000 : ℝ)|=(818969673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3080449297/10000000000 : ℝ)|^4883 ≤ (11269013773103/50000000000000 : ℝ)^3859
        have hw : |(3080449297/10000000000 : ℝ)|=(3080449297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(533445037/1000000000 : ℝ)|^4883 ≤ (1806058867281/4000000000000 : ℝ)^3859
        have hw : |(533445037/1000000000 : ℝ)|=(533445037/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s0_4 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1510981607/10000000000 : ℝ)*x 0 + (2468671311/5000000000 : ℝ)*x 1 + (1443457817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1510981607/10000000000 : ℝ)^4883 ≤ (9151084141611/100000000000000 : ℝ)^3859 := by
    have hnat : (1510981607 : ℕ)^4883*100000000000000^3859 ≤ 9151084141611^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510981607 10000000000 9151084141611 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2468671311/5000000000 : ℝ)^4883 ≤ (8188239927557/20000000000000 : ℝ)^3859 := by
    have hnat : (2468671311 : ℕ)^4883*20000000000000^3859 ≤ 8188239927557^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2468671311 5000000000 8188239927557 20000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1443457817/2500000000 : ℝ)^4883 ≤ (1559616131417/3125000000000 : ℝ)^3859 := by
    have hnat : (1443457817 : ℕ)^4883*3125000000000^3859 ≤ 1559616131417^3859*2500000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1443457817 2500000000 1559616131417 3125000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1510981607/10000000000 : ℝ), (2468671311/5000000000 : ℝ), (1443457817/2500000000 : ℝ)] ![(9151084141611/100000000000000 : ℝ), (8188239927557/20000000000000 : ℝ), (1559616131417/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1510981607/10000000000 : ℝ)|^4883 ≤ (9151084141611/100000000000000 : ℝ)^3859
        have hw : |(-1510981607/10000000000 : ℝ)|=(1510981607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2468671311/5000000000 : ℝ)|^4883 ≤ (8188239927557/20000000000000 : ℝ)^3859
        have hw : |(2468671311/5000000000 : ℝ)|=(2468671311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1443457817/2500000000 : ℝ)|^4883 ≤ (1559616131417/3125000000000 : ℝ)^3859
        have hw : |(1443457817/2500000000 : ℝ)|=(1443457817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s0_5 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (650075177/1250000000 : ℝ)*x 0 + (-567369041/5000000000 : ℝ)*x 1 + (5773831189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (650075177/1250000000 : ℝ)^4883 ≤ (21861367908781/50000000000000 : ℝ)^3859 := by
    have hnat : (650075177 : ℕ)^4883*50000000000000^3859 ≤ 21861367908781^3859*1250000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650075177 1250000000 21861367908781 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (567369041/5000000000 : ℝ)^4883 ≤ (6369548826639/100000000000000 : ℝ)^3859 := by
    have hnat : (567369041 : ℕ)^4883*100000000000000^3859 ≤ 6369548826639^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567369041 5000000000 6369548826639 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5773831189/10000000000 : ℝ)^4883 ≤ (49907715341287/100000000000000 : ℝ)^3859 := by
    have hnat : (5773831189 : ℕ)^4883*100000000000000^3859 ≤ 49907715341287^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5773831189 10000000000 49907715341287 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(650075177/1250000000 : ℝ), (-567369041/5000000000 : ℝ), (5773831189/10000000000 : ℝ)] ![(21861367908781/50000000000000 : ℝ), (6369548826639/100000000000000 : ℝ), (49907715341287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(650075177/1250000000 : ℝ)|^4883 ≤ (21861367908781/50000000000000 : ℝ)^3859
        have hw : |(650075177/1250000000 : ℝ)|=(650075177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-567369041/5000000000 : ℝ)|^4883 ≤ (6369548826639/100000000000000 : ℝ)^3859
        have hw : |(-567369041/5000000000 : ℝ)|=(567369041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5773831189/10000000000 : ℝ)|^4883 ≤ (49907715341287/100000000000000 : ℝ)^3859
        have hw : |(5773831189/10000000000 : ℝ)|=(5773831189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s0_6 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1300150381/2500000000 : ℝ)*x 0 + (2886915537/5000000000 : ℝ)*x 1 + (-1134738097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1300150381/2500000000 : ℝ)^4883 ≤ (43722736966481/100000000000000 : ℝ)^3859 := by
    have hnat : (1300150381 : ℕ)^4883*100000000000000^3859 ≤ 43722736966481^3859*2500000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300150381 2500000000 43722736966481 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2886915537/5000000000 : ℝ)^4883 ≤ (24953857041741/50000000000000 : ℝ)^3859 := by
    have hnat : (2886915537 : ℕ)^4883*50000000000000^3859 ≤ 24953857041741^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2886915537 5000000000 24953857041741 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134738097/10000000000 : ℝ)^4883 ≤ (318477446659/5000000000000 : ℝ)^3859 := by
    have hnat : (1134738097 : ℕ)^4883*5000000000000^3859 ≤ 318477446659^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134738097 10000000000 318477446659 5000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1300150381/2500000000 : ℝ), (2886915537/5000000000 : ℝ), (-1134738097/10000000000 : ℝ)] ![(43722736966481/100000000000000 : ℝ), (24953857041741/50000000000000 : ℝ), (318477446659/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1300150381/2500000000 : ℝ)|^4883 ≤ (43722736966481/100000000000000 : ℝ)^3859
        have hw : |(1300150381/2500000000 : ℝ)|=(1300150381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2886915537/5000000000 : ℝ)|^4883 ≤ (24953857041741/50000000000000 : ℝ)^3859
        have hw : |(2886915537/5000000000 : ℝ)|=(2886915537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1134738097/10000000000 : ℝ)|^4883 ≤ (318477446659/5000000000000 : ℝ)^3859
        have hw : |(-1134738097/10000000000 : ℝ)|=(1134738097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s0_7 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82019803/200000000 : ℝ)*x 0 + (5278269341/10000000000 : ℝ)*x 1 + (627716379/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82019803/200000000 : ℝ)^4883 ≤ (32371834406957/100000000000000 : ℝ)^3859 := by
    have hnat : (82019803 : ℕ)^4883*100000000000000^3859 ≤ 32371834406957^3859*200000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82019803 200000000 32371834406957 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5278269341/10000000000 : ℝ)^4883 ≤ (5568826161607/12500000000000 : ℝ)^3859 := by
    have hnat : (5278269341 : ℕ)^4883*12500000000000^3859 ≤ 5568826161607^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278269341 10000000000 5568826161607 12500000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627716379/2000000000 : ℝ)^4883 ≤ (23077556277741/100000000000000 : ℝ)^3859 := by
    have hnat : (627716379 : ℕ)^4883*100000000000000^3859 ≤ 23077556277741^3859*2000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627716379 2000000000 23077556277741 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82019803/200000000 : ℝ), (5278269341/10000000000 : ℝ), (627716379/2000000000 : ℝ)] ![(32371834406957/100000000000000 : ℝ), (5568826161607/12500000000000 : ℝ), (23077556277741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82019803/200000000 : ℝ)|^4883 ≤ (32371834406957/100000000000000 : ℝ)^3859
        have hw : |(82019803/200000000 : ℝ)|=(82019803/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5278269341/10000000000 : ℝ)|^4883 ≤ (5568826161607/12500000000000 : ℝ)^3859
        have hw : |(5278269341/10000000000 : ℝ)|=(5278269341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(627716379/2000000000 : ℝ)|^4883 ≤ (23077556277741/100000000000000 : ℝ)^3859
        have hw : |(627716379/2000000000 : ℝ)|=(627716379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1641_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (88948487/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4667/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (471/2000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4879/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4879 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4879*1^1024 ≤ 0^1024*1^4879 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4879 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4879/1024 : ℝ) ≤ (1270444681461893941/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4879 ≤ (1270444681461893941/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4879*100000000000000000000^1024 ≤ 1270444681461893941^1024*5^4879 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1270444681461893941 100000000000000000000 4879 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1270444681461893941/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4879/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4879 := by
      have hnat : (1 : ℕ)^1024*1^4879 ≤ 1^4879*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4879 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101270444681461893941/100000000000000000000 : ℝ) ≤ (10026531153745489/10000000000000000 : ℝ) ^ (4879/1024 : ℝ) := by
    have hpowers : (101270444681461893941/100000000000000000000 : ℝ)^1024 ≤ (10026531153745489/10000000000000000 : ℝ)^4879 := by
      have hnat : (101270444681461893941 : ℕ)^1024*10000000000000000^4879 ≤ 10026531153745489^4879*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101270444681461893941 100000000000000000000 10026531153745489 10000000000000000 1024 4879 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10026531153745489/10000000000000000 : ℝ)) (X := (101270444681461893941/100000000000000000000 : ℝ)) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51270444681461893941/50000000000000000000 : ℝ) ≤ (5026531153745489/5000000000000000 : ℝ) ^ (4879/1024 : ℝ) := by
    have hpowers : (51270444681461893941/50000000000000000000 : ℝ)^1024 ≤ (5026531153745489/5000000000000000 : ℝ)^4879 := by
      have hnat : (51270444681461893941 : ℕ)^1024*5000000000000000^4879 ≤ 5026531153745489^4879*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51270444681461893941 50000000000000000000 5026531153745489 5000000000000000 1024 4879 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5026531153745489/5000000000000000 : ℝ)) (X := (51270444681461893941/50000000000000000000 : ℝ)) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(26531153745489/4000000000000000 : ℝ)*(0 : ℝ))^(4879/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(26531153745489/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1270444681461893941/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(26531153745489/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4879/1024 : ℝ) := by
    rw [show (1 : ℝ)+(26531153745489/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10026531153745489/10000000000000000 : ℝ) by norm_num, show 1+(1270444681461893941/100000000000000000000 : ℝ)+(0 : ℝ)=(101270444681461893941/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1270444681461893941/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(26531153745489/4000000000000000 : ℝ)*(2/5 : ℝ))^(4879/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(26531153745489/4000000000000000 : ℝ)*(2/5 : ℝ)=(5026531153745489/5000000000000000 : ℝ) by norm_num, show 1+2*(1270444681461893941/100000000000000000000 : ℝ)=(51270444681461893941/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(26531153745489/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4879/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26531153745489/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(26531153745489/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4879/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26531153745489/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(26531153745489/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4879/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26531153745489/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-75429071/500000000 : ℝ)*X 0 0+(5796558749/10000000000 : ℝ)*X 0 1+(4915378721/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((680140121/1250000000 : ℝ)*X 1 0+(-1993190441/10000000000 : ℝ)*X 1 1+(98307603/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5441122981/10000000000 : ℝ)*X 2 0+(4915378613/10000000000 : ℝ)*X 2 1+(-996594883/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((818969673/2000000000 : ℝ)*X 0 0+(3080449297/10000000000 : ℝ)*X 0 1+(533445037/1000000000 : ℝ)*X 0 2+(818969673/2000000000 : ℝ)*X 1 0+(3080449297/10000000000 : ℝ)*X 1 1+(533445037/1000000000 : ℝ)*X 1 2+(818969673/2000000000 : ℝ)*X 2 0+(3080449297/10000000000 : ℝ)*X 2 1+(533445037/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1510981607/10000000000 : ℝ)*X 0 0+(2468671311/5000000000 : ℝ)*X 0 1+(1443457817/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((650075177/1250000000 : ℝ)*X 1 0+(-567369041/5000000000 : ℝ)*X 1 1+(5773831189/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1300150381/2500000000 : ℝ)*X 2 0+(2886915537/5000000000 : ℝ)*X 2 1+(-1134738097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((82019803/200000000 : ℝ)*X 0 0+(5278269341/10000000000 : ℝ)*X 0 1+(627716379/2000000000 : ℝ)*X 0 2+(82019803/200000000 : ℝ)*X 1 0+(5278269341/10000000000 : ℝ)*X 1 1+(627716379/2000000000 : ℝ)*X 1 2+(82019803/200000000 : ℝ)*X 2 0+(5278269341/10000000000 : ℝ)*X 2 1+(627716379/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (233607637548347314875759/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (372066437/25000000000000 : ℝ)*(base19) + (226650377/12500000000000 : ℝ)*(base23) + (181719/195312500000 : ℝ)*(upper3) + (51644179/100000000000000 : ℝ)*(upper4) + (347736017/100000000000000 : ℝ)*(upper5) + (98657433431523/12500000000000 : ℝ)*(major0) + (98657433431523/12500000000000 : ℝ)*(major1) + (98657433431523/12500000000000 : ℝ)*(major2) + (56742400897141/5000000000000 : ℝ)*(sp0) + (567428074991339/50000000000000 : ℝ)*(sp1) + (113485582504541/10000000000000 : ℝ)*(sp2) + (221829217650219/50000000000000 : ℝ)*(sp3) + (9620305607/100000000000000 : ℝ)*(sp4) + (2549878649/100000000000000 : ℝ)*(sp7) + (443660985179087/100000000000000 : ℝ)*(f.failure) + (567428819124213/50000000000000 : ℝ)*(f.sum) + (100577042374747/25000000000000000000000000000 : ℝ)*base65 + (39752145199747/50000000000000000000000000000 : ℝ)*base67 + (206061288900253/50000000000000000000000000000 : ℝ)*base70 + (474378275449747/50000000000000000000000000000 : ℝ)*base71 + (26945333275253/25000000000000000000000000000 : ℝ)*base74 + (131439270899747/50000000000000000000000000000 : ℝ)*base75 + (293529530149747/50000000000000000000000000000 : ℝ)*base77 + (254332015399747/50000000000000000000000000000 : ℝ)*base79 + (93158744725253/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (12691369/5000000000000000000000 : ℝ)*base89 + (12691369/5000000000000000000000 : ℝ)*base91 + (12691369/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1894640914585088409/250000000000000000000000 : ℝ) := by norm_num
    linear_combination (72857381/5000000000000 : ℝ)*(base19) + (186907919/12500000000000 : ℝ)*(base23) + (98260741/100000000000000 : ℝ)*(base32) + (116832731/50000000000000 : ℝ)*(upper3) + (159603331/100000000000000 : ℝ)*(upper5) + (33256619664413/4000000000000 : ℝ)*(major0) + (33256619664413/4000000000000 : ℝ)*(major1) + (33256619664413/4000000000000 : ℝ)*(major2) + (135675139/3125000000000 : ℝ)*(sp1) + (185156799/4000000000000 : ℝ)*(sp2) + (298868217521293/25000000000000 : ℝ)*(sp4) + (74716691958319/6250000000000 : ℝ)*(sp5) + (597733372950923/50000000000000 : ℝ)*(sp6) + (93471552451189/20000000000000 : ℝ)*(sp7) + (233678930258343/50000000000000 : ℝ)*(f.failure) + (298868217521293/25000000000000 : ℝ)*(f.sum) + (20372890185043/8000000000000000000000000000 : ℝ)*base66 + (82506660918957/16000000000000000000000000000 : ℝ)*base67 + (1902789353043/16000000000000000000000000000 : ℝ)*base70 + (71393069734957/16000000000000000000000000000 : ℝ)*base71 + (5969319390957/8000000000000000000000000000 : ℝ)*base73 + (20216734486957/16000000000000000000000000000 : ℝ)*base75 + (10600784118957/16000000000000000000000000000 : ℝ)*base77 + (53596639801043/16000000000000000000000000000 : ℝ)*base80 + (31915310321043/8000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3977041/2500000000000000000000 : ℝ)*base89 + (3977041/2500000000000000000000 : ℝ)*base91 + (3977041/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1641_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (88948487/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4667/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (471/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1641_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1641_s1_0 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-404556603/2500000000 : ℝ)*x 0 + (5503202459/10000000000 : ℝ)*x 1 + (5137551669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404556603/2500000000 : ℝ)^4883 ≤ (1996112039179/20000000000000 : ℝ)^3859 := by
    have hnat : (404556603 : ℕ)^4883*20000000000000^3859 ≤ 1996112039179^3859*2500000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404556603 2500000000 1996112039179 20000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5503202459/10000000000 : ℝ)^4883 ≤ (46966353909809/100000000000000 : ℝ)^3859 := by
    have hnat : (5503202459 : ℕ)^4883*100000000000000^3859 ≤ 46966353909809^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503202459 10000000000 46966353909809 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5137551669/10000000000 : ℝ)^4883 ≤ (43053085879239/100000000000000 : ℝ)^3859 := by
    have hnat : (5137551669 : ℕ)^4883*100000000000000^3859 ≤ 43053085879239^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137551669 10000000000 43053085879239 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-404556603/2500000000 : ℝ), (5503202459/10000000000 : ℝ), (5137551669/10000000000 : ℝ)] ![(1996112039179/20000000000000 : ℝ), (46966353909809/100000000000000 : ℝ), (43053085879239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-404556603/2500000000 : ℝ)|^4883 ≤ (1996112039179/20000000000000 : ℝ)^3859
        have hw : |(-404556603/2500000000 : ℝ)|=(404556603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5503202459/10000000000 : ℝ)|^4883 ≤ (46966353909809/100000000000000 : ℝ)^3859
        have hw : |(5503202459/10000000000 : ℝ)|=(5503202459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5137551669/10000000000 : ℝ)|^4883 ≤ (43053085879239/100000000000000 : ℝ)^3859
        have hw : |(5137551669/10000000000 : ℝ)|=(5137551669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s1_1 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072619003/2000000000 : ℝ)*x 0 + (-1808551983/10000000000 : ℝ)*x 1 + (513755147/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072619003/2000000000 : ℝ)^4883 ≤ (45458477435799/100000000000000 : ℝ)^3859 := by
    have hnat : (1072619003 : ℕ)^4883*100000000000000^3859 ≤ 45458477435799^3859*2000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072619003 2000000000 45458477435799 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1808551983/10000000000 : ℝ)^4883 ≤ (2872109695041/25000000000000 : ℝ)^3859 := by
    have hnat : (1808551983 : ℕ)^4883*25000000000000^3859 ≤ 2872109695041^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1808551983 10000000000 2872109695041 25000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513755147/1000000000 : ℝ)^4883 ≤ (4305308376909/10000000000000 : ℝ)^3859 := by
    have hnat : (513755147 : ℕ)^4883*10000000000000^3859 ≤ 4305308376909^3859*1000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513755147 1000000000 4305308376909 10000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072619003/2000000000 : ℝ), (-1808551983/10000000000 : ℝ), (513755147/1000000000 : ℝ)] ![(45458477435799/100000000000000 : ℝ), (2872109695041/25000000000000 : ℝ), (4305308376909/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072619003/2000000000 : ℝ)|^4883 ≤ (45458477435799/100000000000000 : ℝ)^3859
        have hw : |(1072619003/2000000000 : ℝ)|=(1072619003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1808551983/10000000000 : ℝ)|^4883 ≤ (2872109695041/25000000000000 : ℝ)^3859
        have hw : |(-1808551983/10000000000 : ℝ)|=(1808551983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(513755147/1000000000 : ℝ)|^4883 ≤ (4305308376909/10000000000000 : ℝ)^3859
        have hw : |(513755147/1000000000 : ℝ)|=(513755147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s1_2 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335193507/625000000 : ℝ)*x 0 + (5137550197/10000000000 : ℝ)*x 1 + (-1808552199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335193507/625000000 : ℝ)^4883 ≤ (9091697840301/20000000000000 : ℝ)^3859 := by
    have hnat : (335193507 : ℕ)^4883*20000000000000^3859 ≤ 9091697840301^3859*625000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335193507 625000000 9091697840301 20000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5137550197/10000000000 : ℝ)^4883 ≤ (86106140541/200000000000 : ℝ)^3859 := by
    have hnat : (5137550197 : ℕ)^4883*200000000000^3859 ≤ 86106140541^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137550197 10000000000 86106140541 200000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1808552199/10000000000 : ℝ)^4883 ≤ (2872110129087/25000000000000 : ℝ)^3859 := by
    have hnat : (1808552199 : ℕ)^4883*25000000000000^3859 ≤ 2872110129087^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1808552199 10000000000 2872110129087 25000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335193507/625000000 : ℝ), (5137550197/10000000000 : ℝ), (-1808552199/10000000000 : ℝ)] ![(9091697840301/20000000000000 : ℝ), (86106140541/200000000000 : ℝ), (2872110129087/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335193507/625000000 : ℝ)|^4883 ≤ (9091697840301/20000000000000 : ℝ)^3859
        have hw : |(335193507/625000000 : ℝ)|=(335193507/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5137550197/10000000000 : ℝ)|^4883 ≤ (86106140541/200000000000 : ℝ)^3859
        have hw : |(5137550197/10000000000 : ℝ)|=(5137550197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1808552199/10000000000 : ℝ)|^4883 ≤ (2872110129087/25000000000000 : ℝ)^3859
        have hw : |(-1808552199/10000000000 : ℝ)|=(1808552199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s1_3 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (835910417/2000000000 : ℝ)*x 0 + (3731075997/10000000000 : ℝ)*x 1 + (4666390489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (835910417/2000000000 : ℝ)^4883 ≤ (33158517850557/100000000000000 : ℝ)^3859 := by
    have hnat : (835910417 : ℕ)^4883*100000000000000^3859 ≤ 33158517850557^3859*2000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835910417 2000000000 33158517850557 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3731075997/10000000000 : ℝ)^4883 ≤ (28722264688243/100000000000000 : ℝ)^3859 := by
    have hnat : (3731075997 : ℕ)^4883*100000000000000^3859 ≤ 28722264688243^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3731075997 10000000000 28722264688243 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4666390489/10000000000 : ℝ)^4883 ≤ (9529804362943/25000000000000 : ℝ)^3859 := by
    have hnat : (4666390489 : ℕ)^4883*25000000000000^3859 ≤ 9529804362943^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4666390489 10000000000 9529804362943 25000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(835910417/2000000000 : ℝ), (3731075997/10000000000 : ℝ), (4666390489/10000000000 : ℝ)] ![(33158517850557/100000000000000 : ℝ), (28722264688243/100000000000000 : ℝ), (9529804362943/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(835910417/2000000000 : ℝ)|^4883 ≤ (33158517850557/100000000000000 : ℝ)^3859
        have hw : |(835910417/2000000000 : ℝ)|=(835910417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3731075997/10000000000 : ℝ)|^4883 ≤ (28722264688243/100000000000000 : ℝ)^3859
        have hw : |(3731075997/10000000000 : ℝ)|=(3731075997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4666390489/10000000000 : ℝ)|^4883 ≤ (9529804362943/25000000000000 : ℝ)^3859
        have hw : |(4666390489/10000000000 : ℝ)|=(4666390489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s1_4 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1618395643/10000000000 : ℝ)*x 0 + (1028263159/2000000000 : ℝ)*x 1 + (5499383371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1618395643/10000000000 : ℝ)^4883 ≤ (9981880924321/100000000000000 : ℝ)^3859 := by
    have hnat : (1618395643 : ℕ)^4883*100000000000000^3859 ≤ 9981880924321^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1618395643 10000000000 9981880924321 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028263159/2000000000 : ℝ)^4883 ≤ (21546501829993/50000000000000 : ℝ)^3859 := by
    have hnat : (1028263159 : ℕ)^4883*50000000000000^3859 ≤ 21546501829993^3859*2000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028263159 2000000000 21546501829993 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5499383371/10000000000 : ℝ)^4883 ≤ (2346255769963/5000000000000 : ℝ)^3859 := by
    have hnat : (5499383371 : ℕ)^4883*5000000000000^3859 ≤ 2346255769963^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499383371 10000000000 2346255769963 5000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1618395643/10000000000 : ℝ), (1028263159/2000000000 : ℝ), (5499383371/10000000000 : ℝ)] ![(9981880924321/100000000000000 : ℝ), (21546501829993/50000000000000 : ℝ), (2346255769963/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1618395643/10000000000 : ℝ)|^4883 ≤ (9981880924321/100000000000000 : ℝ)^3859
        have hw : |(-1618395643/10000000000 : ℝ)|=(1618395643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028263159/2000000000 : ℝ)|^4883 ≤ (21546501829993/50000000000000 : ℝ)^3859
        have hw : |(1028263159/2000000000 : ℝ)|=(1028263159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5499383371/10000000000 : ℝ)|^4883 ≤ (2346255769963/5000000000000 : ℝ)^3859
        have hw : |(5499383371/10000000000 : ℝ)|=(5499383371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s1_5 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5265423719/10000000000 : ℝ)*x 0 + (-723359827/5000000000 : ℝ)*x 1 + (687422921/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265423719/10000000000 : ℝ)^4883 ≤ (11103365373083/25000000000000 : ℝ)^3859 := by
    have hnat : (5265423719 : ℕ)^4883*25000000000000^3859 ≤ 11103365373083^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265423719 10000000000 11103365373083 25000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (723359827/5000000000 : ℝ)^4883 ≤ (8661423121159/100000000000000 : ℝ)^3859 := by
    have hnat : (723359827 : ℕ)^4883*100000000000000^3859 ≤ 8661423121159^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      723359827 5000000000 8661423121159 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (687422921/1250000000 : ℝ)^4883 ≤ (46925115366869/100000000000000 : ℝ)^3859 := by
    have hnat : (687422921 : ℕ)^4883*100000000000000^3859 ≤ 46925115366869^3859*1250000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687422921 1250000000 46925115366869 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265423719/10000000000 : ℝ), (-723359827/5000000000 : ℝ), (687422921/1250000000 : ℝ)] ![(11103365373083/25000000000000 : ℝ), (8661423121159/100000000000000 : ℝ), (46925115366869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265423719/10000000000 : ℝ)|^4883 ≤ (11103365373083/25000000000000 : ℝ)^3859
        have hw : |(5265423719/10000000000 : ℝ)|=(5265423719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-723359827/5000000000 : ℝ)|^4883 ≤ (8661423121159/100000000000000 : ℝ)^3859
        have hw : |(-723359827/5000000000 : ℝ)|=(723359827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(687422921/1250000000 : ℝ)|^4883 ≤ (46925115366869/100000000000000 : ℝ)^3859
        have hw : |(687422921/1250000000 : ℝ)|=(687422921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s1_6 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5265423579/10000000000 : ℝ)*x 0 + (274969179/500000000 : ℝ)*x 1 + (-1446719549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265423579/10000000000 : ℝ)^4883 ≤ (44413459998089/100000000000000 : ℝ)^3859 := by
    have hnat : (5265423579 : ℕ)^4883*100000000000000^3859 ≤ 44413459998089^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265423579 10000000000 44413459998089 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274969179/500000000 : ℝ)^4883 ≤ (23462558827917/50000000000000 : ℝ)^3859 := by
    have hnat : (274969179 : ℕ)^4883*50000000000000^3859 ≤ 23462558827917^3859*500000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274969179 500000000 23462558827917 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1446719549/10000000000 : ℝ)^4883 ≤ (4330711162861/50000000000000 : ℝ)^3859 := by
    have hnat : (1446719549 : ℕ)^4883*50000000000000^3859 ≤ 4330711162861^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1446719549 10000000000 4330711162861 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265423579/10000000000 : ℝ), (274969179/500000000 : ℝ), (-1446719549/10000000000 : ℝ)] ![(44413459998089/100000000000000 : ℝ), (23462558827917/50000000000000 : ℝ), (4330711162861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265423579/10000000000 : ℝ)|^4883 ≤ (44413459998089/100000000000000 : ℝ)^3859
        have hw : |(5265423579/10000000000 : ℝ)|=(5265423579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274969179/500000000 : ℝ)|^4883 ≤ (23462558827917/50000000000000 : ℝ)^3859
        have hw : |(274969179/500000000 : ℝ)|=(274969179/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1446719549/10000000000 : ℝ)|^4883 ≤ (4330711162861/50000000000000 : ℝ)^3859
        have hw : |(-1446719549/10000000000 : ℝ)|=(1446719549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s1_7 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2089990821/5000000000 : ℝ)*x 0 + (4656760789/10000000000 : ℝ)*x 1 + (37408457/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089990821/5000000000 : ℝ)^4883 ≤ (8290707525401/25000000000000 : ℝ)^3859 := by
    have hnat : (2089990821 : ℕ)^4883*25000000000000^3859 ≤ 8290707525401^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089990821 5000000000 8290707525401 25000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4656760789/10000000000 : ℝ)^4883 ≤ (38019707018557/100000000000000 : ℝ)^3859 := by
    have hnat : (4656760789 : ℕ)^4883*100000000000000^3859 ≤ 38019707018557^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4656760789 10000000000 38019707018557 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37408457/100000000 : ℝ)^4883 ≤ (5763492573731/20000000000000 : ℝ)^3859 := by
    have hnat : (37408457 : ℕ)^4883*20000000000000^3859 ≤ 5763492573731^3859*100000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37408457 100000000 5763492573731 20000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2089990821/5000000000 : ℝ), (4656760789/10000000000 : ℝ), (37408457/100000000 : ℝ)] ![(8290707525401/25000000000000 : ℝ), (38019707018557/100000000000000 : ℝ), (5763492573731/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2089990821/5000000000 : ℝ)|^4883 ≤ (8290707525401/25000000000000 : ℝ)^3859
        have hw : |(2089990821/5000000000 : ℝ)|=(2089990821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4656760789/10000000000 : ℝ)|^4883 ≤ (38019707018557/100000000000000 : ℝ)^3859
        have hw : |(4656760789/10000000000 : ℝ)|=(4656760789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(37408457/100000000 : ℝ)|^4883 ≤ (5763492573731/20000000000000 : ℝ)^3859
        have hw : |(37408457/100000000 : ℝ)|=(37408457/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1641_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (88948487/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (471/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4667/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9631/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3479/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (471/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4667/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (471/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4667/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (471/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4667/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (471/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4667/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (471/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4667/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (471/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4667/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4667/100000 : ℝ) ^ (4879/1024 : ℝ) ≤ (45544195771051/100000000000000000000 : ℝ) := by
    have hpowers : (4667/100000 : ℝ)^4879 ≤ (45544195771051/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4667 : ℕ)^4879*100000000000000000000^1024 ≤ 45544195771051^1024*100000^4879 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4667 100000 45544195771051 100000000000000000000 4879 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4667/100000 : ℝ)) (X := (45544195771051/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (471/2000 : ℝ) ^ (4879/1024 : ℝ) ≤ (101802273636389927/100000000000000000000 : ℝ) := by
    have hpowers : (471/2000 : ℝ)^4879 ≤ (101802273636389927/100000000000000000000 : ℝ)^1024 := by
      have hnat : (471 : ℕ)^4879*100000000000000000000^1024 ≤ 101802273636389927^1024*2000^4879 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        471 2000 101802273636389927 100000000000000000000 4879 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (471/2000 : ℝ)) (X := (101802273636389927/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000045544195771051/50000000000000000000 : ℝ) ≤ (2500000477938509/2500000000000000 : ℝ) ^ (4879/1024 : ℝ) := by
    have hpowers : (50000045544195771051/50000000000000000000 : ℝ)^1024 ≤ (2500000477938509/2500000000000000 : ℝ)^4879 := by
      have hnat : (50000045544195771051 : ℕ)^1024*2500000000000000^4879 ≤ 2500000477938509^4879*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000045544195771051 50000000000000000000 2500000477938509 2500000000000000 1024 4879 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000477938509/2500000000000000 : ℝ)) (X := (50000045544195771051/50000000000000000000 : ℝ)) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50050923908916080489/50000000000000000000 : ℝ) ≤ (400085468520517/400000000000000 : ℝ) ^ (4879/1024 : ℝ) := by
    have hpowers : (50050923908916080489/50000000000000000000 : ℝ)^1024 ≤ (400085468520517/400000000000000 : ℝ)^4879 := by
      have hnat : (50050923908916080489 : ℕ)^1024*400000000000000^4879 ≤ 400085468520517^4879*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50050923908916080489 50000000000000000000 400085468520517 400000000000000 1024 4879 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400085468520517/400000000000000 : ℝ)) (X := (50050923908916080489/50000000000000000000 : ℝ)) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50101802273636389927/50000000000000000000 : ℝ) ≤ (5002135757135907/5000000000000000 : ℝ) ^ (4879/1024 : ℝ) := by
    have hpowers : (50101802273636389927/50000000000000000000 : ℝ)^1024 ≤ (5002135757135907/5000000000000000 : ℝ)^4879 := by
      have hnat : (50101802273636389927 : ℕ)^1024*5000000000000000^4879 ≤ 5002135757135907^4879*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50101802273636389927 50000000000000000000 5002135757135907 5000000000000000 1024 4879 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002135757135907/5000000000000000 : ℝ)) (X := (50101802273636389927/50000000000000000000 : ℝ)) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(45544195771051/100000000000000000000 : ℝ) ≤ ((94405054932350495931/94415000000000000000 : ℝ)+2*(2134801258889/1888300000000000 : ℝ)*(4667/100000 : ℝ))^(4879/1024 : ℝ) := by
    rw [show (94405054932350495931/94415000000000000000 : ℝ)+2*(2134801258889/1888300000000000 : ℝ)*(4667/100000 : ℝ)=(2500000477938509/2500000000000000 : ℝ) by norm_num, show 1+2*(45544195771051/100000000000000000000 : ℝ)=(50000045544195771051/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(101802273636389927/100000000000000000000 : ℝ)+(45544195771051/100000000000000000000 : ℝ) ≤ ((94405054932350495931/94415000000000000000 : ℝ)+(2134801258889/1888300000000000 : ℝ)*((471/2000 : ℝ)+(4667/100000 : ℝ)))^(4879/1024 : ℝ) := by
    rw [show (94405054932350495931/94415000000000000000 : ℝ)+(2134801258889/1888300000000000 : ℝ)*((471/2000 : ℝ)+(4667/100000 : ℝ))=(400085468520517/400000000000000 : ℝ) by norm_num, show 1+(101802273636389927/100000000000000000000 : ℝ)+(45544195771051/100000000000000000000 : ℝ)=(50050923908916080489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(101802273636389927/100000000000000000000 : ℝ) ≤ ((94405054932350495931/94415000000000000000 : ℝ)+2*(2134801258889/1888300000000000 : ℝ)*(471/2000 : ℝ))^(4879/1024 : ℝ) := by
    rw [show (94405054932350495931/94415000000000000000 : ℝ)+2*(2134801258889/1888300000000000 : ℝ)*(471/2000 : ℝ)=(5002135757135907/5000000000000000 : ℝ) by norm_num, show 1+2*(101802273636389927/100000000000000000000 : ℝ)=(50101802273636389927/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (94405054932350495931/94415000000000000000 : ℝ)*(X 1 0+X 2 0)+(2134801258889/1888300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4879/1024 : ℝ)) (lo := (4667/100000 : ℝ)) (hi := (471/2000 : ℝ)) (c := (94405054932350495931/94415000000000000000 : ℝ)) (alpha := (2134801258889/1888300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (94405054932350495931/94415000000000000000 : ℝ)*(X 0 1+X 2 1)+(2134801258889/1888300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4879/1024 : ℝ)) (lo := (4667/100000 : ℝ)) (hi := (471/2000 : ℝ)) (c := (94405054932350495931/94415000000000000000 : ℝ)) (alpha := (2134801258889/1888300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (94405054932350495931/94415000000000000000 : ℝ)*(X 0 2+X 1 2)+(2134801258889/1888300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4879/1024 : ℝ)) (lo := (4667/100000 : ℝ)) (hi := (471/2000 : ℝ)) (c := (94405054932350495931/94415000000000000000 : ℝ)) (alpha := (2134801258889/1888300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-404556603/2500000000 : ℝ)*X 0 0+(5503202459/10000000000 : ℝ)*X 0 1+(5137551669/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1072619003/2000000000 : ℝ)*X 1 0+(-1808551983/10000000000 : ℝ)*X 1 1+(513755147/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((335193507/625000000 : ℝ)*X 2 0+(5137550197/10000000000 : ℝ)*X 2 1+(-1808552199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((835910417/2000000000 : ℝ)*X 0 0+(3731075997/10000000000 : ℝ)*X 0 1+(4666390489/10000000000 : ℝ)*X 0 2+(835910417/2000000000 : ℝ)*X 1 0+(3731075997/10000000000 : ℝ)*X 1 1+(4666390489/10000000000 : ℝ)*X 1 2+(835910417/2000000000 : ℝ)*X 2 0+(3731075997/10000000000 : ℝ)*X 2 1+(4666390489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1618395643/10000000000 : ℝ)*X 0 0+(1028263159/2000000000 : ℝ)*X 0 1+(5499383371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5265423719/10000000000 : ℝ)*X 1 0+(-723359827/5000000000 : ℝ)*X 1 1+(687422921/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5265423579/10000000000 : ℝ)*X 2 0+(274969179/500000000 : ℝ)*X 2 1+(-1446719549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2089990821/5000000000 : ℝ)*X 0 0+(4656760789/10000000000 : ℝ)*X 0 1+(37408457/100000000 : ℝ)*X 0 2+(2089990821/5000000000 : ℝ)*X 1 0+(4656760789/10000000000 : ℝ)*X 1 1+(37408457/100000000 : ℝ)*X 1 2+(2089990821/5000000000 : ℝ)*X 2 0+(4656760789/10000000000 : ℝ)*X 2 1+(37408457/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10919029008480591931196674719/1180187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (308681881/50000000000000 : ℝ)*(base1) + (1013738369/100000000000000 : ℝ)*(base19) + (1573140631/100000000000000 : ℝ)*(base23) + (11178589/10000000000000 : ℝ)*(upper3) + (33629057/50000000000000 : ℝ)*(upper5) + (951002548287117/50000000000000 : ℝ)*(major0) + (951002548287117/50000000000000 : ℝ)*(major1) + (951002548287117/50000000000000 : ℝ)*(major2) + (683712305330869/25000000000000 : ℝ)*(sp0) + (2734847853931223/100000000000000 : ℝ)*(sp1) + (2734847294528961/100000000000000 : ℝ)*(sp2) + (1069159274850213/100000000000000 : ℝ)*(sp3) + (263709879/100000000000000 : ℝ)*(sp4) + (1124866749/100000000000000 : ℝ)*(sp7) + (534580508540363/50000000000000 : ℝ)*(f.failure) + (341856108458699/12500000000000 : ℝ)*(f.sum) + (25708224589827/11801875000000000000000000000 : ℝ)*base65 + (502424912208722649/205250000000000000000000000000000 : ℝ)*base67 + (31337646686027351/205250000000000000000000000000000 : ℝ)*base70 + (943381816649472649/205250000000000000000000000000000 : ℝ)*base71 + (50285380757869/94415000000000000000000000000 : ℝ)*base74 + (1580112069564722649/205250000000000000000000000000000 : ℝ)*base75 + (1069334241242722649/205250000000000000000000000000000 : ℝ)*base77 + (1313185189211722649/205250000000000000000000000000000 : ℝ)*base79 + (46590039921611/23603750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (17280781/2500000000000000000000 : ℝ)*base89 + (17280781/2500000000000000000000 : ℝ)*base91 + (17280781/2500000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23305396254713891077662779931/4720750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (990730621/100000000000000 : ℝ)*(base19) + (243905537/25000000000000 : ℝ)*(base23) + (21957407/100000000000000 : ℝ)*(upper2) + (120401901/100000000000000 : ℝ)*(upper3) + (64334473/50000000000000 : ℝ)*(upper5) + (1942286454015111/100000000000000 : ℝ)*(major0) + (1942286454015111/100000000000000 : ℝ)*(major1) + (1942286454015111/100000000000000 : ℝ)*(major2) + (8972402421/100000000000000 : ℝ)*(sp1) + (4956393749/50000000000000 : ℝ)*(sp2) + (279276864453423/10000000000000 : ℝ)*(sp4) + (698189670350297/25000000000000 : ℝ)*(sp5) + (349094719515573/12500000000000 : ℝ)*(sp6) + (136475512367/12500000000 : ℝ)*(sp7) + (136475512367/12500000000 : ℝ)*(f.failure) + (279276864453423/10000000000000 : ℝ)*(f.sum) + (65358861606029/94415000000000000000000000000 : ℝ)*base65 + (1252275915492476667/410500000000000000000000000000000 : ℝ)*base67 + (1806523787452476667/410500000000000000000000000000000 : ℝ)*base69 + (1406519387003976667/410500000000000000000000000000000 : ℝ)*base71 + (26445611514151/23603750000000000000000000000 : ℝ)*base73 + (2972154660250476667/410500000000000000000000000000000 : ℝ)*base75 + (1500045890541476667/410500000000000000000000000000000 : ℝ)*base77 + (6286727972844476667/410500000000000000000000000000000 : ℝ)*base79 + (616860747361649/94415000000000000000000000000 : ℝ)*base81 + (5021/625000000000000000 : ℝ)*base90 + (5021/625000000000000000 : ℝ)*base92 + (5021/625000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1641_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (88948487/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (471/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4667/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9631/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3479/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1641_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1641_s2_0 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1628420321/10000000000 : ℝ)*x 0 + (5454359609/10000000000 : ℝ)*x 1 + (5179680541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1628420321/10000000000 : ℝ)^4883 ≤ (5030090870417/50000000000000 : ℝ)^3859 := by
    have hnat : (1628420321 : ℕ)^4883*50000000000000^3859 ≤ 5030090870417^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1628420321 10000000000 5030090870417 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5454359609/10000000000 : ℝ)^4883 ≤ (46439522723739/100000000000000 : ℝ)^3859 := by
    have hnat : (5454359609 : ℕ)^4883*100000000000000^3859 ≤ 46439522723739^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454359609 10000000000 46439522723739 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179680541/10000000000 : ℝ)^4883 ≤ (21750147761229/50000000000000 : ℝ)^3859 := by
    have hnat : (5179680541 : ℕ)^4883*50000000000000^3859 ≤ 21750147761229^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179680541 10000000000 21750147761229 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1628420321/10000000000 : ℝ), (5454359609/10000000000 : ℝ), (5179680541/10000000000 : ℝ)] ![(5030090870417/50000000000000 : ℝ), (46439522723739/100000000000000 : ℝ), (21750147761229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1628420321/10000000000 : ℝ)|^4883 ≤ (5030090870417/50000000000000 : ℝ)^3859
        have hw : |(-1628420321/10000000000 : ℝ)|=(1628420321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5454359609/10000000000 : ℝ)|^4883 ≤ (46439522723739/100000000000000 : ℝ)^3859
        have hw : |(5454359609/10000000000 : ℝ)|=(5454359609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179680541/10000000000 : ℝ)|^4883 ≤ (21750147761229/50000000000000 : ℝ)^3859
        have hw : |(5179680541/10000000000 : ℝ)|=(5179680541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s2_1 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070041559/2000000000 : ℝ)*x 0 + (-176999397/1000000000 : ℝ)*x 1 + (647460159/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070041559/2000000000 : ℝ)^4883 ≤ (181281206503/400000000000 : ℝ)^3859 := by
    have hnat : (1070041559 : ℕ)^4883*400000000000^3859 ≤ 181281206503^3859*2000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070041559 2000000000 181281206503 400000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176999397/1000000000 : ℝ)^4883 ≤ (11179395068927/100000000000000 : ℝ)^3859 := by
    have hnat : (176999397 : ℕ)^4883*100000000000000^3859 ≤ 11179395068927^3859*1000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176999397 1000000000 11179395068927 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647460159/1250000000 : ℝ)^4883 ≤ (13920097053/32000000000 : ℝ)^3859 := by
    have hnat : (647460159 : ℕ)^4883*32000000000^3859 ≤ 13920097053^3859*1250000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647460159 1250000000 13920097053 32000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070041559/2000000000 : ℝ), (-176999397/1000000000 : ℝ), (647460159/1250000000 : ℝ)] ![(181281206503/400000000000 : ℝ), (11179395068927/100000000000000 : ℝ), (13920097053/32000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070041559/2000000000 : ℝ)|^4883 ≤ (181281206503/400000000000 : ℝ)^3859
        have hw : |(1070041559/2000000000 : ℝ)|=(1070041559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-176999397/1000000000 : ℝ)|^4883 ≤ (11179395068927/100000000000000 : ℝ)^3859
        have hw : |(-176999397/1000000000 : ℝ)|=(176999397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647460159/1250000000 : ℝ)|^4883 ≤ (13920097053/32000000000 : ℝ)^3859
        have hw : |(647460159/1250000000 : ℝ)|=(647460159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s2_2 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83597033/156250000 : ℝ)*x 0 + (5179679873/10000000000 : ℝ)*x 1 + (-1769992723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83597033/156250000 : ℝ)^4883 ≤ (1133008161513/2500000000000 : ℝ)^3859 := by
    have hnat : (83597033 : ℕ)^4883*2500000000000^3859 ≤ 1133008161513^3859*156250000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83597033 156250000 1133008161513 2500000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179679873/10000000000 : ℝ)^4883 ≤ (43500288423777/100000000000000 : ℝ)^3859 := by
    have hnat : (5179679873 : ℕ)^4883*100000000000000^3859 ≤ 43500288423777^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179679873 10000000000 43500288423777 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1769992723/10000000000 : ℝ)^4883 ≤ (2235877020567/20000000000000 : ℝ)^3859 := by
    have hnat : (1769992723 : ℕ)^4883*20000000000000^3859 ≤ 2235877020567^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769992723 10000000000 2235877020567 20000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83597033/156250000 : ℝ), (5179679873/10000000000 : ℝ), (-1769992723/10000000000 : ℝ)] ![(1133008161513/2500000000000 : ℝ), (43500288423777/100000000000000 : ℝ), (2235877020567/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83597033/156250000 : ℝ)|^4883 ≤ (1133008161513/2500000000000 : ℝ)^3859
        have hw : |(83597033/156250000 : ℝ)|=(83597033/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179679873/10000000000 : ℝ)|^4883 ≤ (43500288423777/100000000000000 : ℝ)^3859
        have hw : |(5179679873/10000000000 : ℝ)|=(5179679873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1769992723/10000000000 : ℝ)|^4883 ≤ (2235877020567/20000000000000 : ℝ)^3859
        have hw : |(-1769992723/10000000000 : ℝ)|=(1769992723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s2_3 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1046783497/2500000000 : ℝ)*x 0 + (3846656069/10000000000 : ℝ)*x 1 + (181970771/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046783497/2500000000 : ℝ)^4883 ≤ (33234648582573/100000000000000 : ℝ)^3859 := by
    have hnat : (1046783497 : ℕ)^4883*100000000000000^3859 ≤ 33234648582573^3859*2500000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046783497 2500000000 33234648582573 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3846656069/10000000000 : ℝ)^4883 ≤ (29852704608151/100000000000000 : ℝ)^3859 := by
    have hnat : (3846656069 : ℕ)^4883*100000000000000^3859 ≤ 29852704608151^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3846656069 10000000000 29852704608151 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181970771/400000000 : ℝ)^4883 ≤ (1153520212271/3125000000000 : ℝ)^3859 := by
    have hnat : (181970771 : ℕ)^4883*3125000000000^3859 ≤ 1153520212271^3859*400000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181970771 400000000 1153520212271 3125000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046783497/2500000000 : ℝ), (3846656069/10000000000 : ℝ), (181970771/400000000 : ℝ)] ![(33234648582573/100000000000000 : ℝ), (29852704608151/100000000000000 : ℝ), (1153520212271/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046783497/2500000000 : ℝ)|^4883 ≤ (33234648582573/100000000000000 : ℝ)^3859
        have hw : |(1046783497/2500000000 : ℝ)|=(1046783497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3846656069/10000000000 : ℝ)|^4883 ≤ (29852704608151/100000000000000 : ℝ)^3859
        have hw : |(3846656069/10000000000 : ℝ)|=(3846656069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(181970771/400000000 : ℝ)|^4883 ≤ (1153520212271/3125000000000 : ℝ)^3859
        have hw : |(181970771/400000000 : ℝ)|=(181970771/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s2_4 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1628490759/10000000000 : ℝ)*x 0 + (5181810971/10000000000 : ℝ)*x 1 + (5452206853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1628490759/10000000000 : ℝ)^4883 ≤ (10060732371973/100000000000000 : ℝ)^3859 := by
    have hnat : (1628490759 : ℕ)^4883*100000000000000^3859 ≤ 10060732371973^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1628490759 10000000000 10060732371973 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181810971/10000000000 : ℝ)^4883 ≤ (43522936342021/100000000000000 : ℝ)^3859 := by
    have hnat : (5181810971 : ℕ)^4883*100000000000000^3859 ≤ 43522936342021^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181810971 10000000000 43522936342021 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452206853/10000000000 : ℝ)^4883 ≤ (46416331269141/100000000000000 : ℝ)^3859 := by
    have hnat : (5452206853 : ℕ)^4883*100000000000000^3859 ≤ 46416331269141^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452206853 10000000000 46416331269141 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1628490759/10000000000 : ℝ), (5181810971/10000000000 : ℝ), (5452206853/10000000000 : ℝ)] ![(10060732371973/100000000000000 : ℝ), (43522936342021/100000000000000 : ℝ), (46416331269141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1628490759/10000000000 : ℝ)|^4883 ≤ (10060732371973/100000000000000 : ℝ)^3859
        have hw : |(-1628490759/10000000000 : ℝ)|=(1628490759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181810971/10000000000 : ℝ)|^4883 ≤ (43522936342021/100000000000000 : ℝ)^3859
        have hw : |(5181810971/10000000000 : ℝ)|=(5181810971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452206853/10000000000 : ℝ)|^4883 ≤ (46416331269141/100000000000000 : ℝ)^3859
        have hw : |(5452206853/10000000000 : ℝ)|=(5452206853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s2_5 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638452277/5000000000 : ℝ)*x 0 + (-299493481/2000000000 : ℝ)*x 1 + (5452206229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638452277/5000000000 : ℝ)^4883 ≤ (22268016887011/50000000000000 : ℝ)^3859 := by
    have hnat : (2638452277 : ℕ)^4883*50000000000000^3859 ≤ 22268016887011^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638452277 5000000000 22268016887011 50000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299493481/2000000000 : ℝ)^4883 ≤ (904764166207/10000000000000 : ℝ)^3859 := by
    have hnat : (299493481 : ℕ)^4883*10000000000000^3859 ≤ 904764166207^3859*2000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299493481 2000000000 904764166207 10000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452206229/10000000000 : ℝ)^4883 ≤ (9283264909439/20000000000000 : ℝ)^3859 := by
    have hnat : (5452206229 : ℕ)^4883*20000000000000^3859 ≤ 9283264909439^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452206229 10000000000 9283264909439 20000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638452277/5000000000 : ℝ), (-299493481/2000000000 : ℝ), (5452206229/10000000000 : ℝ)] ![(22268016887011/50000000000000 : ℝ), (904764166207/10000000000000 : ℝ), (9283264909439/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638452277/5000000000 : ℝ)|^4883 ≤ (22268016887011/50000000000000 : ℝ)^3859
        have hw : |(2638452277/5000000000 : ℝ)|=(2638452277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-299493481/2000000000 : ℝ)|^4883 ≤ (904764166207/10000000000000 : ℝ)^3859
        have hw : |(-299493481/2000000000 : ℝ)|=(299493481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452206229/10000000000 : ℝ)|^4883 ≤ (9283264909439/20000000000000 : ℝ)^3859
        have hw : |(5452206229/10000000000 : ℝ)|=(5452206229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s2_6 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055381079/2000000000 : ℝ)*x 0 + (5452205739/10000000000 : ℝ)*x 1 + (-748733461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055381079/2000000000 : ℝ)^4883 ≤ (2783502672209/6250000000000 : ℝ)^3859 := by
    have hnat : (1055381079 : ℕ)^4883*6250000000000^3859 ≤ 2783502672209^3859*2000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055381079 2000000000 2783502672209 6250000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5452205739/10000000000 : ℝ)^4883 ≤ (5802039908593/12500000000000 : ℝ)^3859 := by
    have hnat : (5452205739 : ℕ)^4883*12500000000000^3859 ≤ 5802039908593^3859*10000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452205739 10000000000 5802039908593 12500000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (748733461/5000000000 : ℝ)^4883 ≤ (9047637969429/100000000000000 : ℝ)^3859 := by
    have hnat : (748733461 : ℕ)^4883*100000000000000^3859 ≤ 9047637969429^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748733461 5000000000 9047637969429 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055381079/2000000000 : ℝ), (5452205739/10000000000 : ℝ), (-748733461/5000000000 : ℝ)] ![(2783502672209/6250000000000 : ℝ), (5802039908593/12500000000000 : ℝ), (9047637969429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055381079/2000000000 : ℝ)|^4883 ≤ (2783502672209/6250000000000 : ℝ)^3859
        have hw : |(1055381079/2000000000 : ℝ)|=(1055381079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5452205739/10000000000 : ℝ)|^4883 ≤ (5802039908593/12500000000000 : ℝ)^3859
        have hw : |(5452205739/10000000000 : ℝ)|=(5452205739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-748733461/5000000000 : ℝ)|^4883 ≤ (9047637969429/100000000000000 : ℝ)^3859
        have hw : |(-748733461/5000000000 : ℝ)|=(748733461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1641_s2_7 (p : ℝ) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2093658671/5000000000 : ℝ)*x 0 + (2271909629/5000000000 : ℝ)*x 1 + (1926082351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093658671/5000000000 : ℝ)^4883 ≤ (33236490113811/100000000000000 : ℝ)^3859 := by
    have hnat : (2093658671 : ℕ)^4883*100000000000000^3859 ≤ 33236490113811^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093658671 5000000000 33236490113811 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2271909629/5000000000 : ℝ)^4883 ≤ (36856700116427/100000000000000 : ℝ)^3859 := by
    have hnat : (2271909629 : ℕ)^4883*100000000000000^3859 ≤ 36856700116427^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271909629 5000000000 36856700116427 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1926082351/5000000000 : ℝ)^4883 ≤ (29906809756333/100000000000000 : ℝ)^3859 := by
    have hnat : (1926082351 : ℕ)^4883*100000000000000^3859 ≤ 29906809756333^3859*5000000000^4883 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926082351 5000000000 29906809756333 100000000000000 4883 3859 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4883/1024 : ℝ)) 4883 3859 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2093658671/5000000000 : ℝ), (2271909629/5000000000 : ℝ), (1926082351/5000000000 : ℝ)] ![(33236490113811/100000000000000 : ℝ), (36856700116427/100000000000000 : ℝ), (29906809756333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2093658671/5000000000 : ℝ)|^4883 ≤ (33236490113811/100000000000000 : ℝ)^3859
        have hw : |(2093658671/5000000000 : ℝ)|=(2093658671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2271909629/5000000000 : ℝ)|^4883 ≤ (36856700116427/100000000000000 : ℝ)^3859
        have hw : |(2271909629/5000000000 : ℝ)|=(2271909629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1926082351/5000000000 : ℝ)|^4883 ≤ (29906809756333/100000000000000 : ℝ)^3859
        have hw : |(1926082351/5000000000 : ℝ)|=(1926082351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1641_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (88948487/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3479/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9631/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10541/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2047/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3479/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9631/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3479/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9631/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3479/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9631/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3479/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9631/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3479/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9631/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3479/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9631/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9631/100000 : ℝ) ^ (4879/1024 : ℝ) ≤ (57492531744753/4000000000000000000 : ℝ) := by
    have hpowers : (9631/100000 : ℝ)^4879 ≤ (57492531744753/4000000000000000000 : ℝ)^1024 := by
      have hnat : (9631 : ℕ)^4879*4000000000000000000^1024 ≤ 57492531744753^1024*100000^4879 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9631 100000 57492531744753 4000000000000000000 4879 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9631/100000 : ℝ)) (X := (57492531744753/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3479/20000 : ℝ) ^ (4879/1024 : ℝ) ≤ (12018754557445309/50000000000000000000 : ℝ) := by
    have hpowers : (3479/20000 : ℝ)^4879 ≤ (12018754557445309/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3479 : ℕ)^4879*50000000000000000000^1024 ≤ 12018754557445309^1024*20000^4879 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3479 20000 12018754557445309 50000000000000000000 4879 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3479/20000 : ℝ)) (X := (12018754557445309/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000057492531744753/2000000000000000000 : ℝ) ≤ (10000060331711349/10000000000000000 : ℝ) ^ (4879/1024 : ℝ) := by
    have hpowers : (2000057492531744753/2000000000000000000 : ℝ)^1024 ≤ (10000060331711349/10000000000000000 : ℝ)^4879 := by
      have hnat : (2000057492531744753 : ℕ)^1024*10000000000000000^4879 ≤ 10000060331711349^4879*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000057492531744753 2000000000000000000 10000060331711349 10000000000000000 1024 4879 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000060331711349/10000000000000000 : ℝ)) (X := (2000057492531744753/2000000000000000000 : ℝ)) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025474822408509443/100000000000000000000 : ℝ) ≤ (10000534609411837/10000000000000000 : ℝ) ^ (4879/1024 : ℝ) := by
    have hpowers : (100025474822408509443/100000000000000000000 : ℝ)^1024 ≤ (10000534609411837/10000000000000000 : ℝ)^4879 := by
      have hnat : (100025474822408509443 : ℕ)^1024*10000000000000000^4879 ≤ 10000534609411837^4879*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025474822408509443 100000000000000000000 10000534609411837 10000000000000000 1024 4879 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000534609411837/10000000000000000 : ℝ)) (X := (100025474822408509443/100000000000000000000 : ℝ)) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012018754557445309/25000000000000000000 : ℝ) ≤ (400040355484493/400000000000000 : ℝ) ^ (4879/1024 : ℝ) := by
    have hpowers : (25012018754557445309/25000000000000000000 : ℝ)^1024 ≤ (400040355484493/400000000000000 : ℝ)^4879 := by
      have hnat : (25012018754557445309 : ℕ)^1024*400000000000000^4879 ≤ 400040355484493^4879*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012018754557445309 25000000000000000000 400040355484493 400000000000000 1024 4879 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400040355484493/400000000000000 : ℝ)) (X := (25012018754557445309/25000000000000000000 : ℝ)) (by norm_num) 4879 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(57492531744753/4000000000000000000 : ℝ) ≤ ((3881566643917005689/3882000000000000000 : ℝ)+2*(59284712561/97050000000000 : ℝ)*(9631/100000 : ℝ))^(4879/1024 : ℝ) := by
    rw [show (3881566643917005689/3882000000000000000 : ℝ)+2*(59284712561/97050000000000 : ℝ)*(9631/100000 : ℝ)=(10000060331711349/10000000000000000 : ℝ) by norm_num, show 1+2*(57492531744753/4000000000000000000 : ℝ)=(2000057492531744753/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12018754557445309/50000000000000000000 : ℝ)+(57492531744753/4000000000000000000 : ℝ) ≤ ((3881566643917005689/3882000000000000000 : ℝ)+(59284712561/97050000000000 : ℝ)*((3479/20000 : ℝ)+(9631/100000 : ℝ)))^(4879/1024 : ℝ) := by
    rw [show (3881566643917005689/3882000000000000000 : ℝ)+(59284712561/97050000000000 : ℝ)*((3479/20000 : ℝ)+(9631/100000 : ℝ))=(10000534609411837/10000000000000000 : ℝ) by norm_num, show 1+(12018754557445309/50000000000000000000 : ℝ)+(57492531744753/4000000000000000000 : ℝ)=(100025474822408509443/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12018754557445309/50000000000000000000 : ℝ) ≤ ((3881566643917005689/3882000000000000000 : ℝ)+2*(59284712561/97050000000000 : ℝ)*(3479/20000 : ℝ))^(4879/1024 : ℝ) := by
    rw [show (3881566643917005689/3882000000000000000 : ℝ)+2*(59284712561/97050000000000 : ℝ)*(3479/20000 : ℝ)=(400040355484493/400000000000000 : ℝ) by norm_num, show 1+2*(12018754557445309/50000000000000000000 : ℝ)=(25012018754557445309/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3881566643917005689/3882000000000000000 : ℝ)*(X 1 0+X 2 0)+(59284712561/97050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4879/1024 : ℝ)) (lo := (9631/100000 : ℝ)) (hi := (3479/20000 : ℝ)) (c := (3881566643917005689/3882000000000000000 : ℝ)) (alpha := (59284712561/97050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3881566643917005689/3882000000000000000 : ℝ)*(X 0 1+X 2 1)+(59284712561/97050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4879/1024 : ℝ)) (lo := (9631/100000 : ℝ)) (hi := (3479/20000 : ℝ)) (c := (3881566643917005689/3882000000000000000 : ℝ)) (alpha := (59284712561/97050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3881566643917005689/3882000000000000000 : ℝ)*(X 0 2+X 1 2)+(59284712561/97050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4879/1024 : ℝ)) (lo := (9631/100000 : ℝ)) (hi := (3479/20000 : ℝ)) (c := (3881566643917005689/3882000000000000000 : ℝ)) (alpha := (59284712561/97050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1628420321/10000000000 : ℝ)*X 0 0+(5454359609/10000000000 : ℝ)*X 0 1+(5179680541/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070041559/2000000000 : ℝ)*X 1 0+(-176999397/1000000000 : ℝ)*X 1 1+(647460159/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((83597033/156250000 : ℝ)*X 2 0+(5179679873/10000000000 : ℝ)*X 2 1+(-1769992723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1046783497/2500000000 : ℝ)*X 0 0+(3846656069/10000000000 : ℝ)*X 0 1+(181970771/400000000 : ℝ)*X 0 2+(1046783497/2500000000 : ℝ)*X 1 0+(3846656069/10000000000 : ℝ)*X 1 1+(181970771/400000000 : ℝ)*X 1 2+(1046783497/2500000000 : ℝ)*X 2 0+(3846656069/10000000000 : ℝ)*X 2 1+(181970771/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1628490759/10000000000 : ℝ)*X 0 0+(5181810971/10000000000 : ℝ)*X 0 1+(5452206853/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638452277/5000000000 : ℝ)*X 1 0+(-299493481/2000000000 : ℝ)*X 1 1+(5452206229/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055381079/2000000000 : ℝ)*X 2 0+(5452205739/10000000000 : ℝ)*X 2 1+(-748733461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2093658671/5000000000 : ℝ)*X 0 0+(2271909629/5000000000 : ℝ)*X 0 1+(1926082351/5000000000 : ℝ)*X 0 2+(2093658671/5000000000 : ℝ)*X 1 0+(2271909629/5000000000 : ℝ)*X 1 1+(1926082351/5000000000 : ℝ)*X 1 2+(2093658671/5000000000 : ℝ)*X 2 0+(2271909629/5000000000 : ℝ)*X 2 1+(1926082351/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1641_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52594949148165394074941499/8087500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (79257199/50000000000000 : ℝ)*(base19) + (213052953/12500000000000 : ℝ)*(base23) + (99254677/100000000000000 : ℝ)*(upper4) + (441831243/100000000000000 : ℝ)*(upper5) + (316494514794291/12500000000000 : ℝ)*(major0) + (316494514794291/12500000000000 : ℝ)*(major1) + (316494514794291/12500000000000 : ℝ)*(major2) + (3640617110152841/100000000000000 : ℝ)*(sp0) + (1820314760319117/50000000000000 : ℝ)*(sp1) + (1820319635963141/50000000000000 : ℝ)*(sp2) + (142326472487817/10000000000000 : ℝ)*(sp3) + (4773239413/20000000000000 : ℝ)*(sp4) + (5648598637/50000000000000 : ℝ)*(sp5) + (3159352963/50000000000000 : ℝ)*(sp7) + (44477220112003/3125000000000 : ℝ)*(f.failure) + (1820320488174953/50000000000000 : ℝ)*(f.sum) + (6130521370253/808750000000000000000000000 : ℝ)*base65 + (90666353011096167/16175000000000000000000000000000 : ℝ)*base68 + (75689407860646167/16175000000000000000000000000000 : ℝ)*base70 + (137605040045603833/16175000000000000000000000000000 : ℝ)*base71 + (423144257749/404375000000000000000000000 : ℝ)*base73 + (217649618343046167/16175000000000000000000000000000 : ℝ)*base76 + (38191164759953833/16175000000000000000000000000000 : ℝ)*base77 + (83923365950946167/16175000000000000000000000000000 : ℝ)*base80 + (595680159853/808750000000000000000000000 : ℝ)*base81 + (110539/156250000000000000000 : ℝ)*base90 + (110539/156250000000000000000 : ℝ)*base92 + (110539/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (155026196611188755627221783/16175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (180057217/20000000000000 : ℝ)*(base19) + (147862807/6250000000000 : ℝ)*(base23) + (47097/1000000000000 : ℝ)*(upper3) + (11714101/3125000000000 : ℝ)*(lower4) + (243111519/100000000000000 : ℝ)*(upper5) + (643011305555353/25000000000000 : ℝ)*(major0) + (643011305555353/25000000000000 : ℝ)*(major1) + (643011305555353/25000000000000 : ℝ)*(major2) + (6382861987/100000000000000 : ℝ)*(sp1) + (9157120223/50000000000000 : ℝ)*(sp2) + (1849142034851493/50000000000000 : ℝ)*(sp4) + (739655357310983/20000000000000 : ℝ)*(sp5) + (924565847414407/25000000000000 : ℝ)*(sp6) + (1445806055262869/100000000000000 : ℝ)*(sp7) + (1445806055262869/100000000000000 : ℝ)*(f.failure) + (1849142034851493/50000000000000 : ℝ)*(f.sum) + (7530602764957/1213125000000000000000000000 : ℝ)*base66 + (901150522060323217/97050000000000000000000000000000 : ℝ)*base67 + (450380204599923217/97050000000000000000000000000000 : ℝ)*base69 + (175401366702926783/97050000000000000000000000000000 : ℝ)*base72 + (3123010577179/9705000000000000000000000000 : ℝ)*base73 + (218722280174126783/97050000000000000000000000000000 : ℝ)*base76 + (19327377836223217/97050000000000000000000000000000 : ℝ)*base77 + (77272590240123217/97050000000000000000000000000000 : ℝ)*base79 + (6834099282839/2426250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (15170797/5000000000000000000000 : ℝ)*base90 + (15170797/5000000000000000000000 : ℝ)*base92 + (15170797/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1641_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (88948487/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3479/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9631/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10541/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2047/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1641_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1641_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (88948487/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10541/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2047/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1641_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1641_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1641_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4879/1024 : ℝ) ≤ p) (hpb : p ≤ (4883/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (88948487/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10541/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2047/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1641_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

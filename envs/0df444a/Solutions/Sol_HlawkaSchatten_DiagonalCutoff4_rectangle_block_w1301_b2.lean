-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1301_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:36:42.820845+00:00
-- url     : https://prove2.me/submissions/52791548-b0c7-4776-869b-5fc36bfdbea5

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
theorem support_rectangle_w1301_s6_0 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-129995017/625000000 : ℝ)*x 0 + (216594209/400000000 : ℝ)*x 1 + (5243230559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129995017/625000000 : ℝ)^4261 ≤ (12656569661379/100000000000000 : ℝ)^3237 := by
    have hnat : (129995017 : ℕ)^4261*100000000000000^3237 ≤ 12656569661379^3237*625000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129995017 625000000 12656569661379 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216594209/400000000 : ℝ)^4261 ≤ (44597355071999/100000000000000 : ℝ)^3237 := by
    have hnat : (216594209 : ℕ)^4261*100000000000000^3237 ≤ 44597355071999^3237*400000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216594209 400000000 44597355071999 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243230559/10000000000 : ℝ)^4261 ≤ (42746075253163/100000000000000 : ℝ)^3237 := by
    have hnat : (5243230559 : ℕ)^4261*100000000000000^3237 ≤ 42746075253163^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243230559 10000000000 42746075253163 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-129995017/625000000 : ℝ), (216594209/400000000 : ℝ), (5243230559/10000000000 : ℝ)] ![(12656569661379/100000000000000 : ℝ), (44597355071999/100000000000000 : ℝ), (42746075253163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-129995017/625000000 : ℝ)|^4261 ≤ (12656569661379/100000000000000 : ℝ)^3237
        have hw : |(-129995017/625000000 : ℝ)|=(129995017/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216594209/400000000 : ℝ)|^4261 ≤ (44597355071999/100000000000000 : ℝ)^3237
        have hw : |(216594209/400000000 : ℝ)|=(216594209/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243230559/10000000000 : ℝ)|^4261 ≤ (42746075253163/100000000000000 : ℝ)^3237
        have hw : |(5243230559/10000000000 : ℝ)|=(5243230559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s6_1 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133741811/250000000 : ℝ)*x 0 + (-2167399173/10000000000 : ℝ)*x 1 + (5243230559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133741811/250000000 : ℝ)^4261 ≤ (43892022371661/100000000000000 : ℝ)^3237 := by
    have hnat : (133741811 : ℕ)^4261*100000000000000^3237 ≤ 43892022371661^3237*250000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133741811 250000000 43892022371661 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2167399173/10000000000 : ℝ)^4261 ≤ (66809511787/500000000000 : ℝ)^3237 := by
    have hnat : (2167399173 : ℕ)^4261*500000000000^3237 ≤ 66809511787^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167399173 10000000000 66809511787 500000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243230559/10000000000 : ℝ)^4261 ≤ (42746075253163/100000000000000 : ℝ)^3237 := by
    have hnat : (5243230559 : ℕ)^4261*100000000000000^3237 ≤ 42746075253163^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243230559 10000000000 42746075253163 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133741811/250000000 : ℝ), (-2167399173/10000000000 : ℝ), (5243230559/10000000000 : ℝ)] ![(43892022371661/100000000000000 : ℝ), (66809511787/500000000000 : ℝ), (42746075253163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133741811/250000000 : ℝ)|^4261 ≤ (43892022371661/100000000000000 : ℝ)^3237
        have hw : |(133741811/250000000 : ℝ)|=(133741811/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2167399173/10000000000 : ℝ)|^4261 ≤ (66809511787/500000000000 : ℝ)^3237
        have hw : |(-2167399173/10000000000 : ℝ)|=(2167399173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243230559/10000000000 : ℝ)|^4261 ≤ (42746075253163/100000000000000 : ℝ)^3237
        have hw : |(5243230559/10000000000 : ℝ)|=(5243230559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s6_2 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349672439/10000000000 : ℝ)*x 0 + (5243230559/10000000000 : ℝ)*x 1 + (-2167399173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349672439/10000000000 : ℝ)^4261 ≤ (43892022360861/100000000000000 : ℝ)^3237 := by
    have hnat : (5349672439 : ℕ)^4261*100000000000000^3237 ≤ 43892022360861^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349672439 10000000000 43892022360861 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243230559/10000000000 : ℝ)^4261 ≤ (42746075253163/100000000000000 : ℝ)^3237 := by
    have hnat : (5243230559 : ℕ)^4261*100000000000000^3237 ≤ 42746075253163^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243230559 10000000000 42746075253163 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2167399173/10000000000 : ℝ)^4261 ≤ (66809511787/500000000000 : ℝ)^3237 := by
    have hnat : (2167399173 : ℕ)^4261*500000000000^3237 ≤ 66809511787^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167399173 10000000000 66809511787 500000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349672439/10000000000 : ℝ), (5243230559/10000000000 : ℝ), (-2167399173/10000000000 : ℝ)] ![(43892022360861/100000000000000 : ℝ), (42746075253163/100000000000000 : ℝ), (66809511787/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349672439/10000000000 : ℝ)|^4261 ≤ (43892022360861/100000000000000 : ℝ)^3237
        have hw : |(5349672439/10000000000 : ℝ)|=(5349672439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243230559/10000000000 : ℝ)|^4261 ≤ (42746075253163/100000000000000 : ℝ)^3237
        have hw : |(5243230559/10000000000 : ℝ)|=(5243230559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2167399173/10000000000 : ℝ)|^4261 ≤ (66809511787/500000000000 : ℝ)^3237
        have hw : |(-2167399173/10000000000 : ℝ)|=(2167399173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s6_3 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4337451337/10000000000 : ℝ)*x 0 + (4163916913/10000000000 : ℝ)*x 1 + (1129464929/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4337451337/10000000000 : ℝ)^4261 ≤ (4162810056401/12500000000000 : ℝ)^3237 := by
    have hnat : (4337451337 : ℕ)^4261*12500000000000^3237 ≤ 4162810056401^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4337451337 10000000000 4162810056401 12500000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4163916913/10000000000 : ℝ)^4261 ≤ (31559816025539/100000000000000 : ℝ)^3237 := by
    have hnat : (4163916913 : ℕ)^4261*100000000000000^3237 ≤ 31559816025539^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163916913 10000000000 31559816025539 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129464929/2500000000 : ℝ)^4261 ≤ (7027540702533/20000000000000 : ℝ)^3237 := by
    have hnat : (1129464929 : ℕ)^4261*20000000000000^3237 ≤ 7027540702533^3237*2500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129464929 2500000000 7027540702533 20000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4337451337/10000000000 : ℝ), (4163916913/10000000000 : ℝ), (1129464929/2500000000 : ℝ)] ![(4162810056401/12500000000000 : ℝ), (31559816025539/100000000000000 : ℝ), (7027540702533/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4337451337/10000000000 : ℝ)|^4261 ≤ (4162810056401/12500000000000 : ℝ)^3237
        have hw : |(4337451337/10000000000 : ℝ)|=(4337451337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4163916913/10000000000 : ℝ)|^4261 ≤ (31559816025539/100000000000000 : ℝ)^3237
        have hw : |(4163916913/10000000000 : ℝ)|=(4163916913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1129464929/2500000000 : ℝ)|^4261 ≤ (7027540702533/20000000000000 : ℝ)^3237
        have hw : |(1129464929/2500000000 : ℝ)|=(1129464929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s6_4 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2079932917/10000000000 : ℝ)*x 0 + (2621921601/5000000000 : ℝ)*x 1 + (1353559857/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079932917/10000000000 : ℝ)^4261 ≤ (6328335474621/50000000000000 : ℝ)^3237 := by
    have hnat : (2079932917 : ℕ)^4261*50000000000000^3237 ≤ 6328335474621^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079932917 10000000000 6328335474621 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621921601/5000000000 : ℝ)^4261 ≤ (42752650039247/100000000000000 : ℝ)^3237 := by
    have hnat : (2621921601 : ℕ)^4261*100000000000000^3237 ≤ 42752650039247^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621921601 5000000000 42752650039247 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353559857/2500000000 : ℝ)^4261 ≤ (5573834875321/12500000000000 : ℝ)^3237 := by
    have hnat : (1353559857 : ℕ)^4261*12500000000000^3237 ≤ 5573834875321^3237*2500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353559857 2500000000 5573834875321 12500000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2079932917/10000000000 : ℝ), (2621921601/5000000000 : ℝ), (1353559857/2500000000 : ℝ)] ![(6328335474621/50000000000000 : ℝ), (42752650039247/100000000000000 : ℝ), (5573834875321/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2079932917/10000000000 : ℝ)|^4261 ≤ (6328335474621/50000000000000 : ℝ)^3237
        have hw : |(-2079932917/10000000000 : ℝ)|=(2079932917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621921601/5000000000 : ℝ)|^4261 ≤ (42752650039247/100000000000000 : ℝ)^3237
        have hw : |(2621921601/5000000000 : ℝ)|=(2621921601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353559857/2500000000 : ℝ)|^4261 ≤ (5573834875321/12500000000000 : ℝ)^3237
        have hw : |(1353559857/2500000000 : ℝ)|=(1353559857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s6_5 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652841211/5000000000 : ℝ)*x 0 + (-1996390323/10000000000 : ℝ)*x 1 + (1082847881/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652841211/5000000000 : ℝ)^4261 ≤ (678399147763/1562500000000 : ℝ)^3237 := by
    have hnat : (2652841211 : ℕ)^4261*1562500000000^3237 ≤ 678399147763^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652841211 5000000000 678399147763 1562500000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1996390323/10000000000 : ℝ)^4261 ≤ (1199177578193/10000000000000 : ℝ)^3237 := by
    have hnat : (1996390323 : ℕ)^4261*10000000000000^3237 ≤ 1199177578193^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1996390323 10000000000 1199177578193 10000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082847881/2000000000 : ℝ)^4261 ≤ (22295339376611/50000000000000 : ℝ)^3237 := by
    have hnat : (1082847881 : ℕ)^4261*50000000000000^3237 ≤ 22295339376611^3237*2000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082847881 2000000000 22295339376611 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652841211/5000000000 : ℝ), (-1996390323/10000000000 : ℝ), (1082847881/2000000000 : ℝ)] ![(678399147763/1562500000000 : ℝ), (1199177578193/10000000000000 : ℝ), (22295339376611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652841211/5000000000 : ℝ)|^4261 ≤ (678399147763/1562500000000 : ℝ)^3237
        have hw : |(2652841211/5000000000 : ℝ)|=(2652841211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1996390323/10000000000 : ℝ)|^4261 ≤ (1199177578193/10000000000000 : ℝ)^3237
        have hw : |(-1996390323/10000000000 : ℝ)|=(1996390323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082847881/2000000000 : ℝ)|^4261 ≤ (22295339376611/50000000000000 : ℝ)^3237
        have hw : |(1082847881/2000000000 : ℝ)|=(1082847881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s6_6 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305682439/10000000000 : ℝ)*x 0 + (1082847861/2000000000 : ℝ)*x 1 + (-499097609/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305682439/10000000000 : ℝ)^4261 ≤ (8683509127991/20000000000000 : ℝ)^3237 := by
    have hnat : (5305682439 : ℕ)^4261*20000000000000^3237 ≤ 8683509127991^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305682439 10000000000 8683509127991 20000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082847861/2000000000 : ℝ)^4261 ≤ (44590677669107/100000000000000 : ℝ)^3237 := by
    have hnat : (1082847861 : ℕ)^4261*100000000000000^3237 ≤ 44590677669107^3237*2000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082847861 2000000000 44590677669107 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (499097609/2500000000 : ℝ)^4261 ≤ (11991776675411/100000000000000 : ℝ)^3237 := by
    have hnat : (499097609 : ℕ)^4261*100000000000000^3237 ≤ 11991776675411^3237*2500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499097609 2500000000 11991776675411 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305682439/10000000000 : ℝ), (1082847861/2000000000 : ℝ), (-499097609/2500000000 : ℝ)] ![(8683509127991/20000000000000 : ℝ), (44590677669107/100000000000000 : ℝ), (11991776675411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305682439/10000000000 : ℝ)|^4261 ≤ (8683509127991/20000000000000 : ℝ)^3237
        have hw : |(5305682439/10000000000 : ℝ)|=(5305682439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082847861/2000000000 : ℝ)|^4261 ≤ (44590677669107/100000000000000 : ℝ)^3237
        have hw : |(1082847861/2000000000 : ℝ)|=(1082847861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-499097609/2500000000 : ℝ)|^4261 ≤ (11991776675411/100000000000000 : ℝ)^3237
        have hw : |(-499097609/2500000000 : ℝ)|=(499097609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s6_7 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (216873869/500000000 : ℝ)*x 0 + (4516596113/10000000000 : ℝ)*x 1 + (4165187051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216873869/500000000 : ℝ)^4261 ≤ (3330274366111/10000000000000 : ℝ)^3237 := by
    have hnat : (216873869 : ℕ)^4261*10000000000000^3237 ≤ 3330274366111^3237*500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216873869 500000000 3330274366111 10000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4516596113/10000000000 : ℝ)^4261 ≤ (35124767486027/100000000000000 : ℝ)^3237 := by
    have hnat : (4516596113 : ℕ)^4261*100000000000000^3237 ≤ 35124767486027^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516596113 10000000000 35124767486027 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4165187051/10000000000 : ℝ)^4261 ≤ (31572488840797/100000000000000 : ℝ)^3237 := by
    have hnat : (4165187051 : ℕ)^4261*100000000000000^3237 ≤ 31572488840797^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165187051 10000000000 31572488840797 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216873869/500000000 : ℝ), (4516596113/10000000000 : ℝ), (4165187051/10000000000 : ℝ)] ![(3330274366111/10000000000000 : ℝ), (35124767486027/100000000000000 : ℝ), (31572488840797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216873869/500000000 : ℝ)|^4261 ≤ (3330274366111/10000000000000 : ℝ)^3237
        have hw : |(216873869/500000000 : ℝ)|=(216873869/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4516596113/10000000000 : ℝ)|^4261 ≤ (35124767486027/100000000000000 : ℝ)^3237
        have hw : |(4516596113/10000000000 : ℝ)|=(4516596113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4165187051/10000000000 : ℝ)|^4261 ≤ (31572488840797/100000000000000 : ℝ)^3237
        have hw : |(4165187051/10000000000 : ℝ)|=(4165187051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1301_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5519/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1381/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14681/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3673/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5519/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3673/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5519/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3673/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5519/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3673/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5519/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3673/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5519/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3673/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5519/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5519/50000 : ℝ) ^ (1065/256 : ℝ) ≤ (10429763792967421/100000000000000000000 : ℝ) := by
    have hpowers : (5519/50000 : ℝ)^1065 ≤ (10429763792967421/100000000000000000000 : ℝ)^256 := by
      have hnat : (5519 : ℕ)^1065*100000000000000000000^256 ≤ 10429763792967421^256*50000^1065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5519 50000 10429763792967421 100000000000000000000 1065 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5519/50000 : ℝ)) (X := (10429763792967421/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3673/25000 : ℝ) ^ (1065/256 : ℝ) ≤ (6854195348283471/20000000000000000000 : ℝ) := by
    have hpowers : (3673/25000 : ℝ)^1065 ≤ (6854195348283471/20000000000000000000 : ℝ)^256 := by
      have hnat : (3673 : ℕ)^1065*20000000000000000000^256 ≤ 6854195348283471^256*25000^1065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3673 25000 6854195348283471 20000000000000000000 1065 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3673/25000 : ℝ)) (X := (6854195348283471/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010429763792967421/50000000000000000000 : ℝ) ≤ (2500125343099491/2500000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (50010429763792967421/50000000000000000000 : ℝ)^256 ≤ (2500125343099491/2500000000000000 : ℝ)^1065 := by
      have hnat : (50010429763792967421 : ℕ)^256*2500000000000000^1065 ≤ 2500125343099491^1065*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010429763792967421 50000000000000000000 2500125343099491 2500000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500125343099491/2500000000000000 : ℝ)) (X := (50010429763792967421/50000000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505587592566798097/12500000000000000000 : ℝ) ≤ (625067144643429/625000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (12505587592566798097/12500000000000000000 : ℝ)^256 ≤ (625067144643429/625000000000000 : ℝ)^1065 := by
      have hnat : (12505587592566798097 : ℕ)^256*625000000000000^1065 ≤ 625067144643429^1065*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505587592566798097 12500000000000000000 625067144643429 625000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625067144643429/625000000000000 : ℝ)) (X := (12505587592566798097/12500000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006854195348283471/10000000000000000000 : ℝ) ≤ (2500411814047941/2500000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (10006854195348283471/10000000000000000000 : ℝ)^256 ≤ (2500411814047941/2500000000000000 : ℝ)^1065 := by
      have hnat : (10006854195348283471 : ℕ)^256*2500000000000000^1065 ≤ 2500411814047941^1065*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006854195348283471 10000000000000000000 2500411814047941 2500000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500411814047941/2500000000000000 : ℝ)) (X := (10006854195348283471/10000000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10429763792967421/100000000000000000000 : ℝ) ≤ ((1522049322892758169/1522500000000000000 : ℝ)+2*(1909806323/1218000000000 : ℝ)*(5519/50000 : ℝ))^(1065/256 : ℝ) := by
    rw [show (1522049322892758169/1522500000000000000 : ℝ)+2*(1909806323/1218000000000 : ℝ)*(5519/50000 : ℝ)=(2500125343099491/2500000000000000 : ℝ) by norm_num, show 1+2*(10429763792967421/100000000000000000000 : ℝ)=(50010429763792967421/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6854195348283471/20000000000000000000 : ℝ)+(10429763792967421/100000000000000000000 : ℝ) ≤ ((1522049322892758169/1522500000000000000 : ℝ)+(1909806323/1218000000000 : ℝ)*((3673/25000 : ℝ)+(5519/50000 : ℝ)))^(1065/256 : ℝ) := by
    rw [show (1522049322892758169/1522500000000000000 : ℝ)+(1909806323/1218000000000 : ℝ)*((3673/25000 : ℝ)+(5519/50000 : ℝ))=(625067144643429/625000000000000 : ℝ) by norm_num, show 1+(6854195348283471/20000000000000000000 : ℝ)+(10429763792967421/100000000000000000000 : ℝ)=(12505587592566798097/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6854195348283471/20000000000000000000 : ℝ) ≤ ((1522049322892758169/1522500000000000000 : ℝ)+2*(1909806323/1218000000000 : ℝ)*(3673/25000 : ℝ))^(1065/256 : ℝ) := by
    rw [show (1522049322892758169/1522500000000000000 : ℝ)+2*(1909806323/1218000000000 : ℝ)*(3673/25000 : ℝ)=(2500411814047941/2500000000000000 : ℝ) by norm_num, show 1+2*(6854195348283471/20000000000000000000 : ℝ)=(10006854195348283471/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1522049322892758169/1522500000000000000 : ℝ)*(X 1 0+X 2 0)+(1909806323/1218000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (5519/50000 : ℝ)) (hi := (3673/25000 : ℝ)) (c := (1522049322892758169/1522500000000000000 : ℝ)) (alpha := (1909806323/1218000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1522049322892758169/1522500000000000000 : ℝ)*(X 0 1+X 2 1)+(1909806323/1218000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (5519/50000 : ℝ)) (hi := (3673/25000 : ℝ)) (c := (1522049322892758169/1522500000000000000 : ℝ)) (alpha := (1909806323/1218000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1522049322892758169/1522500000000000000 : ℝ)*(X 0 2+X 1 2)+(1909806323/1218000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (5519/50000 : ℝ)) (hi := (3673/25000 : ℝ)) (c := (1522049322892758169/1522500000000000000 : ℝ)) (alpha := (1909806323/1218000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-129995017/625000000 : ℝ)*X 0 0+(216594209/400000000 : ℝ)*X 0 1+(5243230559/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133741811/250000000 : ℝ)*X 1 0+(-2167399173/10000000000 : ℝ)*X 1 1+(5243230559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349672439/10000000000 : ℝ)*X 2 0+(5243230559/10000000000 : ℝ)*X 2 1+(-2167399173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4337451337/10000000000 : ℝ)*X 0 0+(4163916913/10000000000 : ℝ)*X 0 1+(1129464929/2500000000 : ℝ)*X 0 2+(4337451337/10000000000 : ℝ)*X 1 0+(4163916913/10000000000 : ℝ)*X 1 1+(1129464929/2500000000 : ℝ)*X 1 2+(4337451337/10000000000 : ℝ)*X 2 0+(4163916913/10000000000 : ℝ)*X 2 1+(1129464929/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2079932917/10000000000 : ℝ)*X 0 0+(2621921601/5000000000 : ℝ)*X 0 1+(1353559857/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652841211/5000000000 : ℝ)*X 1 0+(-1996390323/10000000000 : ℝ)*X 1 1+(1082847881/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305682439/10000000000 : ℝ)*X 2 0+(1082847861/2000000000 : ℝ)*X 2 1+(-499097609/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((216873869/500000000 : ℝ)*X 0 0+(4516596113/10000000000 : ℝ)*X 0 1+(4165187051/10000000000 : ℝ)*X 0 2+(216873869/500000000 : ℝ)*X 1 0+(4516596113/10000000000 : ℝ)*X 1 1+(4165187051/10000000000 : ℝ)*X 1 2+(216873869/500000000 : ℝ)*X 2 0+(4516596113/10000000000 : ℝ)*X 2 1+(4165187051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9139723742031140564133339/875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (199768177/10000000000000 : ℝ)*(base19) + (1860846351/100000000000000 : ℝ)*(base23) + (72619793/100000000000000 : ℝ)*(lower2) + (52795481/20000000000000 : ℝ)*(upper3) + (162308889/100000000000000 : ℝ)*(upper5) + (540756622969989/12500000000000 : ℝ)*(major0) + (540756622969989/12500000000000 : ℝ)*(major1) + (4326052983759913/100000000000000 : ℝ)*(major2) + (2913355134926441/50000000000000 : ℝ)*(sp0) + (2913374201528911/50000000000000 : ℝ)*(sp1) + (5826748539893241/100000000000000 : ℝ)*(sp2) + (282533414309033/10000000000000 : ℝ)*(sp3) + (4013088671/10000000000000 : ℝ)*(sp4) + (10537754973/50000000000000 : ℝ)*(sp7) + (706338804650069/25000000000000 : ℝ)*(f.failure) + (728343800092449/12500000000000 : ℝ)*(f.sum) + (1380756516331/609000000000000000000000000 : ℝ)*base65 + (154828999741753609/19031250000000000000000000000000 : ℝ)*base68 + (272529434036479297/152250000000000000000000000000000 : ℝ)*base69 + (166016963710753609/19031250000000000000000000000000 : ℝ)*base72 + (2907927611663/609000000000000000000000000 : ℝ)*base74 + (556542737981479297/152250000000000000000000000000000 : ℝ)*base75 + (35639395580529/906250000000000000000000000000 : ℝ)*base78 + (2342391944356971/906250000000000000000000000000 : ℝ)*base79 + (811950852179/203000000000000000000000000 : ℝ)*base82 + (8430127/1250000000000000000000 : ℝ)*base89 + (8430127/1250000000000000000000 : ℝ)*base91 + (4069873/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53402264786413032484659869/6343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (373925001/25000000000000 : ℝ)*(base19) + (196218507/12500000000000 : ℝ)*(base23) + (12717451/10000000000000 : ℝ)*(upper3) + (6079667/12500000000000 : ℝ)*(lower4) + (207624359/100000000000000 : ℝ)*(upper5) + (2178590359614449/50000000000000 : ℝ)*(major0) + (2178590359614449/50000000000000 : ℝ)*(major1) + (2178590359614449/50000000000000 : ℝ)*(major2) + (15941273257/50000000000000 : ℝ)*(sp1) + (5497833203/20000000000000 : ℝ)*(sp2) + (58686763431583/1000000000000 : ℝ)*(sp4) + (5868642964911781/100000000000000 : ℝ)*(sp5) + (5868647284244229/100000000000000 : ℝ)*(sp6) + (1422842407348227/50000000000000 : ℝ)*(sp7) + (1422842407348227/50000000000000 : ℝ)*(f.failure) + (58686763431583/1000000000000 : ℝ)*(f.sum) + (8240781547/7612500000000000000000000 : ℝ)*base65 + (124526829111311983/10875000000000000000000000000000 : ℝ)*base67 + (26110513354188017/10875000000000000000000000000000 : ℝ)*base70 + (91865524446311983/10875000000000000000000000000000 : ℝ)*base71 + (1379645154287/609000000000000000000000000 : ℝ)*base73 + (60049945008686983/10875000000000000000000000000000 : ℝ)*base75 + (20774916754061983/10875000000000000000000000000000 : ℝ)*base77 + (97572090760061983/10875000000000000000000000000000 : ℝ)*base79 + (109627866421/121800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (16721959/2500000000000000000000 : ℝ)*base90 + (16721959/2500000000000000000000 : ℝ)*base92 + (16721959/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1301_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5519/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1381/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1301_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1301_s7_0 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-207993307/1000000000 : ℝ)*x 0 + (2707380943/5000000000 : ℝ)*x 1 + (5243315301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207993307/1000000000 : ℝ)^4261 ≤ (12656672174791/100000000000000 : ℝ)^3237 := by
    have hnat : (207993307 : ℕ)^4261*100000000000000^3237 ≤ 12656672174791^3237*1000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207993307 1000000000 12656672174791 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707380943/5000000000 : ℝ)^4261 ≤ (8919268627199/20000000000000 : ℝ)^3237 := by
    have hnat : (2707380943 : ℕ)^4261*20000000000000^3237 ≤ 8919268627199^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707380943 5000000000 8919268627199 20000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243315301/10000000000 : ℝ)^4261 ≤ (42746984676187/100000000000000 : ℝ)^3237 := by
    have hnat : (5243315301 : ℕ)^4261*100000000000000^3237 ≤ 42746984676187^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243315301 10000000000 42746984676187 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-207993307/1000000000 : ℝ), (2707380943/5000000000 : ℝ), (5243315301/10000000000 : ℝ)] ![(12656672174791/100000000000000 : ℝ), (8919268627199/20000000000000 : ℝ), (42746984676187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-207993307/1000000000 : ℝ)|^4261 ≤ (12656672174791/100000000000000 : ℝ)^3237
        have hw : |(-207993307/1000000000 : ℝ)|=(207993307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707380943/5000000000 : ℝ)|^4261 ≤ (8919268627199/20000000000000 : ℝ)^3237
        have hw : |(2707380943/5000000000 : ℝ)|=(2707380943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243315301/10000000000 : ℝ)|^4261 ≤ (42746984676187/100000000000000 : ℝ)^3237
        have hw : |(5243315301/10000000000 : ℝ)|=(5243315301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s7_1 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674824387/5000000000 : ℝ)*x 0 + (-433463731/2000000000 : ℝ)*x 1 + (2621657631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674824387/5000000000 : ℝ)^4261 ≤ (1371617711781/3125000000000 : ℝ)^3237 := by
    have hnat : (2674824387 : ℕ)^4261*3125000000000^3237 ≤ 1371617711781^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674824387 5000000000 1371617711781 3125000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (433463731/2000000000 : ℝ)^4261 ≤ (6680624471537/50000000000000 : ℝ)^3237 := by
    have hnat : (433463731 : ℕ)^4261*50000000000000^3237 ≤ 6680624471537^3237*2000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433463731 2000000000 6680624471537 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621657631/5000000000 : ℝ)^4261 ≤ (42746984257651/100000000000000 : ℝ)^3237 := by
    have hnat : (2621657631 : ℕ)^4261*100000000000000^3237 ≤ 42746984257651^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621657631 5000000000 42746984257651 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674824387/5000000000 : ℝ), (-433463731/2000000000 : ℝ), (2621657631/5000000000 : ℝ)] ![(1371617711781/3125000000000 : ℝ), (6680624471537/50000000000000 : ℝ), (42746984257651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674824387/5000000000 : ℝ)|^4261 ≤ (1371617711781/3125000000000 : ℝ)^3237
        have hw : |(2674824387/5000000000 : ℝ)|=(2674824387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-433463731/2000000000 : ℝ)|^4261 ≤ (6680624471537/50000000000000 : ℝ)^3237
        have hw : |(-433463731/2000000000 : ℝ)|=(433463731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621657631/5000000000 : ℝ)|^4261 ≤ (42746984257651/100000000000000 : ℝ)^3237
        have hw : |(2621657631/5000000000 : ℝ)|=(2621657631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s7_2 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349647571/10000000000 : ℝ)*x 0 + (524331851/1000000000 : ℝ)*x 1 + (-1083657981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349647571/10000000000 : ℝ)^4261 ≤ (21945876892253/50000000000000 : ℝ)^3237 := by
    have hnat : (5349647571 : ℕ)^4261*50000000000000^3237 ≤ 21945876892253^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349647571 10000000000 21945876892253 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524331851/1000000000 : ℝ)^4261 ≤ (21373509557101/50000000000000 : ℝ)^3237 := by
    have hnat : (524331851 : ℕ)^4261*50000000000000^3237 ≤ 21373509557101^3237*1000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524331851 1000000000 21373509557101 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083657981/5000000000 : ℝ)^4261 ≤ (52192293317/390625000000 : ℝ)^3237 := by
    have hnat : (1083657981 : ℕ)^4261*390625000000^3237 ≤ 52192293317^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083657981 5000000000 52192293317 390625000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349647571/10000000000 : ℝ), (524331851/1000000000 : ℝ), (-1083657981/5000000000 : ℝ)] ![(21945876892253/50000000000000 : ℝ), (21373509557101/50000000000000 : ℝ), (52192293317/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349647571/10000000000 : ℝ)|^4261 ≤ (21945876892253/50000000000000 : ℝ)^3237
        have hw : |(5349647571/10000000000 : ℝ)|=(5349647571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524331851/1000000000 : ℝ)|^4261 ≤ (21373509557101/50000000000000 : ℝ)^3237
        have hw : |(524331851/1000000000 : ℝ)|=(524331851/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1083657981/5000000000 : ℝ)|^4261 ≤ (52192293317/390625000000 : ℝ)^3237
        have hw : |(-1083657981/5000000000 : ℝ)|=(1083657981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s7_3 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2168730007/5000000000 : ℝ)*x 0 + (2082050559/5000000000 : ℝ)*x 1 + (903534327/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168730007/5000000000 : ℝ)^4261 ≤ (33302568147359/100000000000000 : ℝ)^3237 := by
    have hnat : (2168730007 : ℕ)^4261*100000000000000^3237 ≤ 33302568147359^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168730007 5000000000 33302568147359 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082050559/5000000000 : ℝ)^4261 ≤ (1578082692853/5000000000000 : ℝ)^3237 := by
    have hnat : (2082050559 : ℕ)^4261*5000000000000^3237 ≤ 1578082692853^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082050559 5000000000 1578082692853 5000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903534327/2000000000 : ℝ)^4261 ≤ (548996530893/1562500000000 : ℝ)^3237 := by
    have hnat : (903534327 : ℕ)^4261*1562500000000^3237 ≤ 548996530893^3237*2000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903534327 2000000000 548996530893 1562500000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2168730007/5000000000 : ℝ), (2082050559/5000000000 : ℝ), (903534327/2000000000 : ℝ)] ![(33302568147359/100000000000000 : ℝ), (1578082692853/5000000000000 : ℝ), (548996530893/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2168730007/5000000000 : ℝ)|^4261 ≤ (33302568147359/100000000000000 : ℝ)^3237
        have hw : |(2168730007/5000000000 : ℝ)|=(2168730007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2082050559/5000000000 : ℝ)|^4261 ≤ (1578082692853/5000000000000 : ℝ)^3237
        have hw : |(2082050559/5000000000 : ℝ)|=(2082050559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(903534327/2000000000 : ℝ)|^4261 ≤ (548996530893/1562500000000 : ℝ)^3237
        have hw : |(903534327/2000000000 : ℝ)|=(903534327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s7_4 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2079944559/10000000000 : ℝ)*x 0 + (5243928129/10000000000 : ℝ)*x 1 + (5414146753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079944559/10000000000 : ℝ)^4261 ≤ (98880970337/781250000000 : ℝ)^3237 := by
    have hnat : (2079944559 : ℕ)^4261*781250000000^3237 ≤ 98880970337^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079944559 10000000000 98880970337 781250000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243928129/10000000000 : ℝ)^4261 ≤ (21376780740661/50000000000000 : ℝ)^3237 := by
    have hnat : (5243928129 : ℕ)^4261*50000000000000^3237 ≤ 21376780740661^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243928129 10000000000 21376780740661 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414146753/10000000000 : ℝ)^4261 ≤ (22294837150729/50000000000000 : ℝ)^3237 := by
    have hnat : (5414146753 : ℕ)^4261*50000000000000^3237 ≤ 22294837150729^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414146753 10000000000 22294837150729 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2079944559/10000000000 : ℝ), (5243928129/10000000000 : ℝ), (5414146753/10000000000 : ℝ)] ![(98880970337/781250000000 : ℝ), (21376780740661/50000000000000 : ℝ), (22294837150729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2079944559/10000000000 : ℝ)|^4261 ≤ (98880970337/781250000000 : ℝ)^3237
        have hw : |(-2079944559/10000000000 : ℝ)|=(2079944559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243928129/10000000000 : ℝ)|^4261 ≤ (21376780740661/50000000000000 : ℝ)^3237
        have hw : |(5243928129/10000000000 : ℝ)|=(5243928129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414146753/10000000000 : ℝ)|^4261 ≤ (22294837150729/50000000000000 : ℝ)^3237
        have hw : |(5414146753/10000000000 : ℝ)|=(5414146753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s7_5 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652851967/5000000000 : ℝ)*x 0 + (-24956097/125000000 : ℝ)*x 1 + (5414146963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652851967/5000000000 : ℝ)^4261 ≤ (43417777182381/100000000000000 : ℝ)^3237 := by
    have hnat : (2652851967 : ℕ)^4261*100000000000000^3237 ≤ 43417777182381^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652851967 5000000000 43417777182381 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24956097/125000000 : ℝ)^4261 ≤ (5996273106807/50000000000000 : ℝ)^3237 := by
    have hnat : (24956097 : ℕ)^4261*50000000000000^3237 ≤ 5996273106807^3237*125000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24956097 125000000 5996273106807 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414146963/10000000000 : ℝ)^4261 ≤ (5573709572261/12500000000000 : ℝ)^3237 := by
    have hnat : (5414146963 : ℕ)^4261*12500000000000^3237 ≤ 5573709572261^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414146963 10000000000 5573709572261 12500000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652851967/5000000000 : ℝ), (-24956097/125000000 : ℝ), (5414146963/10000000000 : ℝ)] ![(43417777182381/100000000000000 : ℝ), (5996273106807/50000000000000 : ℝ), (5573709572261/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652851967/5000000000 : ℝ)|^4261 ≤ (43417777182381/100000000000000 : ℝ)^3237
        have hw : |(2652851967/5000000000 : ℝ)|=(2652851967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-24956097/125000000 : ℝ)|^4261 ≤ (5996273106807/50000000000000 : ℝ)^3237
        have hw : |(-24956097/125000000 : ℝ)|=(24956097/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414146963/10000000000 : ℝ)|^4261 ≤ (5573709572261/12500000000000 : ℝ)^3237
        have hw : |(5414146963/10000000000 : ℝ)|=(5414146963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s7_6 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326426049/2500000000 : ℝ)*x 0 + (1353536699/2500000000 : ℝ)*x 1 + (-1996487633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326426049/2500000000 : ℝ)^4261 ≤ (21708890002313/50000000000000 : ℝ)^3237 := by
    have hnat : (1326426049 : ℕ)^4261*50000000000000^3237 ≤ 21708890002313^3237*2500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326426049 2500000000 21708890002313 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353536699/2500000000 : ℝ)^4261 ≤ (356717398141/800000000000 : ℝ)^3237 := by
    have hnat : (1353536699 : ℕ)^4261*800000000000^3237 ≤ 356717398141^3237*2500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353536699 2500000000 356717398141 800000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1996487633/10000000000 : ℝ)^4261 ≤ (11992545209421/100000000000000 : ℝ)^3237 := by
    have hnat : (1996487633 : ℕ)^4261*100000000000000^3237 ≤ 11992545209421^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1996487633 10000000000 11992545209421 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326426049/2500000000 : ℝ), (1353536699/2500000000 : ℝ), (-1996487633/10000000000 : ℝ)] ![(21708890002313/50000000000000 : ℝ), (356717398141/800000000000 : ℝ), (11992545209421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326426049/2500000000 : ℝ)|^4261 ≤ (21708890002313/50000000000000 : ℝ)^3237
        have hw : |(1326426049/2500000000 : ℝ)|=(1326426049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353536699/2500000000 : ℝ)|^4261 ≤ (356717398141/800000000000 : ℝ)^3237
        have hw : |(1353536699/2500000000 : ℝ)|=(1353536699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1996487633/10000000000 : ℝ)|^4261 ≤ (11992545209421/100000000000000 : ℝ)^3237
        have hw : |(-1996487633/10000000000 : ℝ)|=(1996487633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s7_7 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4337483849/10000000000 : ℝ)*x 0 + (2258205983/5000000000 : ℝ)*x 1 + (4165369423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4337483849/10000000000 : ℝ)^4261 ≤ (33302809041707/100000000000000 : ℝ)^3237 := by
    have hnat : (4337483849 : ℕ)^4261*100000000000000^3237 ≤ 33302809041707^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4337483849 10000000000 33302809041707 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2258205983/5000000000 : ℝ)^4261 ≤ (1756144119629/5000000000000 : ℝ)^3237 := by
    have hnat : (2258205983 : ℕ)^4261*5000000000000^3237 ≤ 1756144119629^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258205983 5000000000 1756144119629 5000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4165369423/10000000000 : ℝ)^4261 ≤ (7893577139931/25000000000000 : ℝ)^3237 := by
    have hnat : (4165369423 : ℕ)^4261*25000000000000^3237 ≤ 7893577139931^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165369423 10000000000 7893577139931 25000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4337483849/10000000000 : ℝ), (2258205983/5000000000 : ℝ), (4165369423/10000000000 : ℝ)] ![(33302809041707/100000000000000 : ℝ), (1756144119629/5000000000000 : ℝ), (7893577139931/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4337483849/10000000000 : ℝ)|^4261 ≤ (33302809041707/100000000000000 : ℝ)^3237
        have hw : |(4337483849/10000000000 : ℝ)|=(4337483849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2258205983/5000000000 : ℝ)|^4261 ≤ (1756144119629/5000000000000 : ℝ)^3237
        have hw : |(2258205983/5000000000 : ℝ)|=(2258205983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4165369423/10000000000 : ℝ)|^4261 ≤ (7893577139931/25000000000000 : ℝ)^3237
        have hw : |(4165369423/10000000000 : ℝ)|=(4165369423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1301_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1381/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (221/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14679/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14681/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1381/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14681/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1381/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14681/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1381/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14681/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1381/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14681/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1381/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14681/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1381/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1381/12500 : ℝ) ^ (1065/256 : ℝ) ≤ (65432057855667/625000000000000000 : ℝ) := by
    have hpowers : (1381/12500 : ℝ)^1065 ≤ (65432057855667/625000000000000000 : ℝ)^256 := by
      have hnat : (1381 : ℕ)^1065*625000000000000000^256 ≤ 65432057855667^256*12500^1065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1381 12500 65432057855667 625000000000000000 1065 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1381/12500 : ℝ)) (X := (65432057855667/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14681/100000 : ℝ) ^ (1065/256 : ℝ) ≤ (34164357868724301/100000000000000000000 : ℝ) := by
    have hpowers : (14681/100000 : ℝ)^1065 ≤ (34164357868724301/100000000000000000000 : ℝ)^256 := by
      have hnat : (14681 : ℕ)^1065*100000000000000000000^256 ≤ 34164357868724301^256*100000^1065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14681 100000 34164357868724301 100000000000000000000 1065 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14681/100000 : ℝ)) (X := (34164357868724301/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (312565432057855667/312500000000000000 : ℝ) ≤ (5000251632298439/5000000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (312565432057855667/312500000000000000 : ℝ)^256 ≤ (5000251632298439/5000000000000000 : ℝ)^1065 := by
      have hnat : (312565432057855667 : ℕ)^256*5000000000000000^1065 ≤ 5000251632298439^1065*312500000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312565432057855667 312500000000000000 5000251632298439 5000000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000251632298439/5000000000000000 : ℝ)) (X := (312565432057855667/312500000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044633487125631021/100000000000000000000 : ℝ) ≤ (625067043639713/625000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (100044633487125631021/100000000000000000000 : ℝ)^256 ≤ (625067043639713/625000000000000 : ℝ)^1065 := by
      have hnat : (100044633487125631021 : ℕ)^256*625000000000000^1065 ≤ 625067043639713^1065*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044633487125631021 100000000000000000000 625067043639713 625000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625067043639713/625000000000000 : ℝ)) (X := (100044633487125631021/100000000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034164357868724301/50000000000000000000 : ℝ) ≤ (5000821065936969/5000000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (50034164357868724301/50000000000000000000 : ℝ)^256 ≤ (5000821065936969/5000000000000000 : ℝ)^1065 := by
      have hnat : (50034164357868724301 : ℕ)^256*5000000000000000^1065 ≤ 5000821065936969^1065*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034164357868724301 50000000000000000000 5000821065936969 5000000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000821065936969/5000000000000000 : ℝ)) (X := (50034164357868724301/50000000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(65432057855667/625000000000000000 : ℝ) ≤ ((18159623077301749447/18165000000000000000 : ℝ)+2*(56943363853/36330000000000 : ℝ)*(1381/12500 : ℝ))^(1065/256 : ℝ) := by
    rw [show (18159623077301749447/18165000000000000000 : ℝ)+2*(56943363853/36330000000000 : ℝ)*(1381/12500 : ℝ)=(5000251632298439/5000000000000000 : ℝ) by norm_num, show 1+2*(65432057855667/625000000000000000 : ℝ)=(312565432057855667/312500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34164357868724301/100000000000000000000 : ℝ)+(65432057855667/625000000000000000 : ℝ) ≤ ((18159623077301749447/18165000000000000000 : ℝ)+(56943363853/36330000000000 : ℝ)*((14681/100000 : ℝ)+(1381/12500 : ℝ)))^(1065/256 : ℝ) := by
    rw [show (18159623077301749447/18165000000000000000 : ℝ)+(56943363853/36330000000000 : ℝ)*((14681/100000 : ℝ)+(1381/12500 : ℝ))=(625067043639713/625000000000000 : ℝ) by norm_num, show 1+(34164357868724301/100000000000000000000 : ℝ)+(65432057855667/625000000000000000 : ℝ)=(100044633487125631021/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34164357868724301/100000000000000000000 : ℝ) ≤ ((18159623077301749447/18165000000000000000 : ℝ)+2*(56943363853/36330000000000 : ℝ)*(14681/100000 : ℝ))^(1065/256 : ℝ) := by
    rw [show (18159623077301749447/18165000000000000000 : ℝ)+2*(56943363853/36330000000000 : ℝ)*(14681/100000 : ℝ)=(5000821065936969/5000000000000000 : ℝ) by norm_num, show 1+2*(34164357868724301/100000000000000000000 : ℝ)=(50034164357868724301/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18159623077301749447/18165000000000000000 : ℝ)*(X 1 0+X 2 0)+(56943363853/36330000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (1381/12500 : ℝ)) (hi := (14681/100000 : ℝ)) (c := (18159623077301749447/18165000000000000000 : ℝ)) (alpha := (56943363853/36330000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18159623077301749447/18165000000000000000 : ℝ)*(X 0 1+X 2 1)+(56943363853/36330000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (1381/12500 : ℝ)) (hi := (14681/100000 : ℝ)) (c := (18159623077301749447/18165000000000000000 : ℝ)) (alpha := (56943363853/36330000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18159623077301749447/18165000000000000000 : ℝ)*(X 0 2+X 1 2)+(56943363853/36330000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (1381/12500 : ℝ)) (hi := (14681/100000 : ℝ)) (c := (18159623077301749447/18165000000000000000 : ℝ)) (alpha := (56943363853/36330000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-207993307/1000000000 : ℝ)*X 0 0+(2707380943/5000000000 : ℝ)*X 0 1+(5243315301/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674824387/5000000000 : ℝ)*X 1 0+(-433463731/2000000000 : ℝ)*X 1 1+(2621657631/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349647571/10000000000 : ℝ)*X 2 0+(524331851/1000000000 : ℝ)*X 2 1+(-1083657981/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2168730007/5000000000 : ℝ)*X 0 0+(2082050559/5000000000 : ℝ)*X 0 1+(903534327/2000000000 : ℝ)*X 0 2+(2168730007/5000000000 : ℝ)*X 1 0+(2082050559/5000000000 : ℝ)*X 1 1+(903534327/2000000000 : ℝ)*X 1 2+(2168730007/5000000000 : ℝ)*X 2 0+(2082050559/5000000000 : ℝ)*X 2 1+(903534327/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2079944559/10000000000 : ℝ)*X 0 0+(5243928129/10000000000 : ℝ)*X 0 1+(5414146753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652851967/5000000000 : ℝ)*X 1 0+(-24956097/125000000 : ℝ)*X 1 1+(5414146963/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326426049/2500000000 : ℝ)*X 2 0+(1353536699/2500000000 : ℝ)*X 2 1+(-1996487633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4337483849/10000000000 : ℝ)*X 0 0+(2258205983/5000000000 : ℝ)*X 0 1+(4165369423/10000000000 : ℝ)*X 0 2+(4337483849/10000000000 : ℝ)*X 1 0+(2258205983/5000000000 : ℝ)*X 1 1+(4165369423/10000000000 : ℝ)*X 1 2+(4337483849/10000000000 : ℝ)*X 2 0+(2258205983/5000000000 : ℝ)*X 2 1+(4165369423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (845176394245009702321749447/302750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (372206469/10000000000000 : ℝ)*(base19) + (250357383/10000000000000 : ℝ)*(base23) + (146009839/100000000000000 : ℝ)*(lower2) + (326713191/25000000000000 : ℝ)*(upper5) + (2165334961436489/50000000000000 : ℝ)*(major0) + (2165334961436489/50000000000000 : ℝ)*(major1) + (4330669922872979/100000000000000 : ℝ)*(major2) + (5832822322842383/100000000000000 : ℝ)*(sp0) + (2916460453772463/50000000000000 : ℝ)*(sp1) + (1458241674223327/25000000000000 : ℝ)*(sp2) + (707085249911693/25000000000000 : ℝ)*(sp3) + (36719406189/25000000000000 : ℝ)*(sp4) + (44570857523/100000000000000 : ℝ)*(sp5) + (14776288281/50000000000000 : ℝ)*(sp7) + (1414185276111667/50000000000000 : ℝ)*(f.failure) + (5832969200467139/100000000000000 : ℝ)*(f.sum) + (175971255371/242200000000000000000000000 : ℝ)*base65 + (300353707140621583/908250000000000000000000000000000 : ℝ)*base67 + (4532397551119007387/1816500000000000000000000000000000 : ℝ)*base70 + (4994979610349121583/908250000000000000000000000000000 : ℝ)*base71 + (1976410181749/1211000000000000000000000000 : ℝ)*base73 + (19532316525334007387/1816500000000000000000000000000000 : ℝ)*base76 + (194985506791876139/302750000000000000000000000000000 : ℝ)*base78 + (100654029809623861/302750000000000000000000000000000 : ℝ)*base79 + (1172004799009/1816500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (24787561/2500000000000000000000 : ℝ)*base89 + (24787561/2500000000000000000000 : ℝ)*base91 + (212439/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49473810517462713449618627/4730468750000000000000000000000 : ℝ) := by norm_num
    linear_combination (185883059/50000000000000 : ℝ)*(base19) + (601121729/50000000000000 : ℝ)*(base23) + (210657261/100000000000000 : ℝ)*(lower1) + (83199783/100000000000000 : ℝ)*(upper3) + (15023853/6250000000000 : ℝ)*(lower4) + (48617279/20000000000000 : ℝ)*(upper5) + (17037964626227/390625000000 : ℝ)*(major0) + (17037964626227/390625000000 : ℝ)*(major1) + (17037964626227/390625000000 : ℝ)*(major2) + (5271057217/50000000000000 : ℝ)*(sp2) + (293739440000221/5000000000000 : ℝ)*(sp4) + (2937394214119151/50000000000000 : ℝ)*(sp5) + (91793391494477/1562500000000 : ℝ)*(sp6) + (1424324370002849/50000000000000 : ℝ)*(sp7) + (1424324370002849/50000000000000 : ℝ)*(f.failure) + (293739440000221/5000000000000 : ℝ)*(f.sum) + (3507651229627/1816500000000000000000000000 : ℝ)*base66 + (17481990343663677/2365234375000000000000000000000 : ℝ)*base68 + (137470616592826583/9460937500000000000000000000000 : ℝ)*base70 + (180680548798454667/9460937500000000000000000000000 : ℝ)*base71 + (1551134533897/908250000000000000000000000 : ℝ)*base73 + (4511999430964651/1182617187500000000000000000000 : ℝ)*base76 + (11171191248214651/1182617187500000000000000000000 : ℝ)*base78 + (16129712339339651/1182617187500000000000000000000 : ℝ)*base80 + (2674320243323/1816500000000000000000000000 : ℝ)*base81 + (22838867/2500000000000000000000 : ℝ)*base89 + (22838867/2500000000000000000000 : ℝ)*base91 + (22838867/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1301_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1381/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (221/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1301_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1301_s8_0 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2079933857/10000000000 : ℝ)*x 0 + (5414743587/10000000000 : ℝ)*x 1 + (13108333/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079933857/10000000000 : ℝ)^4261 ≤ (2531335695751/20000000000000 : ℝ)^3237 := by
    have hnat : (2079933857 : ℕ)^4261*20000000000000^3237 ≤ 2531335695751^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079933857 10000000000 2531335695751 20000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414743587/10000000000 : ℝ)^4261 ≤ (2787259046737/6250000000000 : ℝ)^3237 := by
    have hnat : (5414743587 : ℕ)^4261*6250000000000^3237 ≤ 2787259046737^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414743587 10000000000 2787259046737 6250000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13108333/25000000 : ℝ)^4261 ≤ (4274717676291/10000000000000 : ℝ)^3237 := by
    have hnat : (13108333 : ℕ)^4261*10000000000000^3237 ≤ 4274717676291^3237*25000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13108333 25000000 4274717676291 10000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2079933857/10000000000 : ℝ), (5414743587/10000000000 : ℝ), (13108333/25000000 : ℝ)] ![(2531335695751/20000000000000 : ℝ), (2787259046737/6250000000000 : ℝ), (4274717676291/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2079933857/10000000000 : ℝ)|^4261 ≤ (2531335695751/20000000000000 : ℝ)^3237
        have hw : |(-2079933857/10000000000 : ℝ)|=(2079933857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414743587/10000000000 : ℝ)|^4261 ≤ (2787259046737/6250000000000 : ℝ)^3237
        have hw : |(5414743587/10000000000 : ℝ)|=(5414743587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13108333/25000000 : ℝ)|^4261 ≤ (4274717676291/10000000000000 : ℝ)^3237
        have hw : |(13108333/25000000 : ℝ)|=(13108333/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s8_1 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349643759/10000000000 : ℝ)*x 0 + (-2167301549/10000000000 : ℝ)*x 1 + (1048666649/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349643759/10000000000 : ℝ)^4261 ≤ (21945856307321/50000000000000 : ℝ)^3237 := by
    have hnat : (5349643759 : ℕ)^4261*50000000000000^3237 ≤ 21945856307321^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349643759 10000000000 21945856307321 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2167301549/10000000000 : ℝ)^4261 ≤ (3340277531647/25000000000000 : ℝ)^3237 := by
    have hnat : (2167301549 : ℕ)^4261*25000000000000^3237 ≤ 3340277531647^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167301549 10000000000 3340277531647 25000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048666649/2000000000 : ℝ)^4261 ≤ (42747177245837/100000000000000 : ℝ)^3237 := by
    have hnat : (1048666649 : ℕ)^4261*100000000000000^3237 ≤ 42747177245837^3237*2000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048666649 2000000000 42747177245837 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349643759/10000000000 : ℝ), (-2167301549/10000000000 : ℝ), (1048666649/2000000000 : ℝ)] ![(21945856307321/50000000000000 : ℝ), (3340277531647/25000000000000 : ℝ), (42747177245837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349643759/10000000000 : ℝ)|^4261 ≤ (21945856307321/50000000000000 : ℝ)^3237
        have hw : |(5349643759/10000000000 : ℝ)|=(5349643759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2167301549/10000000000 : ℝ)|^4261 ≤ (3340277531647/25000000000000 : ℝ)^3237
        have hw : |(-2167301549/10000000000 : ℝ)|=(2167301549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048666649/2000000000 : ℝ)|^4261 ≤ (42747177245837/100000000000000 : ℝ)^3237
        have hw : |(1048666649/2000000000 : ℝ)|=(1048666649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s8_2 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349643859/10000000000 : ℝ)*x 0 + (2621666567/5000000000 : ℝ)*x 1 + (-1083650781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349643859/10000000000 : ℝ)^4261 ≤ (5486464211831/12500000000000 : ℝ)^3237 := by
    have hnat : (5349643859 : ℕ)^4261*12500000000000^3237 ≤ 5486464211831^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349643859 10000000000 5486464211831 12500000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621666567/5000000000 : ℝ)^4261 ≤ (21373588027309/50000000000000 : ℝ)^3237 := by
    have hnat : (2621666567 : ℕ)^4261*50000000000000^3237 ≤ 21373588027309^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621666567 5000000000 21373588027309 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083650781/5000000000 : ℝ)^4261 ≤ (3340277558021/25000000000000 : ℝ)^3237 := by
    have hnat : (1083650781 : ℕ)^4261*25000000000000^3237 ≤ 3340277558021^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083650781 5000000000 3340277558021 25000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349643859/10000000000 : ℝ), (2621666567/5000000000 : ℝ), (-1083650781/5000000000 : ℝ)] ![(5486464211831/12500000000000 : ℝ), (21373588027309/50000000000000 : ℝ), (3340277558021/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349643859/10000000000 : ℝ)|^4261 ≤ (5486464211831/12500000000000 : ℝ)^3237
        have hw : |(5349643859/10000000000 : ℝ)|=(5349643859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621666567/5000000000 : ℝ)|^4261 ≤ (21373588027309/50000000000000 : ℝ)^3237
        have hw : |(2621666567/5000000000 : ℝ)|=(2621666567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1083650781/5000000000 : ℝ)|^4261 ≤ (3340277558021/25000000000000 : ℝ)^3237
        have hw : |(-1083650781/5000000000 : ℝ)|=(1083650781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s8_3 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4337459029/10000000000 : ℝ)*x 0 + (166565473/400000000 : ℝ)*x 1 + (4517637809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4337459029/10000000000 : ℝ)^4261 ≤ (33302558192221/100000000000000 : ℝ)^3237 := by
    have hnat : (4337459029 : ℕ)^4261*100000000000000^3237 ≤ 33302558192221^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4337459029 10000000000 33302558192221 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166565473/400000000 : ℝ)^4261 ≤ (3156201011231/10000000000000 : ℝ)^3237 := by
    have hnat : (166565473 : ℕ)^4261*10000000000000^3237 ≤ 3156201011231^3237*400000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166565473 400000000 3156201011231 10000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4517637809/10000000000 : ℝ)^4261 ≤ (35135431676047/100000000000000 : ℝ)^3237 := by
    have hnat : (4517637809 : ℕ)^4261*100000000000000^3237 ≤ 35135431676047^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517637809 10000000000 35135431676047 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4337459029/10000000000 : ℝ), (166565473/400000000 : ℝ), (4517637809/10000000000 : ℝ)] ![(33302558192221/100000000000000 : ℝ), (3156201011231/10000000000000 : ℝ), (35135431676047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4337459029/10000000000 : ℝ)|^4261 ≤ (33302558192221/100000000000000 : ℝ)^3237
        have hw : |(4337459029/10000000000 : ℝ)|=(4337459029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(166565473/400000000 : ℝ)|^4261 ≤ (3156201011231/10000000000000 : ℝ)^3237
        have hw : |(166565473/400000000 : ℝ)|=(166565473/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4517637809/10000000000 : ℝ)|^4261 ≤ (35135431676047/100000000000000 : ℝ)^3237
        have hw : |(4517637809/10000000000 : ℝ)|=(4517637809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s8_4 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2079946499/10000000000 : ℝ)*x 0 + (5243944351/10000000000 : ℝ)*x 1 + (5414129261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079946499/10000000000 : ℝ)^4261 ≤ (6328389871399/50000000000000 : ℝ)^3237 := by
    have hnat : (2079946499 : ℕ)^4261*50000000000000^3237 ≤ 6328389871399^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079946499 10000000000 6328389871399 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243944351/10000000000 : ℝ)^4261 ≤ (4275373557741/10000000000000 : ℝ)^3237 := by
    have hnat : (5243944351 : ℕ)^4261*10000000000000^3237 ≤ 4275373557741^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243944351 10000000000 4275373557741 10000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414129261/10000000000 : ℝ)^4261 ≤ (22294742334569/50000000000000 : ℝ)^3237 := by
    have hnat : (5414129261 : ℕ)^4261*50000000000000^3237 ≤ 22294742334569^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414129261 10000000000 22294742334569 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2079946499/10000000000 : ℝ), (5243944351/10000000000 : ℝ), (5414129261/10000000000 : ℝ)] ![(6328389871399/50000000000000 : ℝ), (4275373557741/10000000000000 : ℝ), (22294742334569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2079946499/10000000000 : ℝ)|^4261 ≤ (6328389871399/50000000000000 : ℝ)^3237
        have hw : |(-2079946499/10000000000 : ℝ)|=(2079946499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243944351/10000000000 : ℝ)|^4261 ≤ (4275373557741/10000000000000 : ℝ)^3237
        have hw : |(5243944351/10000000000 : ℝ)|=(5243944351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414129261/10000000000 : ℝ)|^4261 ≤ (22294742334569/50000000000000 : ℝ)^3237
        have hw : |(5414129261/10000000000 : ℝ)|=(5414129261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s8_5 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4337484909/10000000000 : ℝ)*x 0 + (4516377403/10000000000 : ℝ)*x 1 + (4165403807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4337484909/10000000000 : ℝ)^4261 ≤ (3330281975487/10000000000000 : ℝ)^3237 := by
    have hnat : (4337484909 : ℕ)^4261*10000000000000^3237 ≤ 3330281975487^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4337484909 10000000000 3330281975487 10000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4516377403/10000000000 : ℝ)^4261 ≤ (35122528577499/100000000000000 : ℝ)^3237 := by
    have hnat : (4516377403 : ℕ)^4261*100000000000000^3237 ≤ 35122528577499^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516377403 10000000000 35122528577499 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4165403807/10000000000 : ℝ)^4261 ≤ (6314930329639/20000000000000 : ℝ)^3237 := by
    have hnat : (4165403807 : ℕ)^4261*20000000000000^3237 ≤ 6314930329639^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165403807 10000000000 6314930329639 20000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4337484909/10000000000 : ℝ), (4516377403/10000000000 : ℝ), (4165403807/10000000000 : ℝ)] ![(3330281975487/10000000000000 : ℝ), (35122528577499/100000000000000 : ℝ), (6314930329639/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4337484909/10000000000 : ℝ)|^4261 ≤ (3330281975487/10000000000000 : ℝ)^3237
        have hw : |(4337484909/10000000000 : ℝ)|=(4337484909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4516377403/10000000000 : ℝ)|^4261 ≤ (35122528577499/100000000000000 : ℝ)^3237
        have hw : |(4516377403/10000000000 : ℝ)|=(4516377403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4165403807/10000000000 : ℝ)|^4261 ≤ (6314930329639/20000000000000 : ℝ)^3237
        have hw : |(4165403807/10000000000 : ℝ)|=(4165403807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1301_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (221/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (11051/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14679/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14679/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (221/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14679/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (221/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14679/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (221/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14679/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (221/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14679/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (221/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14679/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (221/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (221/2000 : ℝ) ^ (1065/256 : ℝ) ≤ (1309626984254937/12500000000000000000 : ℝ) := by
    have hpowers : (221/2000 : ℝ)^1065 ≤ (1309626984254937/12500000000000000000 : ℝ)^256 := by
      have hnat : (221 : ℕ)^1065*12500000000000000000^256 ≤ 1309626984254937^256*2000^1065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        221 2000 1309626984254937 12500000000000000000 1065 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (221/2000 : ℝ)) (X := (1309626984254937/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14679/100000 : ℝ) ^ (1065/256 : ℝ) ≤ (34144999722011307/100000000000000000000 : ℝ) := by
    have hpowers : (14679/100000 : ℝ)^1065 ≤ (34144999722011307/100000000000000000000 : ℝ)^256 := by
      have hnat : (14679 : ℕ)^1065*100000000000000000000^256 ≤ 34144999722011307^256*100000^1065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14679 100000 34144999722011307 100000000000000000000 1065 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14679/100000 : ℝ)) (X := (34144999722011307/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251309626984254937/6250000000000000000 : ℝ) ≤ (5000251821843303/5000000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (6251309626984254937/6250000000000000000 : ℝ)^256 ≤ (5000251821843303/5000000000000000 : ℝ)^1065 := by
      have hnat : (6251309626984254937 : ℕ)^256*5000000000000000^1065 ≤ 5000251821843303^1065*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251309626984254937 6250000000000000000 5000251821843303 5000000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000251821843303/5000000000000000 : ℝ)) (X := (6251309626984254937/6250000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044622015596050803/100000000000000000000 : ℝ) ≤ (2000214484516257/2000000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (100044622015596050803/100000000000000000000 : ℝ)^256 ≤ (2000214484516257/2000000000000000 : ℝ)^1065 := by
      have hnat : (100044622015596050803 : ℕ)^256*2000000000000000^1065 ≤ 2000214484516257^1065*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044622015596050803 100000000000000000000 2000214484516257 2000000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000214484516257/2000000000000000 : ℝ)) (X := (100044622015596050803/100000000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034144999722011307/50000000000000000000 : ℝ) ≤ (2500410300368991/2500000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (50034144999722011307/50000000000000000000 : ℝ)^256 ≤ (2500410300368991/2500000000000000 : ℝ)^1065 := by
      have hnat : (50034144999722011307 : ℕ)^256*2500000000000000^1065 ≤ 2500410300368991^1065*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034144999722011307 50000000000000000000 2500410300368991 2500000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500410300368991/2500000000000000 : ℝ)) (X := (50034144999722011307/50000000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1309626984254937/12500000000000000000 : ℝ) ≤ ((18139628854683143637/18145000000000000000 : ℝ)+2*(568778894679/362900000000000 : ℝ)*(221/2000 : ℝ))^(1065/256 : ℝ) := by
    rw [show (18139628854683143637/18145000000000000000 : ℝ)+2*(568778894679/362900000000000 : ℝ)*(221/2000 : ℝ)=(5000251821843303/5000000000000000 : ℝ) by norm_num, show 1+2*(1309626984254937/12500000000000000000 : ℝ)=(6251309626984254937/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34144999722011307/100000000000000000000 : ℝ)+(1309626984254937/12500000000000000000 : ℝ) ≤ ((18139628854683143637/18145000000000000000 : ℝ)+(568778894679/362900000000000 : ℝ)*((14679/100000 : ℝ)+(221/2000 : ℝ)))^(1065/256 : ℝ) := by
    rw [show (18139628854683143637/18145000000000000000 : ℝ)+(568778894679/362900000000000 : ℝ)*((14679/100000 : ℝ)+(221/2000 : ℝ))=(2000214484516257/2000000000000000 : ℝ) by norm_num, show 1+(34144999722011307/100000000000000000000 : ℝ)+(1309626984254937/12500000000000000000 : ℝ)=(100044622015596050803/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34144999722011307/100000000000000000000 : ℝ) ≤ ((18139628854683143637/18145000000000000000 : ℝ)+2*(568778894679/362900000000000 : ℝ)*(14679/100000 : ℝ))^(1065/256 : ℝ) := by
    rw [show (18139628854683143637/18145000000000000000 : ℝ)+2*(568778894679/362900000000000 : ℝ)*(14679/100000 : ℝ)=(2500410300368991/2500000000000000 : ℝ) by norm_num, show 1+2*(34144999722011307/100000000000000000000 : ℝ)=(50034144999722011307/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18139628854683143637/18145000000000000000 : ℝ)*(X 1 0+X 2 0)+(568778894679/362900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (221/2000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (18139628854683143637/18145000000000000000 : ℝ)) (alpha := (568778894679/362900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18139628854683143637/18145000000000000000 : ℝ)*(X 0 1+X 2 1)+(568778894679/362900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (221/2000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (18139628854683143637/18145000000000000000 : ℝ)) (alpha := (568778894679/362900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18139628854683143637/18145000000000000000 : ℝ)*(X 0 2+X 1 2)+(568778894679/362900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (221/2000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (18139628854683143637/18145000000000000000 : ℝ)) (alpha := (568778894679/362900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2079933857/10000000000 : ℝ)*X 0 0+(5414743587/10000000000 : ℝ)*X 0 1+(13108333/25000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349643759/10000000000 : ℝ)*X 1 0+(-2167301549/10000000000 : ℝ)*X 1 1+(1048666649/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349643859/10000000000 : ℝ)*X 2 0+(2621666567/5000000000 : ℝ)*X 2 1+(-1083650781/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4337459029/10000000000 : ℝ)*X 0 0+(166565473/400000000 : ℝ)*X 0 1+(4517637809/10000000000 : ℝ)*X 0 2+(4337459029/10000000000 : ℝ)*X 1 0+(166565473/400000000 : ℝ)*X 1 1+(4517637809/10000000000 : ℝ)*X 1 2+(4337459029/10000000000 : ℝ)*X 2 0+(166565473/400000000 : ℝ)*X 2 1+(4517637809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2079946499/10000000000 : ℝ)*X 0 0+(5243944351/10000000000 : ℝ)*X 0 1+(5414129261/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4337484909/10000000000 : ℝ)*X 0 0+(4516377403/10000000000 : ℝ)*X 0 1+(4165403807/10000000000 : ℝ)*X 0 2+(4337484909/10000000000 : ℝ)*X 1 0+(4516377403/10000000000 : ℝ)*X 1 1+(4165403807/10000000000 : ℝ)*X 1 2+(4337484909/10000000000 : ℝ)*X 2 0+(4516377403/10000000000 : ℝ)*X 2 1+(4165403807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2749544950660335372052519089/907250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (443528121/100000000000000 : ℝ)*(base19) + (207762657/50000000000000 : ℝ)*(base23) + (36660091/50000000000000 : ℝ)*(lower2) + (108485951/100000000000000 : ℝ)*(upper3) + (10469777/100000000000000 : ℝ)*(upper5) + (2165705875515497/50000000000000 : ℝ)*(major0) + (2165705875515497/50000000000000 : ℝ)*(major1) + (866282350206199/20000000000000 : ℝ)*(major2) + (1458490205394017/25000000000000 : ℝ)*(sp0) + (5833967915601959/100000000000000 : ℝ)*(sp1) + (2916983971802383/50000000000000 : ℝ)*(sp2) + (282884952781759/10000000000000 : ℝ)*(sp3) + (7537554011/100000000000000 : ℝ)*(sp4) + (1378523273/25000000000000 : ℝ)*(sp5) + (1414427520955341/50000000000000 : ℝ)*(f.failure) + (36462302244563/625000000000 : ℝ)*(f.sum) + (132575432906361/36290000000000000000000000000 : ℝ)*base65 + (8978300330938817589/907250000000000000000000000000000 : ℝ)*base67 + (2793267212721565763/362900000000000000000000000000000 : ℝ)*base69 + (1828519650327182411/907250000000000000000000000000000 : ℝ)*base72 + (114570499169381/36290000000000000000000000000 : ℝ)*base73 + (1044468993377965763/362900000000000000000000000000000 : ℝ)*base75 + (863971032011231969/47750000000000000000000000000000 : ℝ)*base78 + (1495105116500731969/47750000000000000000000000000000 : ℝ)*base80 + (2577063886367/2268125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3434903/2500000000000000000000 : ℝ)*base89 + (3434903/2500000000000000000000 : ℝ)*base91 + (21565097/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1301_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (221/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1301_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1301_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5519/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1301_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1301_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1301_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5519/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1301_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

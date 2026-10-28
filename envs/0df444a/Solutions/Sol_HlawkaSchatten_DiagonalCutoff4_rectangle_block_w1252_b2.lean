-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1252_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:23:57.502196+00:00
-- url     : https://prove2.me/submissions/e31d6530-eb9e-40d2-aa04-97e523f71eb3

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
theorem support_rectangle_w1252_s6_0 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1057675799/5000000000 : ℝ)*x 0 + (5391190661/10000000000 : ℝ)*x 1 + (2633588519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057675799/5000000000 : ℝ)^8445 ≤ (3216205213811/25000000000000 : ℝ)^6397 := by
    have hnat : (1057675799 : ℕ)^8445*25000000000000^6397 ≤ 3216205213811^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057675799 5000000000 3216205213811 25000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391190661/10000000000 : ℝ)^8445 ≤ (22118390963001/50000000000000 : ℝ)^6397 := by
    have hnat : (5391190661 : ℕ)^8445*50000000000000^6397 ≤ 22118390963001^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391190661 10000000000 22118390963001 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633588519/5000000000 : ℝ)^8445 ≤ (10724599300897/25000000000000 : ℝ)^6397 := by
    have hnat : (2633588519 : ℕ)^8445*25000000000000^6397 ≤ 10724599300897^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633588519 5000000000 10724599300897 25000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1057675799/5000000000 : ℝ), (5391190661/10000000000 : ℝ), (2633588519/5000000000 : ℝ)] ![(3216205213811/25000000000000 : ℝ), (22118390963001/50000000000000 : ℝ), (10724599300897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1057675799/5000000000 : ℝ)|^8445 ≤ (3216205213811/25000000000000 : ℝ)^6397
        have hw : |(-1057675799/5000000000 : ℝ)|=(1057675799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391190661/10000000000 : ℝ)|^8445 ≤ (22118390963001/50000000000000 : ℝ)^6397
        have hw : |(5391190661/10000000000 : ℝ)|=(5391190661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633588519/5000000000 : ℝ)|^8445 ≤ (10724599300897/25000000000000 : ℝ)^6397
        have hw : |(2633588519/5000000000 : ℝ)|=(2633588519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s6_1 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344301027/10000000000 : ℝ)*x 0 + (-2178229843/10000000000 : ℝ)*x 1 + (5267177033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344301027/10000000000 : ℝ)^8445 ≤ (8745913238303/20000000000000 : ℝ)^6397 := by
    have hnat : (5344301027 : ℕ)^8445*20000000000000^6397 ≤ 8745913238303^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344301027 10000000000 8745913238303 20000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2178229843/10000000000 : ℝ)^8445 ≤ (13372036644377/100000000000000 : ℝ)^6397 := by
    have hnat : (2178229843 : ℕ)^8445*100000000000000^6397 ≤ 13372036644377^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178229843 10000000000 13372036644377 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267177033/10000000000 : ℝ)^8445 ≤ (10724599287457/25000000000000 : ℝ)^6397 := by
    have hnat : (5267177033 : ℕ)^8445*25000000000000^6397 ≤ 10724599287457^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267177033 10000000000 10724599287457 25000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344301027/10000000000 : ℝ), (-2178229843/10000000000 : ℝ), (5267177033/10000000000 : ℝ)] ![(8745913238303/20000000000000 : ℝ), (13372036644377/100000000000000 : ℝ), (10724599287457/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344301027/10000000000 : ℝ)|^8445 ≤ (8745913238303/20000000000000 : ℝ)^6397
        have hw : |(5344301027/10000000000 : ℝ)|=(5344301027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2178229843/10000000000 : ℝ)|^8445 ≤ (13372036644377/100000000000000 : ℝ)^6397
        have hw : |(-2178229843/10000000000 : ℝ)|=(2178229843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267177033/10000000000 : ℝ)|^8445 ≤ (10724599287457/25000000000000 : ℝ)^6397
        have hw : |(5267177033/10000000000 : ℝ)|=(5267177033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s6_2 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672150517/5000000000 : ℝ)*x 0 + (658397129/1250000000 : ℝ)*x 1 + (-435645967/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672150517/5000000000 : ℝ)^8445 ≤ (4372956626713/10000000000000 : ℝ)^6397 := by
    have hnat : (2672150517 : ℕ)^8445*10000000000000^6397 ≤ 4372956626713^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672150517 5000000000 4372956626713 10000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658397129/1250000000 : ℝ)^8445 ≤ (42898397139077/100000000000000 : ℝ)^6397 := by
    have hnat : (658397129 : ℕ)^8445*100000000000000^6397 ≤ 42898397139077^6397*1250000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658397129 1250000000 42898397139077 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (435645967/2000000000 : ℝ)^8445 ≤ (6686018289771/50000000000000 : ℝ)^6397 := by
    have hnat : (435645967 : ℕ)^8445*50000000000000^6397 ≤ 6686018289771^6397*2000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435645967 2000000000 6686018289771 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672150517/5000000000 : ℝ), (658397129/1250000000 : ℝ), (-435645967/2000000000 : ℝ)] ![(4372956626713/10000000000000 : ℝ), (42898397139077/100000000000000 : ℝ), (6686018289771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672150517/5000000000 : ℝ)|^8445 ≤ (4372956626713/10000000000000 : ℝ)^6397
        have hw : |(2672150517/5000000000 : ℝ)|=(2672150517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658397129/1250000000 : ℝ)|^8445 ≤ (42898397139077/100000000000000 : ℝ)^6397
        have hw : |(658397129/1250000000 : ℝ)|=(658397129/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-435645967/2000000000 : ℝ)|^8445 ≤ (6686018289771/50000000000000 : ℝ)^6397
        have hw : |(-435645967/2000000000 : ℝ)|=(435645967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s6_3 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349394653/10000000000 : ℝ)*x 0 + (52814221/125000000 : ℝ)*x 1 + (1119298479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349394653/10000000000 : ℝ)^8445 ≤ (1665872583121/5000000000000 : ℝ)^6397 := by
    have hnat : (4349394653 : ℕ)^8445*5000000000000^6397 ≤ 1665872583121^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349394653 10000000000 1665872583121 5000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52814221/125000000 : ℝ)^8445 ≤ (16033332403791/50000000000000 : ℝ)^6397 := by
    have hnat : (52814221 : ℕ)^8445*50000000000000^6397 ≤ 16033332403791^6397*125000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52814221 125000000 16033332403791 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119298479/2500000000 : ℝ)^8445 ≤ (6923176704361/20000000000000 : ℝ)^6397 := by
    have hnat : (1119298479 : ℕ)^8445*20000000000000^6397 ≤ 6923176704361^6397*2500000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119298479 2500000000 6923176704361 20000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349394653/10000000000 : ℝ), (52814221/125000000 : ℝ), (1119298479/2500000000 : ℝ)] ![(1665872583121/5000000000000 : ℝ), (16033332403791/50000000000000 : ℝ), (6923176704361/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349394653/10000000000 : ℝ)|^8445 ≤ (1665872583121/5000000000000 : ℝ)^6397
        have hw : |(4349394653/10000000000 : ℝ)|=(4349394653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52814221/125000000 : ℝ)|^8445 ≤ (16033332403791/50000000000000 : ℝ)^6397
        have hw : |(52814221/125000000 : ℝ)|=(52814221/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119298479/2500000000 : ℝ)|^8445 ≤ (6923176704361/20000000000000 : ℝ)^6397
        have hw : |(1119298479/2500000000 : ℝ)|=(1119298479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s6_4 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2115356563/10000000000 : ℝ)*x 0 + (5267490249/10000000000 : ℝ)*x 1 + (673859511/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115356563/10000000000 : ℝ)^8445 ≤ (6432430358843/50000000000000 : ℝ)^6397 := by
    have hnat : (2115356563 : ℕ)^8445*50000000000000^6397 ≤ 6432430358843^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115356563 10000000000 6432430358843 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267490249/10000000000 : ℝ)^8445 ≤ (8580352971717/20000000000000 : ℝ)^6397 := by
    have hnat : (5267490249 : ℕ)^8445*20000000000000^6397 ≤ 8580352971717^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267490249 10000000000 8580352971717 20000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673859511/1250000000 : ℝ)^8445 ≤ (11058343599319/25000000000000 : ℝ)^6397 := by
    have hnat : (673859511 : ℕ)^8445*25000000000000^6397 ≤ 11058343599319^6397*1250000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673859511 1250000000 11058343599319 25000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2115356563/10000000000 : ℝ), (5267490249/10000000000 : ℝ), (673859511/1250000000 : ℝ)] ![(6432430358843/50000000000000 : ℝ), (8580352971717/20000000000000 : ℝ), (11058343599319/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2115356563/10000000000 : ℝ)|^8445 ≤ (6432430358843/50000000000000 : ℝ)^6397
        have hw : |(-2115356563/10000000000 : ℝ)|=(2115356563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267490249/10000000000 : ℝ)|^8445 ≤ (8580352971717/20000000000000 : ℝ)^6397
        have hw : |(5267490249/10000000000 : ℝ)|=(5267490249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673859511/1250000000 : ℝ)|^8445 ≤ (11058343599319/25000000000000 : ℝ)^6397
        have hw : |(673859511/1250000000 : ℝ)|=(673859511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s6_5 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312637663/10000000000 : ℝ)*x 0 + (-20545309/100000000 : ℝ)*x 1 + (1347718839/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312637663/10000000000 : ℝ)^8445 ≤ (1735514427327/4000000000000 : ℝ)^6397 := by
    have hnat : (5312637663 : ℕ)^8445*4000000000000^6397 ≤ 1735514427327^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312637663 10000000000 1735514427327 4000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20545309/100000000 : ℝ)^8445 ≤ (12378772821653/100000000000000 : ℝ)^6397 := by
    have hnat : (20545309 : ℕ)^8445*100000000000000^6397 ≤ 12378772821653^6397*100000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20545309 100000000 12378772821653 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347718839/2500000000 : ℝ)^8445 ≤ (22116683234077/50000000000000 : ℝ)^6397 := by
    have hnat : (1347718839 : ℕ)^8445*50000000000000^6397 ≤ 22116683234077^6397*2500000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347718839 2500000000 22116683234077 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312637663/10000000000 : ℝ), (-20545309/100000000 : ℝ), (1347718839/2500000000 : ℝ)] ![(1735514427327/4000000000000 : ℝ), (12378772821653/100000000000000 : ℝ), (22116683234077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312637663/10000000000 : ℝ)|^8445 ≤ (1735514427327/4000000000000 : ℝ)^6397
        have hw : |(5312637663/10000000000 : ℝ)|=(5312637663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20545309/100000000 : ℝ)|^8445 ≤ (12378772821653/100000000000000 : ℝ)^6397
        have hw : |(-20545309/100000000 : ℝ)|=(20545309/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347718839/2500000000 : ℝ)|^8445 ≤ (22116683234077/50000000000000 : ℝ)^6397
        have hw : |(1347718839/2500000000 : ℝ)|=(1347718839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s6_6 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312637983/10000000000 : ℝ)*x 0 + (2695437457/5000000000 : ℝ)*x 1 + (-2054531069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312637983/10000000000 : ℝ)^8445 ≤ (5423483016659/12500000000000 : ℝ)^6397 := by
    have hnat : (5312637983 : ℕ)^8445*12500000000000^6397 ≤ 5423483016659^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312637983 10000000000 5423483016659 12500000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695437457/5000000000 : ℝ)^8445 ≤ (44233361680351/100000000000000 : ℝ)^6397 := by
    have hnat : (2695437457 : ℕ)^8445*100000000000000^6397 ≤ 44233361680351^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695437457 5000000000 44233361680351 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2054531069/10000000000 : ℝ)^8445 ≤ (12378774165887/100000000000000 : ℝ)^6397 := by
    have hnat : (2054531069 : ℕ)^8445*100000000000000^6397 ≤ 12378774165887^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054531069 10000000000 12378774165887 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312637983/10000000000 : ℝ), (2695437457/5000000000 : ℝ), (-2054531069/10000000000 : ℝ)] ![(5423483016659/12500000000000 : ℝ), (44233361680351/100000000000000 : ℝ), (12378774165887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312637983/10000000000 : ℝ)|^8445 ≤ (5423483016659/12500000000000 : ℝ)^6397
        have hw : |(5312637983/10000000000 : ℝ)|=(5312637983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695437457/5000000000 : ℝ)|^8445 ≤ (44233361680351/100000000000000 : ℝ)^6397
        have hw : |(2695437457/5000000000 : ℝ)|=(2695437457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2054531069/10000000000 : ℝ)|^8445 ≤ (12378774165887/100000000000000 : ℝ)^6397
        have hw : |(-2054531069/10000000000 : ℝ)|=(2054531069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s6_7 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (434940393/1000000000 : ℝ)*x 0 + (895311307/2000000000 : ℝ)*x 1 + (4225777601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434940393/1000000000 : ℝ)^8445 ≤ (4164693184723/12500000000000 : ℝ)^6397 := by
    have hnat : (434940393 : ℕ)^8445*12500000000000^6397 ≤ 4164693184723^6397*1000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434940393 1000000000 4164693184723 12500000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895311307/2000000000 : ℝ)^8445 ≤ (17304689000763/50000000000000 : ℝ)^6397 := by
    have hnat : (895311307 : ℕ)^8445*50000000000000^6397 ≤ 17304689000763^6397*2000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895311307 2000000000 17304689000763 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4225777601/10000000000 : ℝ)^8445 ≤ (8018269126627/25000000000000 : ℝ)^6397 := by
    have hnat : (4225777601 : ℕ)^8445*25000000000000^6397 ≤ 8018269126627^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225777601 10000000000 8018269126627 25000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434940393/1000000000 : ℝ), (895311307/2000000000 : ℝ), (4225777601/10000000000 : ℝ)] ![(4164693184723/12500000000000 : ℝ), (17304689000763/50000000000000 : ℝ), (8018269126627/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434940393/1000000000 : ℝ)|^8445 ≤ (4164693184723/12500000000000 : ℝ)^6397
        have hw : |(434940393/1000000000 : ℝ)|=(434940393/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895311307/2000000000 : ℝ)|^8445 ≤ (17304689000763/50000000000000 : ℝ)^6397
        have hw : |(895311307/2000000000 : ℝ)|=(895311307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4225777601/10000000000 : ℝ)|^8445 ≤ (8018269126627/25000000000000 : ℝ)^6397
        have hw : |(4225777601/10000000000 : ℝ)|=(4225777601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1252_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151624409/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7067/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11487/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7057/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7067/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11467/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7067/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11467/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7067/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11467/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7067/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11467/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7067/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11467/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7067/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11467/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11467/100000 : ℝ) ^ (2111/512 : ℝ) ≤ (3311368379450721/25000000000000000000 : ℝ) := by
    have hpowers : (11467/100000 : ℝ)^2111 ≤ (3311368379450721/25000000000000000000 : ℝ)^512 := by
      have hnat : (11467 : ℕ)^2111*25000000000000000000^512 ≤ 3311368379450721^512*100000^2111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11467 100000 3311368379450721 25000000000000000000 2111 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11467/100000 : ℝ)) (X := (3311368379450721/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7067/50000 : ℝ) ^ (2111/512 : ℝ) ≤ (31369176824339349/100000000000000000000 : ℝ) := by
    have hpowers : (7067/50000 : ℝ)^2111 ≤ (31369176824339349/100000000000000000000 : ℝ)^512 := by
      have hnat : (7067 : ℕ)^2111*100000000000000000000^512 ≤ 31369176824339349^512*50000^2111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7067 50000 31369176824339349 100000000000000000000 2111 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7067/50000 : ℝ)) (X := (31369176824339349/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503311368379450721/12500000000000000000 : ℝ) ≤ (10000642444542429/10000000000000000 : ℝ) ^ (2111/512 : ℝ) := by
    have hpowers : (12503311368379450721/12500000000000000000 : ℝ)^512 ≤ (10000642444542429/10000000000000000 : ℝ)^2111 := by
      have hnat : (12503311368379450721 : ℕ)^512*10000000000000000^2111 ≤ 10000642444542429^2111*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503311368379450721 12500000000000000000 10000642444542429 10000000000000000 512 2111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000642444542429/10000000000000000 : ℝ)) (X := (12503311368379450721/12500000000000000000 : ℝ)) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044614650342142233/100000000000000000000 : ℝ) ≤ (5000540948419449/5000000000000000 : ℝ) ^ (2111/512 : ℝ) := by
    have hpowers : (100044614650342142233/100000000000000000000 : ℝ)^512 ≤ (5000540948419449/5000000000000000 : ℝ)^2111 := by
      have hnat : (100044614650342142233 : ℕ)^512*5000000000000000^2111 ≤ 5000540948419449^2111*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044614650342142233 100000000000000000000 5000540948419449 5000000000000000 512 2111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000540948419449/5000000000000000 : ℝ)) (X := (100044614650342142233/100000000000000000000 : ℝ)) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031369176824339349/50000000000000000000 : ℝ) ≤ (10001521349135367/10000000000000000 : ℝ) ^ (2111/512 : ℝ) := by
    have hpowers : (50031369176824339349/50000000000000000000 : ℝ)^512 ≤ (10001521349135367/10000000000000000 : ℝ)^2111 := by
      have hnat : (50031369176824339349 : ℕ)^512*10000000000000000^2111 ≤ 10001521349135367^2111*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031369176824339349 50000000000000000000 10001521349135367 10000000000000000 512 2111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001521349135367/10000000000000000 : ℝ)) (X := (50031369176824339349/50000000000000000000 : ℝ)) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3311368379450721/25000000000000000000 : ℝ) ≤ ((8887211666875812699/8890000000000000000 : ℝ)+2*(146484098823/88900000000000 : ℝ)*(11467/100000 : ℝ))^(2111/512 : ℝ) := by
    rw [show (8887211666875812699/8890000000000000000 : ℝ)+2*(146484098823/88900000000000 : ℝ)*(11467/100000 : ℝ)=(10000642444542429/10000000000000000 : ℝ) by norm_num, show 1+2*(3311368379450721/25000000000000000000 : ℝ)=(12503311368379450721/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31369176824339349/100000000000000000000 : ℝ)+(3311368379450721/25000000000000000000 : ℝ) ≤ ((8887211666875812699/8890000000000000000 : ℝ)+(146484098823/88900000000000 : ℝ)*((7067/50000 : ℝ)+(11467/100000 : ℝ)))^(2111/512 : ℝ) := by
    rw [show (8887211666875812699/8890000000000000000 : ℝ)+(146484098823/88900000000000 : ℝ)*((7067/50000 : ℝ)+(11467/100000 : ℝ))=(5000540948419449/5000000000000000 : ℝ) by norm_num, show 1+(31369176824339349/100000000000000000000 : ℝ)+(3311368379450721/25000000000000000000 : ℝ)=(100044614650342142233/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31369176824339349/100000000000000000000 : ℝ) ≤ ((8887211666875812699/8890000000000000000 : ℝ)+2*(146484098823/88900000000000 : ℝ)*(7067/50000 : ℝ))^(2111/512 : ℝ) := by
    rw [show (8887211666875812699/8890000000000000000 : ℝ)+2*(146484098823/88900000000000 : ℝ)*(7067/50000 : ℝ)=(10001521349135367/10000000000000000 : ℝ) by norm_num, show 1+2*(31369176824339349/100000000000000000000 : ℝ)=(50031369176824339349/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8887211666875812699/8890000000000000000 : ℝ)*(X 1 0+X 2 0)+(146484098823/88900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2111/512 : ℝ)) (lo := (11467/100000 : ℝ)) (hi := (7067/50000 : ℝ)) (c := (8887211666875812699/8890000000000000000 : ℝ)) (alpha := (146484098823/88900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8887211666875812699/8890000000000000000 : ℝ)*(X 0 1+X 2 1)+(146484098823/88900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2111/512 : ℝ)) (lo := (11467/100000 : ℝ)) (hi := (7067/50000 : ℝ)) (c := (8887211666875812699/8890000000000000000 : ℝ)) (alpha := (146484098823/88900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8887211666875812699/8890000000000000000 : ℝ)*(X 0 2+X 1 2)+(146484098823/88900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2111/512 : ℝ)) (lo := (11467/100000 : ℝ)) (hi := (7067/50000 : ℝ)) (c := (8887211666875812699/8890000000000000000 : ℝ)) (alpha := (146484098823/88900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1057675799/5000000000 : ℝ)*X 0 0+(5391190661/10000000000 : ℝ)*X 0 1+(2633588519/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344301027/10000000000 : ℝ)*X 1 0+(-2178229843/10000000000 : ℝ)*X 1 1+(5267177033/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672150517/5000000000 : ℝ)*X 2 0+(658397129/1250000000 : ℝ)*X 2 1+(-435645967/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349394653/10000000000 : ℝ)*X 0 0+(52814221/125000000 : ℝ)*X 0 1+(1119298479/2500000000 : ℝ)*X 0 2+(4349394653/10000000000 : ℝ)*X 1 0+(52814221/125000000 : ℝ)*X 1 1+(1119298479/2500000000 : ℝ)*X 1 2+(4349394653/10000000000 : ℝ)*X 2 0+(52814221/125000000 : ℝ)*X 2 1+(1119298479/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2115356563/10000000000 : ℝ)*X 0 0+(5267490249/10000000000 : ℝ)*X 0 1+(673859511/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312637663/10000000000 : ℝ)*X 1 0+(-20545309/100000000 : ℝ)*X 1 1+(1347718839/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312637983/10000000000 : ℝ)*X 2 0+(2695437457/5000000000 : ℝ)*X 2 1+(-2054531069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((434940393/1000000000 : ℝ)*X 0 0+(895311307/2000000000 : ℝ)*X 0 1+(4225777601/10000000000 : ℝ)*X 0 2+(434940393/1000000000 : ℝ)*X 1 0+(895311307/2000000000 : ℝ)*X 1 1+(4225777601/10000000000 : ℝ)*X 1 2+(434940393/1000000000 : ℝ)*X 2 0+(895311307/2000000000 : ℝ)*X 2 1+(4225777601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (73311425170799701334937177/31750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (450177/97656250000 : ℝ)*(base19) + (434835643/100000000000000 : ℝ)*(base23) + (4904389/25000000000000 : ℝ)*(lower2) + (11219443/20000000000000 : ℝ)*(upper3) + (884941/2000000000000 : ℝ)*(upper5) + (3007759260106171/50000000000000 : ℝ)*(major0) + (3007759260106171/50000000000000 : ℝ)*(major1) + (3007759260106171/50000000000000 : ℝ)*(major2) + (8063642839834719/100000000000000 : ℝ)*(sp0) + (403182757772241/5000000000000 : ℝ)*(sp1) + (4031827590795213/50000000000000 : ℝ)*(sp2) + (991843678575739/25000000000000 : ℝ)*(sp3) + (3194147837/25000000000000 : ℝ)*(sp4) + (3316364137/50000000000000 : ℝ)*(sp7) + (396738134703123/10000000000000 : ℝ)*(f.failure) + (2015913904106517/25000000000000 : ℝ)*(f.sum) + (170156395607/138906250000000000000000000 : ℝ)*base66 + (6987578443568865529/444500000000000000000000000000000 : ℝ)*base67 + (4790771550361365529/444500000000000000000000000000000 : ℝ)*base69 + (7742889002477365529/444500000000000000000000000000000 : ℝ)*base71 + (667680792063/138906250000000000000000000 : ℝ)*base73 + (3417288724688365529/444500000000000000000000000000000 : ℝ)*base75 + (956053934569365529/444500000000000000000000000000000 : ℝ)*base77 + (696049558084365529/444500000000000000000000000000000 : ℝ)*base79 + (486379934883/2222500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (4670693/1000000000000000000000 : ℝ)*base90 + (4670693/1000000000000000000000 : ℝ)*base92 + (4670693/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (65647090524437911921505307/31750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (338256357/12500000000000 : ℝ)*(base19) + (3759402807/100000000000000 : ℝ)*(base23) + (306770971/100000000000000 : ℝ)*(upper2) + (249505639/100000000000000 : ℝ)*(upper5) + (3023064722767839/50000000000000 : ℝ)*(major0) + (3023064722767839/50000000000000 : ℝ)*(major1) + (3023064722767839/50000000000000 : ℝ)*(major2) + (1446189503/12500000000000 : ℝ)*(sp0) + (8054910753/12500000000000 : ℝ)*(sp1) + (499063187/800000000000 : ℝ)*(sp2) + (8104677252915201/100000000000000 : ℝ)*(sp4) + (4052310838547173/50000000000000 : ℝ)*(sp5) + (8104622680130043/100000000000000 : ℝ)*(sp6) + (996892499929823/25000000000000 : ℝ)*(sp7) + (996892499929823/25000000000000 : ℝ)*(f.failure) + (4052344411215613/50000000000000 : ℝ)*(f.sum) + (28046078558031/4445000000000000000000000000 : ℝ)*base66 + (1806637681943812539/444500000000000000000000000000000 : ℝ)*base68 + (3887008344219312539/444500000000000000000000000000000 : ℝ)*base70 + (1081532598692312539/444500000000000000000000000000000 : ℝ)*base72 + (1851232439167/2222500000000000000000000000 : ℝ)*base73 + (4029494316295312539/444500000000000000000000000000000 : ℝ)*base76 + (1560144850190812539/444500000000000000000000000000000 : ℝ)*base78 + (9134903551354312539/444500000000000000000000000000000 : ℝ)*base80 + (7734603000503/2222500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (3849607/2500000000000000000000 : ℝ)*base89 + (3849607/2500000000000000000000 : ℝ)*base91 + (3849607/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1252_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151624409/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7067/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11487/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1252_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1252_s7_0 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2115365107/10000000000 : ℝ)*x 0 + (1078201027/2000000000 : ℝ)*x 1 + (2633676931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115365107/10000000000 : ℝ)^8445 ≤ (12864929314877/100000000000000 : ℝ)^6397 := by
    have hnat : (2115365107 : ℕ)^8445*100000000000000^6397 ≤ 12864929314877^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115365107 10000000000 12864929314877 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078201027/2000000000 : ℝ)^8445 ≤ (5529346532129/12500000000000 : ℝ)^6397 := by
    have hnat : (1078201027 : ℕ)^8445*12500000000000^6397 ≤ 5529346532129^6397*2000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078201027 2000000000 5529346532129 12500000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633676931/5000000000 : ℝ)^8445 ≤ (8580059682637/20000000000000 : ℝ)^6397 := by
    have hnat : (2633676931 : ℕ)^8445*20000000000000^6397 ≤ 8580059682637^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633676931 5000000000 8580059682637 20000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2115365107/10000000000 : ℝ), (1078201027/2000000000 : ℝ), (2633676931/5000000000 : ℝ)] ![(12864929314877/100000000000000 : ℝ), (5529346532129/12500000000000 : ℝ), (8580059682637/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2115365107/10000000000 : ℝ)|^8445 ≤ (12864929314877/100000000000000 : ℝ)^6397
        have hw : |(-2115365107/10000000000 : ℝ)|=(2115365107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078201027/2000000000 : ℝ)|^8445 ≤ (5529346532129/12500000000000 : ℝ)^6397
        have hw : |(1078201027/2000000000 : ℝ)|=(1078201027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633676931/5000000000 : ℝ)|^8445 ≤ (8580059682637/20000000000000 : ℝ)^6397
        have hw : |(2633676931/5000000000 : ℝ)|=(2633676931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s7_1 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068850931/2000000000 : ℝ)*x 0 + (-544514293/2500000000 : ℝ)*x 1 + (526735377/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068850931/2000000000 : ℝ)^8445 ≤ (43729065277961/100000000000000 : ℝ)^6397 := by
    have hnat : (1068850931 : ℕ)^8445*100000000000000^6397 ≤ 43729065277961^6397*2000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068850931 2000000000 43729065277961 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544514293/2500000000 : ℝ)^8445 ≤ (6685318639619/50000000000000 : ℝ)^6397 := by
    have hnat : (544514293 : ℕ)^8445*50000000000000^6397 ≤ 6685318639619^6397*2500000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544514293 2500000000 6685318639619 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526735377/1000000000 : ℝ)^8445 ≤ (42900297423997/100000000000000 : ℝ)^6397 := by
    have hnat : (526735377 : ℕ)^8445*100000000000000^6397 ≤ 42900297423997^6397*1000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526735377 1000000000 42900297423997 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068850931/2000000000 : ℝ), (-544514293/2500000000 : ℝ), (526735377/1000000000 : ℝ)] ![(43729065277961/100000000000000 : ℝ), (6685318639619/50000000000000 : ℝ), (42900297423997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068850931/2000000000 : ℝ)|^8445 ≤ (43729065277961/100000000000000 : ℝ)^6397
        have hw : |(1068850931/2000000000 : ℝ)|=(1068850931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-544514293/2500000000 : ℝ)|^8445 ≤ (6685318639619/50000000000000 : ℝ)^6397
        have hw : |(-544514293/2500000000 : ℝ)|=(544514293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526735377/1000000000 : ℝ)|^8445 ≤ (42900297423997/100000000000000 : ℝ)^6397
        have hw : |(526735377/1000000000 : ℝ)|=(526735377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s7_2 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344254789/10000000000 : ℝ)*x 0 + (5267353641/10000000000 : ℝ)*x 1 + (-435611433/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344254789/10000000000 : ℝ)^8445 ≤ (10932266681359/25000000000000 : ℝ)^6397 := by
    have hnat : (5344254789 : ℕ)^8445*25000000000000^6397 ≤ 10932266681359^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344254789 10000000000 10932266681359 25000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267353641/10000000000 : ℝ)^8445 ≤ (42900296036983/100000000000000 : ℝ)^6397 := by
    have hnat : (5267353641 : ℕ)^8445*100000000000000^6397 ≤ 42900296036983^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267353641 10000000000 42900296036983 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (435611433/2000000000 : ℝ)^8445 ≤ (13370637222509/100000000000000 : ℝ)^6397 := by
    have hnat : (435611433 : ℕ)^8445*100000000000000^6397 ≤ 13370637222509^6397*2000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435611433 2000000000 13370637222509 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344254789/10000000000 : ℝ), (5267353641/10000000000 : ℝ), (-435611433/2000000000 : ℝ)] ![(10932266681359/25000000000000 : ℝ), (42900296036983/100000000000000 : ℝ), (13370637222509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344254789/10000000000 : ℝ)|^8445 ≤ (10932266681359/25000000000000 : ℝ)^6397
        have hw : |(5344254789/10000000000 : ℝ)|=(5344254789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267353641/10000000000 : ℝ)|^8445 ≤ (42900296036983/100000000000000 : ℝ)^6397
        have hw : |(5267353641/10000000000 : ℝ)|=(5267353641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-435611433/2000000000 : ℝ)|^8445 ≤ (13370637222509/100000000000000 : ℝ)^6397
        have hw : |(-435611433/2000000000 : ℝ)|=(435611433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s7_3 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349403441/10000000000 : ℝ)*x 0 + (264094067/625000000 : ℝ)*x 1 + (4476824559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349403441/10000000000 : ℝ)^8445 ≤ (832938513317/2500000000000 : ℝ)^6397 := by
    have hnat : (4349403441 : ℕ)^8445*2500000000000^6397 ≤ 832938513317^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349403441 10000000000 832938513317 2500000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264094067/625000000 : ℝ)^8445 ≤ (3207034585973/10000000000000 : ℝ)^6397 := by
    have hnat : (264094067 : ℕ)^8445*10000000000000^6397 ≤ 3207034585973^6397*625000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264094067 625000000 3207034585973 10000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4476824559/10000000000 : ℝ)^8445 ≤ (34612113590663/100000000000000 : ℝ)^6397 := by
    have hnat : (4476824559 : ℕ)^8445*100000000000000^6397 ≤ 34612113590663^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476824559 10000000000 34612113590663 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349403441/10000000000 : ℝ), (264094067/625000000 : ℝ), (4476824559/10000000000 : ℝ)] ![(832938513317/2500000000000 : ℝ), (3207034585973/10000000000000 : ℝ), (34612113590663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349403441/10000000000 : ℝ)|^8445 ≤ (832938513317/2500000000000 : ℝ)^6397
        have hw : |(4349403441/10000000000 : ℝ)|=(4349403441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264094067/625000000 : ℝ)|^8445 ≤ (3207034585973/10000000000000 : ℝ)^6397
        have hw : |(264094067/625000000 : ℝ)|=(264094067/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4476824559/10000000000 : ℝ)|^8445 ≤ (34612113590663/100000000000000 : ℝ)^6397
        have hw : |(4476824559/10000000000 : ℝ)|=(4476824559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s7_4 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2115369311/10000000000 : ℝ)*x 0 + (2633832927/5000000000 : ℝ)*x 1 + (539069233/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115369311/10000000000 : ℝ)^8445 ≤ (12864963067553/100000000000000 : ℝ)^6397 := by
    have hnat : (2115369311 : ℕ)^8445*100000000000000^6397 ≤ 12864963067553^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115369311 10000000000 12864963067553 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633832927/5000000000 : ℝ)^8445 ≤ (21451826498691/50000000000000 : ℝ)^6397 := by
    have hnat : (2633832927 : ℕ)^8445*50000000000000^6397 ≤ 21451826498691^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633832927 5000000000 21451826498691 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539069233/1000000000 : ℝ)^8445 ≤ (11057845979213/25000000000000 : ℝ)^6397 := by
    have hnat : (539069233 : ℕ)^8445*25000000000000^6397 ≤ 11057845979213^6397*1000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539069233 1000000000 11057845979213 25000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2115369311/10000000000 : ℝ), (2633832927/5000000000 : ℝ), (539069233/1000000000 : ℝ)] ![(12864963067553/100000000000000 : ℝ), (21451826498691/50000000000000 : ℝ), (11057845979213/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2115369311/10000000000 : ℝ)|^8445 ≤ (12864963067553/100000000000000 : ℝ)^6397
        have hw : |(-2115369311/10000000000 : ℝ)|=(2115369311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633832927/5000000000 : ℝ)|^8445 ≤ (21451826498691/50000000000000 : ℝ)^6397
        have hw : |(2633832927/5000000000 : ℝ)|=(2633832927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539069233/1000000000 : ℝ)|^8445 ≤ (11057845979213/25000000000000 : ℝ)^6397
        have hw : |(539069233/1000000000 : ℝ)|=(539069233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s7_5 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312683031/10000000000 : ℝ)*x 0 + (-51367963/250000000 : ℝ)*x 1 + (1347673107/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312683031/10000000000 : ℝ)^8445 ≤ (10847087455341/25000000000000 : ℝ)^6397 := by
    have hnat : (5312683031 : ℕ)^8445*25000000000000^6397 ≤ 10847087455341^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312683031 10000000000 10847087455341 25000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51367963/250000000 : ℝ)^8445 ≤ (12380265181991/100000000000000 : ℝ)^6397 := by
    have hnat : (51367963 : ℕ)^8445*100000000000000^6397 ≤ 12380265181991^6397*250000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51367963 250000000 12380265181991 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347673107/2500000000 : ℝ)^8445 ≤ (44231384978389/100000000000000 : ℝ)^6397 := by
    have hnat : (1347673107 : ℕ)^8445*100000000000000^6397 ≤ 44231384978389^6397*2500000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347673107 2500000000 44231384978389 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312683031/10000000000 : ℝ), (-51367963/250000000 : ℝ), (1347673107/2500000000 : ℝ)] ![(10847087455341/25000000000000 : ℝ), (12380265181991/100000000000000 : ℝ), (44231384978389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312683031/10000000000 : ℝ)|^8445 ≤ (10847087455341/25000000000000 : ℝ)^6397
        have hw : |(5312683031/10000000000 : ℝ)|=(5312683031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-51367963/250000000 : ℝ)|^8445 ≤ (12380265181991/100000000000000 : ℝ)^6397
        have hw : |(-51367963/250000000 : ℝ)|=(51367963/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347673107/2500000000 : ℝ)|^8445 ≤ (44231384978389/100000000000000 : ℝ)^6397
        have hw : |(1347673107/2500000000 : ℝ)|=(1347673107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s7_6 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062536597/2000000000 : ℝ)*x 0 + (2695346249/5000000000 : ℝ)*x 1 + (-2054718487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062536597/2000000000 : ℝ)^8445 ≤ (43388349325411/100000000000000 : ℝ)^6397 := by
    have hnat : (1062536597 : ℕ)^8445*100000000000000^6397 ≤ 43388349325411^6397*2000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062536597 2000000000 43388349325411 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695346249/5000000000 : ℝ)^8445 ≤ (44231385736631/100000000000000 : ℝ)^6397 := by
    have hnat : (2695346249 : ℕ)^8445*100000000000000^6397 ≤ 44231385736631^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695346249 5000000000 44231385736631 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2054718487/10000000000 : ℝ)^8445 ≤ (24760529839/200000000000 : ℝ)^6397 := by
    have hnat : (2054718487 : ℕ)^8445*200000000000^6397 ≤ 24760529839^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054718487 10000000000 24760529839 200000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062536597/2000000000 : ℝ), (2695346249/5000000000 : ℝ), (-2054718487/10000000000 : ℝ)] ![(43388349325411/100000000000000 : ℝ), (44231385736631/100000000000000 : ℝ), (24760529839/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062536597/2000000000 : ℝ)|^8445 ≤ (43388349325411/100000000000000 : ℝ)^6397
        have hw : |(1062536597/2000000000 : ℝ)|=(1062536597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695346249/5000000000 : ℝ)|^8445 ≤ (44231385736631/100000000000000 : ℝ)^6397
        have hw : |(2695346249/5000000000 : ℝ)|=(2695346249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2054718487/10000000000 : ℝ)|^8445 ≤ (24760529839/200000000000 : ℝ)^6397
        have hw : |(-2054718487/10000000000 : ℝ)|=(2054718487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s7_7 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349413191/10000000000 : ℝ)*x 0 + (2238095399/5000000000 : ℝ)*x 1 + (2113070397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349413191/10000000000 : ℝ)^8445 ≤ (33317639131409/100000000000000 : ℝ)^6397 := by
    have hnat : (4349413191 : ℕ)^8445*100000000000000^6397 ≤ 33317639131409^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349413191 10000000000 33317639131409 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2238095399/5000000000 : ℝ)^8445 ≤ (4325705648557/12500000000000 : ℝ)^6397 := by
    have hnat : (2238095399 : ℕ)^8445*12500000000000^6397 ≤ 4325705648557^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238095399 5000000000 4325705648557 12500000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113070397/5000000000 : ℝ)^8445 ≤ (6415343132599/20000000000000 : ℝ)^6397 := by
    have hnat : (2113070397 : ℕ)^8445*20000000000000^6397 ≤ 6415343132599^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113070397 5000000000 6415343132599 20000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349413191/10000000000 : ℝ), (2238095399/5000000000 : ℝ), (2113070397/5000000000 : ℝ)] ![(33317639131409/100000000000000 : ℝ), (4325705648557/12500000000000 : ℝ), (6415343132599/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349413191/10000000000 : ℝ)|^8445 ≤ (33317639131409/100000000000000 : ℝ)^6397
        have hw : |(4349413191/10000000000 : ℝ)|=(4349413191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2238095399/5000000000 : ℝ)|^8445 ≤ (4325705648557/12500000000000 : ℝ)^6397
        have hw : |(2238095399/5000000000 : ℝ)|=(2238095399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113070397/5000000000 : ℝ)|^8445 ≤ (6415343132599/20000000000000 : ℝ)^6397
        have hw : |(2113070397/5000000000 : ℝ)|=(2113070397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1252_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151624409/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1149/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1411/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7057/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11487/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7057/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11487/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11487/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11487/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11487/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11487/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11487/100000 : ℝ) ^ (2111/512 : ℝ) ≤ (6670491731697049/50000000000000000000 : ℝ) := by
    have hpowers : (11487/100000 : ℝ)^2111 ≤ (6670491731697049/50000000000000000000 : ℝ)^512 := by
      have hnat : (11487 : ℕ)^2111*50000000000000000000^512 ≤ 6670491731697049^512*100000^2111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11487 100000 6670491731697049 50000000000000000000 2111 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11487/100000 : ℝ)) (X := (6670491731697049/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7057/50000 : ℝ) ^ (2111/512 : ℝ) ≤ (31186565970253537/100000000000000000000 : ℝ) := by
    have hpowers : (7057/50000 : ℝ)^2111 ≤ (31186565970253537/100000000000000000000 : ℝ)^512 := by
      have hnat : (7057 : ℕ)^2111*100000000000000000000^512 ≤ 31186565970253537^512*50000^2111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7057 50000 31186565970253537 100000000000000000000 2111 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7057/50000 : ℝ)) (X := (31186565970253537/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006670491731697049/25000000000000000000 : ℝ) ≤ (5000323538294267/5000000000000000 : ℝ) ^ (2111/512 : ℝ) := by
    have hpowers : (25006670491731697049/25000000000000000000 : ℝ)^512 ≤ (5000323538294267/5000000000000000 : ℝ)^2111 := by
      have hnat : (25006670491731697049 : ℕ)^512*5000000000000000^2111 ≤ 5000323538294267^2111*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006670491731697049 25000000000000000000 5000323538294267 5000000000000000 512 2111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000323538294267/5000000000000000 : ℝ)) (X := (25006670491731697049/25000000000000000000 : ℝ)) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008905509886729527/20000000000000000000 : ℝ) ≤ (3125337432817/3125000000000 : ℝ) ^ (2111/512 : ℝ) := by
    have hpowers : (20008905509886729527/20000000000000000000 : ℝ)^512 ≤ (3125337432817/3125000000000 : ℝ)^2111 := by
      have hnat : (20008905509886729527 : ℕ)^512*3125000000000^2111 ≤ 3125337432817^2111*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008905509886729527 20000000000000000000 3125337432817 3125000000000 512 2111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3125337432817/3125000000000 : ℝ)) (X := (20008905509886729527/20000000000000000000 : ℝ)) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031186565970253537/50000000000000000000 : ℝ) ≤ (5000756246720133/5000000000000000 : ℝ) ^ (2111/512 : ℝ) := by
    have hpowers : (50031186565970253537/50000000000000000000 : ℝ)^512 ≤ (5000756246720133/5000000000000000 : ℝ)^2111 := by
      have hnat : (50031186565970253537 : ℕ)^512*5000000000000000^2111 ≤ 5000756246720133^2111*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031186565970253537 50000000000000000000 5000756246720133 5000000000000000 512 2111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000756246720133/5000000000000000 : ℝ)) (X := (50031186565970253537/50000000000000000000 : ℝ)) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6670491731697049/50000000000000000000 : ℝ) ≤ ((13130879413411116667/13135000000000000000 : ℝ)+2*(216354212933/131350000000000 : ℝ)*(11487/100000 : ℝ))^(2111/512 : ℝ) := by
    rw [show (13130879413411116667/13135000000000000000 : ℝ)+2*(216354212933/131350000000000 : ℝ)*(11487/100000 : ℝ)=(5000323538294267/5000000000000000 : ℝ) by norm_num, show 1+2*(6670491731697049/50000000000000000000 : ℝ)=(25006670491731697049/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31186565970253537/100000000000000000000 : ℝ)+(6670491731697049/50000000000000000000 : ℝ) ≤ ((13130879413411116667/13135000000000000000 : ℝ)+(216354212933/131350000000000 : ℝ)*((7057/50000 : ℝ)+(11487/100000 : ℝ)))^(2111/512 : ℝ) := by
    rw [show (13130879413411116667/13135000000000000000 : ℝ)+(216354212933/131350000000000 : ℝ)*((7057/50000 : ℝ)+(11487/100000 : ℝ))=(3125337432817/3125000000000 : ℝ) by norm_num, show 1+(31186565970253537/100000000000000000000 : ℝ)+(6670491731697049/50000000000000000000 : ℝ)=(20008905509886729527/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31186565970253537/100000000000000000000 : ℝ) ≤ ((13130879413411116667/13135000000000000000 : ℝ)+2*(216354212933/131350000000000 : ℝ)*(7057/50000 : ℝ))^(2111/512 : ℝ) := by
    rw [show (13130879413411116667/13135000000000000000 : ℝ)+2*(216354212933/131350000000000 : ℝ)*(7057/50000 : ℝ)=(5000756246720133/5000000000000000 : ℝ) by norm_num, show 1+2*(31186565970253537/100000000000000000000 : ℝ)=(50031186565970253537/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13130879413411116667/13135000000000000000 : ℝ)*(X 1 0+X 2 0)+(216354212933/131350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2111/512 : ℝ)) (lo := (11487/100000 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (13130879413411116667/13135000000000000000 : ℝ)) (alpha := (216354212933/131350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13130879413411116667/13135000000000000000 : ℝ)*(X 0 1+X 2 1)+(216354212933/131350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2111/512 : ℝ)) (lo := (11487/100000 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (13130879413411116667/13135000000000000000 : ℝ)) (alpha := (216354212933/131350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13130879413411116667/13135000000000000000 : ℝ)*(X 0 2+X 1 2)+(216354212933/131350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2111/512 : ℝ)) (lo := (11487/100000 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (13130879413411116667/13135000000000000000 : ℝ)) (alpha := (216354212933/131350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2115365107/10000000000 : ℝ)*X 0 0+(1078201027/2000000000 : ℝ)*X 0 1+(2633676931/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068850931/2000000000 : ℝ)*X 1 0+(-544514293/2500000000 : ℝ)*X 1 1+(526735377/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344254789/10000000000 : ℝ)*X 2 0+(5267353641/10000000000 : ℝ)*X 2 1+(-435611433/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349403441/10000000000 : ℝ)*X 0 0+(264094067/625000000 : ℝ)*X 0 1+(4476824559/10000000000 : ℝ)*X 0 2+(4349403441/10000000000 : ℝ)*X 1 0+(264094067/625000000 : ℝ)*X 1 1+(4476824559/10000000000 : ℝ)*X 1 2+(4349403441/10000000000 : ℝ)*X 2 0+(264094067/625000000 : ℝ)*X 2 1+(4476824559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2115369311/10000000000 : ℝ)*X 0 0+(2633832927/5000000000 : ℝ)*X 0 1+(539069233/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312683031/10000000000 : ℝ)*X 1 0+(-51367963/250000000 : ℝ)*X 1 1+(1347673107/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062536597/2000000000 : ℝ)*X 2 0+(2695346249/5000000000 : ℝ)*X 2 1+(-2054718487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349413191/10000000000 : ℝ)*X 0 0+(2238095399/5000000000 : ℝ)*X 0 1+(2113070397/5000000000 : ℝ)*X 0 2+(4349413191/10000000000 : ℝ)*X 1 0+(2238095399/5000000000 : ℝ)*X 1 1+(2113070397/5000000000 : ℝ)*X 1 2+(4349413191/10000000000 : ℝ)*X 2 0+(2238095399/5000000000 : ℝ)*X 2 1+(2113070397/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (125988617634962899820619/13135000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1991147541/100000000000000 : ℝ)*(base19) + (1569071377/100000000000000 : ℝ)*(base23) + (456066419/100000000000000 : ℝ)*(upper3) + (333938511/100000000000000 : ℝ)*(upper4) + (28223173/50000000000000 : ℝ)*(upper5) + (6033183160457873/100000000000000 : ℝ)*(major0) + (6033183160457873/100000000000000 : ℝ)*(major1) + (6033183160457873/100000000000000 : ℝ)*(major2) + (4043650499566919/50000000000000 : ℝ)*(sp0) + (8087332401444051/100000000000000 : ℝ)*(sp1) + (1617466564704043/20000000000000 : ℝ)*(sp2) + (3979009038146009/100000000000000 : ℝ)*(sp3) + (16696728877/50000000000000 : ℝ)*(sp4) + (22570450647/100000000000000 : ℝ)*(sp7) + (248689475537291/6250000000000 : ℝ)*(f.failure) + (1010916799073949/12500000000000 : ℝ)*(f.sum) + (10243662033023/3283750000000000000000000000 : ℝ)*base66 + (10572169624092569291/1313500000000000000000000000000000 : ℝ)*base67 + (25783755428605069291/1313500000000000000000000000000000 : ℝ)*base69 + (3178224764045930709/1313500000000000000000000000000000 : ℝ)*base72 + (1320949594493/205234375000000000000000000 : ℝ)*base74 + (11740198420363930709/1313500000000000000000000000000000 : ℝ)*base76 + (6576808431849069291/1313500000000000000000000000000000 : ℝ)*base77 + (10404113772988930709/1313500000000000000000000000000000 : ℝ)*base80 + (19967445828507/3283750000000000000000000000 : ℝ)*base81 + (913981/625000000000000000000 : ℝ)*base90 + (913981/625000000000000000000 : ℝ)*base92 + (913981/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (602014772574225778668285639/65675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (660155669/100000000000000 : ℝ)*(base19) + (28947599/3125000000000 : ℝ)*(base23) + (7936971/5000000000000 : ℝ)*(upper3) + (143091071/100000000000000 : ℝ)*(lower4) + (118786613/100000000000000 : ℝ)*(upper5) + (1212752483514361/20000000000000 : ℝ)*(major0) + (1212752483514361/20000000000000 : ℝ)*(major1) + (1212752483514361/20000000000000 : ℝ)*(major2) + (18259013437/100000000000000 : ℝ)*(sp1) + (14784116497/50000000000000 : ℝ)*(sp2) + (2032081288565939/25000000000000 : ℝ)*(sp4) + (8128306235094649/100000000000000 : ℝ)*(sp5) + (8128294659707593/100000000000000 : ℝ)*(sp6) + (1999599687663681/50000000000000 : ℝ)*(sp7) + (1999599687663681/50000000000000 : ℝ)*(f.failure) + (2032081288565939/25000000000000 : ℝ)*(f.sum) + (357460428331/656750000000000000000000000 : ℝ)*base65 + (359076075872254787/262700000000000000000000000000000 : ℝ)*base67 + (1156818634890654787/262700000000000000000000000000000 : ℝ)*base69 + (801277704076945213/262700000000000000000000000000000 : ℝ)*base72 + (10689615406419/1313500000000000000000000000 : ℝ)*base74 + (9084044960359254787/262700000000000000000000000000000 : ℝ)*base75 + (1814501586357154787/262700000000000000000000000000000 : ℝ)*base77 + (4733036108153454787/262700000000000000000000000000000 : ℝ)*base79 + (3147659077497/2627000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (27610471/5000000000000000000000 : ℝ)*base90 + (27610471/5000000000000000000000 : ℝ)*base92 + (27610471/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1252_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151624409/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1149/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1252_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1252_s8_0 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-528842503/2500000000 : ℝ)*x 0 + (2695485889/5000000000 : ℝ)*x 1 + (1053476761/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528842503/2500000000 : ℝ)^8445 ≤ (6432484347839/50000000000000 : ℝ)^6397 := by
    have hnat : (528842503 : ℕ)^8445*50000000000000^6397 ≤ 6432484347839^6397*2500000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528842503 2500000000 6432484347839 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695485889/5000000000 : ℝ)^8445 ≤ (22117205463563/50000000000000 : ℝ)^6397 := by
    have hnat : (2695485889 : ℕ)^8445*50000000000000^6397 ≤ 22117205463563^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695485889 5000000000 22117205463563 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053476761/2000000000 : ℝ)^8445 ≤ (42900620361997/100000000000000 : ℝ)^6397 := by
    have hnat : (1053476761 : ℕ)^8445*100000000000000^6397 ≤ 42900620361997^6397*2000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053476761 2000000000 42900620361997 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528842503/2500000000 : ℝ), (2695485889/5000000000 : ℝ), (1053476761/2000000000 : ℝ)] ![(6432484347839/50000000000000 : ℝ), (22117205463563/50000000000000 : ℝ), (42900620361997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528842503/2500000000 : ℝ)|^8445 ≤ (6432484347839/50000000000000 : ℝ)^6397
        have hw : |(-528842503/2500000000 : ℝ)|=(528842503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695485889/5000000000 : ℝ)|^8445 ≤ (22117205463563/50000000000000 : ℝ)^6397
        have hw : |(2695485889/5000000000 : ℝ)|=(2695485889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053476761/2000000000 : ℝ)|^8445 ≤ (42900620361997/100000000000000 : ℝ)^6397
        have hw : |(1053476761/2000000000 : ℝ)|=(1053476761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s8_1 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344245549/10000000000 : ℝ)*x 0 + (-2178029499/10000000000 : ℝ)*x 1 + (164605743/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344245549/10000000000 : ℝ)^8445 ≤ (21864483457241/50000000000000 : ℝ)^6397 := by
    have hnat : (5344245549 : ℕ)^8445*50000000000000^6397 ≤ 21864483457241^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344245549 10000000000 21864483457241 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2178029499/10000000000 : ℝ)^8445 ≤ (13370413014241/100000000000000 : ℝ)^6397 := by
    have hnat : (2178029499 : ℕ)^8445*100000000000000^6397 ≤ 13370413014241^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178029499 10000000000 13370413014241 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164605743/312500000 : ℝ)^8445 ≤ (42900620050187/100000000000000 : ℝ)^6397 := by
    have hnat : (164605743 : ℕ)^8445*100000000000000^6397 ≤ 42900620050187^6397*312500000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164605743 312500000 42900620050187 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344245549/10000000000 : ℝ), (-2178029499/10000000000 : ℝ), (164605743/312500000 : ℝ)] ![(21864483457241/50000000000000 : ℝ), (13370413014241/100000000000000 : ℝ), (42900620050187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344245549/10000000000 : ℝ)|^8445 ≤ (21864483457241/50000000000000 : ℝ)^6397
        have hw : |(5344245549/10000000000 : ℝ)|=(5344245549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2178029499/10000000000 : ℝ)|^8445 ≤ (13370413014241/100000000000000 : ℝ)^6397
        have hw : |(-2178029499/10000000000 : ℝ)|=(2178029499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164605743/312500000 : ℝ)|^8445 ≤ (42900620050187/100000000000000 : ℝ)^6397
        have hw : |(164605743/312500000 : ℝ)|=(164605743/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s8_2 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344245577/10000000000 : ℝ)*x 0 + (5267383757/10000000000 : ℝ)*x 1 + (-2178029489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344245577/10000000000 : ℝ)^8445 ≤ (43728967216939/100000000000000 : ℝ)^6397 := by
    have hnat : (5344245577 : ℕ)^8445*100000000000000^6397 ≤ 43728967216939^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344245577 10000000000 43728967216939 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267383757/10000000000 : ℝ)^8445 ≤ (21450309922949/50000000000000 : ℝ)^6397 := by
    have hnat : (5267383757 : ℕ)^8445*50000000000000^6397 ≤ 21450309922949^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267383757 10000000000 21450309922949 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2178029489/10000000000 : ℝ)^8445 ≤ (33426032333/250000000000 : ℝ)^6397 := by
    have hnat : (2178029489 : ℕ)^8445*250000000000^6397 ≤ 33426032333^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178029489 10000000000 33426032333 250000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344245577/10000000000 : ℝ), (5267383757/10000000000 : ℝ), (-2178029489/10000000000 : ℝ)] ![(43728967216939/100000000000000 : ℝ), (21450309922949/50000000000000 : ℝ), (33426032333/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344245577/10000000000 : ℝ)|^8445 ≤ (43728967216939/100000000000000 : ℝ)^6397
        have hw : |(5344245577/10000000000 : ℝ)|=(5344245577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267383757/10000000000 : ℝ)|^8445 ≤ (21450309922949/50000000000000 : ℝ)^6397
        have hw : |(5267383757/10000000000 : ℝ)|=(5267383757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2178029489/10000000000 : ℝ)|^8445 ≤ (33426032333/250000000000 : ℝ)^6397
        have hw : |(-2178029489/10000000000 : ℝ)|=(2178029489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s8_3 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087351349/2500000000 : ℝ)*x 0 + (4225568867/10000000000 : ℝ)*x 1 + (1119189999/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087351349/2500000000 : ℝ)^8445 ≤ (4164695037873/12500000000000 : ℝ)^6397 := by
    have hnat : (1087351349 : ℕ)^8445*12500000000000^6397 ≤ 4164695037873^6397*2500000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087351349 2500000000 4164695037873 12500000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4225568867/10000000000 : ℝ)^8445 ≤ (16035492529309/50000000000000 : ℝ)^6397 := by
    have hnat : (4225568867 : ℕ)^8445*50000000000000^6397 ≤ 16035492529309^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225568867 10000000000 16035492529309 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119189999/2500000000 : ℝ)^8445 ≤ (8652863655771/25000000000000 : ℝ)^6397 := by
    have hnat : (1119189999 : ℕ)^8445*25000000000000^6397 ≤ 8652863655771^6397*2500000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119189999 2500000000 8652863655771 25000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087351349/2500000000 : ℝ), (4225568867/10000000000 : ℝ), (1119189999/2500000000 : ℝ)] ![(4164695037873/12500000000000 : ℝ), (16035492529309/50000000000000 : ℝ), (8652863655771/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087351349/2500000000 : ℝ)|^8445 ≤ (4164695037873/12500000000000 : ℝ)^6397
        have hw : |(1087351349/2500000000 : ℝ)|=(1087351349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4225568867/10000000000 : ℝ)|^8445 ≤ (16035492529309/50000000000000 : ℝ)^6397
        have hw : |(4225568867/10000000000 : ℝ)|=(4225568867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119189999/2500000000 : ℝ)|^8445 ≤ (8652863655771/25000000000000 : ℝ)^6397
        have hw : |(1119189999/2500000000 : ℝ)|=(1119189999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s8_4 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2115374727/10000000000 : ℝ)*x 0 + (1316923747/2500000000 : ℝ)*x 1 + (1347664849/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115374727/10000000000 : ℝ)^8445 ≤ (3216251637763/25000000000000 : ℝ)^6397 := by
    have hnat : (2115374727 : ℕ)^8445*25000000000000^6397 ≤ 3216251637763^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115374727 10000000000 3216251637763 25000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316923747/2500000000 : ℝ)^8445 ≤ (42903966253713/100000000000000 : ℝ)^6397 := by
    have hnat : (1316923747 : ℕ)^8445*100000000000000^6397 ≤ 42903966253713^6397*2500000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316923747 2500000000 42903966253713 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347664849/2500000000 : ℝ)^8445 ≤ (5528878396949/12500000000000 : ℝ)^6397 := by
    have hnat : (1347664849 : ℕ)^8445*12500000000000^6397 ≤ 5528878396949^6397*2500000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347664849 2500000000 5528878396949 12500000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2115374727/10000000000 : ℝ), (1316923747/2500000000 : ℝ), (1347664849/2500000000 : ℝ)] ![(3216251637763/25000000000000 : ℝ), (42903966253713/100000000000000 : ℝ), (5528878396949/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2115374727/10000000000 : ℝ)|^8445 ≤ (3216251637763/25000000000000 : ℝ)^6397
        have hw : |(-2115374727/10000000000 : ℝ)|=(2115374727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316923747/2500000000 : ℝ)|^8445 ≤ (42903966253713/100000000000000 : ℝ)^6397
        have hw : |(1316923747/2500000000 : ℝ)|=(1316923747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347664849/2500000000 : ℝ)|^8445 ≤ (5528878396949/12500000000000 : ℝ)^6397
        have hw : |(1347664849/2500000000 : ℝ)|=(1347664849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s8_5 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656345133/5000000000 : ℝ)*x 0 + (-128422157/625000000 : ℝ)*x 1 + (5390658797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656345133/5000000000 : ℝ)^8445 ≤ (21694213913067/50000000000000 : ℝ)^6397 := by
    have hnat : (2656345133 : ℕ)^8445*50000000000000^6397 ≤ 21694213913067^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656345133 5000000000 21694213913067 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128422157/625000000 : ℝ)^8445 ≤ (6190275736633/50000000000000 : ℝ)^6397 := by
    have hnat : (128422157 : ℕ)^8445*50000000000000^6397 ≤ 6190275736633^6397*625000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128422157 625000000 6190275736633 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390658797/10000000000 : ℝ)^8445 ≤ (44231020687227/100000000000000 : ℝ)^6397 := by
    have hnat : (5390658797 : ℕ)^8445*100000000000000^6397 ≤ 44231020687227^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390658797 10000000000 44231020687227 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656345133/5000000000 : ℝ), (-128422157/625000000 : ℝ), (5390658797/10000000000 : ℝ)] ![(21694213913067/50000000000000 : ℝ), (6190275736633/50000000000000 : ℝ), (44231020687227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656345133/5000000000 : ℝ)|^8445 ≤ (21694213913067/50000000000000 : ℝ)^6397
        have hw : |(2656345133/5000000000 : ℝ)|=(2656345133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128422157/625000000 : ℝ)|^8445 ≤ (6190275736633/50000000000000 : ℝ)^6397
        have hw : |(-128422157/625000000 : ℝ)|=(128422157/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390658797/10000000000 : ℝ)|^8445 ≤ (44231020687227/100000000000000 : ℝ)^6397
        have hw : |(5390658797/10000000000 : ℝ)|=(5390658797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s8_6 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656345021/5000000000 : ℝ)*x 0 + (1347664811/2500000000 : ℝ)*x 1 + (-2054754207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656345021/5000000000 : ℝ)^8445 ≤ (21694212705529/50000000000000 : ℝ)^6397 := by
    have hnat : (2656345021 : ℕ)^8445*50000000000000^6397 ≤ 21694212705529^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656345021 5000000000 21694212705529 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347664811/2500000000 : ℝ)^8445 ≤ (44231025529129/100000000000000 : ℝ)^6397 := by
    have hnat : (1347664811 : ℕ)^8445*100000000000000^6397 ≤ 44231025529129^6397*2500000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347664811 2500000000 44231025529129 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2054754207/10000000000 : ℝ)^8445 ≤ (12380549047197/100000000000000 : ℝ)^6397 := by
    have hnat : (2054754207 : ℕ)^8445*100000000000000^6397 ≤ 12380549047197^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054754207 10000000000 12380549047197 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656345021/5000000000 : ℝ), (1347664811/2500000000 : ℝ), (-2054754207/10000000000 : ℝ)] ![(21694212705529/50000000000000 : ℝ), (44231025529129/100000000000000 : ℝ), (12380549047197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656345021/5000000000 : ℝ)|^8445 ≤ (21694212705529/50000000000000 : ℝ)^6397
        have hw : |(2656345021/5000000000 : ℝ)|=(2656345021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347664811/2500000000 : ℝ)|^8445 ≤ (44231025529129/100000000000000 : ℝ)^6397
        have hw : |(1347664811/2500000000 : ℝ)|=(1347664811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2054754207/10000000000 : ℝ)|^8445 ≤ (12380549047197/100000000000000 : ℝ)^6397
        have hw : |(-2054754207/10000000000 : ℝ)|=(2054754207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s8_7 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349414941/10000000000 : ℝ)*x 0 + (4476126529/10000000000 : ℝ)*x 1 + (4226204491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349414941/10000000000 : ℝ)^8445 ≤ (2082353551789/6250000000000 : ℝ)^6397 := by
    have hnat : (4349414941 : ℕ)^8445*6250000000000^6397 ≤ 2082353551789^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349414941 10000000000 2082353551789 6250000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4476126529/10000000000 : ℝ)^8445 ≤ (34604989251337/100000000000000 : ℝ)^6397 := by
    have hnat : (4476126529 : ℕ)^8445*100000000000000^6397 ≤ 34604989251337^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476126529 10000000000 34604989251337 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4226204491/10000000000 : ℝ)^8445 ≤ (32077353910701/100000000000000 : ℝ)^6397 := by
    have hnat : (4226204491 : ℕ)^8445*100000000000000^6397 ≤ 32077353910701^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226204491 10000000000 32077353910701 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349414941/10000000000 : ℝ), (4476126529/10000000000 : ℝ), (4226204491/10000000000 : ℝ)] ![(2082353551789/6250000000000 : ℝ), (34604989251337/100000000000000 : ℝ), (32077353910701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349414941/10000000000 : ℝ)|^8445 ≤ (2082353551789/6250000000000 : ℝ)^6397
        have hw : |(4349414941/10000000000 : ℝ)|=(4349414941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4476126529/10000000000 : ℝ)|^8445 ≤ (34604989251337/100000000000000 : ℝ)^6397
        have hw : |(4476126529/10000000000 : ℝ)|=(4476126529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4226204491/10000000000 : ℝ)|^8445 ≤ (32077353910701/100000000000000 : ℝ)^6397
        have hw : |(4226204491/10000000000 : ℝ)|=(4226204491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1252_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151624409/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1149/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11491/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14109/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1411/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1149/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1411/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1149/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1411/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1149/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1411/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1149/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1411/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1149/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1411/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1149/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1149/10000 : ℝ) ^ (2111/512 : ℝ) ≤ (6677677411559889/50000000000000000000 : ℝ) := by
    have hpowers : (1149/10000 : ℝ)^2111 ≤ (6677677411559889/50000000000000000000 : ℝ)^512 := by
      have hnat : (1149 : ℕ)^2111*50000000000000000000^512 ≤ 6677677411559889^512*10000^2111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1149 10000 6677677411559889 50000000000000000000 2111 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1149/10000 : ℝ)) (X := (6677677411559889/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1411/10000 : ℝ) ^ (2111/512 : ℝ) ≤ (31150140639208697/100000000000000000000 : ℝ) := by
    have hpowers : (1411/10000 : ℝ)^2111 ≤ (31150140639208697/100000000000000000000 : ℝ)^512 := by
      have hnat : (1411 : ℕ)^2111*100000000000000000000^512 ≤ 31150140639208697^512*10000^2111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1411 10000 31150140639208697 100000000000000000000 2111 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1411/10000 : ℝ)) (X := (31150140639208697/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006677677411559889/25000000000000000000 : ℝ) ≤ (80005182188567/80000000000000 : ℝ) ^ (2111/512 : ℝ) := by
    have hpowers : (25006677677411559889/25000000000000000000 : ℝ)^512 ≤ (80005182188567/80000000000000 : ℝ)^2111 := by
      have hnat : (25006677677411559889 : ℕ)^512*80000000000000^2111 ≤ 80005182188567^2111*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006677677411559889 25000000000000000000 80005182188567 80000000000000 512 2111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80005182188567/80000000000000 : ℝ)) (X := (25006677677411559889/25000000000000000000 : ℝ)) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001780219818493139/4000000000000000000 : ℝ) ≤ (100010792502997/100000000000000 : ℝ) ^ (2111/512 : ℝ) := by
    have hpowers : (4001780219818493139/4000000000000000000 : ℝ)^512 ≤ (100010792502997/100000000000000 : ℝ)^2111 := by
      have hnat : (4001780219818493139 : ℕ)^512*100000000000000^2111 ≤ 100010792502997^2111*4000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001780219818493139 4000000000000000000 100010792502997 100000000000000 512 2111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100010792502997/100000000000000 : ℝ)) (X := (4001780219818493139/4000000000000000000 : ℝ)) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031150140639208697/50000000000000000000 : ℝ) ≤ (400060429081141/400000000000000 : ℝ) ^ (2111/512 : ℝ) := by
    have hpowers : (50031150140639208697/50000000000000000000 : ℝ)^512 ≤ (400060429081141/400000000000000 : ℝ)^2111 := by
      have hnat : (50031150140639208697 : ℕ)^512*400000000000000^2111 ≤ 400060429081141^2111*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031150140639208697 50000000000000000000 400060429081141 400000000000000 512 2111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400060429081141/400000000000000 : ℝ)) (X := (50031150140639208697/50000000000000000000 : ℝ)) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6677677411559889/50000000000000000000 : ℝ) ≤ ((13095890915763647/13100000000000000 : ℝ)+2*(17259069153/10480000000000 : ℝ)*(1149/10000 : ℝ))^(2111/512 : ℝ) := by
    rw [show (13095890915763647/13100000000000000 : ℝ)+2*(17259069153/10480000000000 : ℝ)*(1149/10000 : ℝ)=(80005182188567/80000000000000 : ℝ) by norm_num, show 1+2*(6677677411559889/50000000000000000000 : ℝ)=(25006677677411559889/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31150140639208697/100000000000000000000 : ℝ)+(6677677411559889/50000000000000000000 : ℝ) ≤ ((13095890915763647/13100000000000000 : ℝ)+(17259069153/10480000000000 : ℝ)*((1411/10000 : ℝ)+(1149/10000 : ℝ)))^(2111/512 : ℝ) := by
    rw [show (13095890915763647/13100000000000000 : ℝ)+(17259069153/10480000000000 : ℝ)*((1411/10000 : ℝ)+(1149/10000 : ℝ))=(100010792502997/100000000000000 : ℝ) by norm_num, show 1+(31150140639208697/100000000000000000000 : ℝ)+(6677677411559889/50000000000000000000 : ℝ)=(4001780219818493139/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31150140639208697/100000000000000000000 : ℝ) ≤ ((13095890915763647/13100000000000000 : ℝ)+2*(17259069153/10480000000000 : ℝ)*(1411/10000 : ℝ))^(2111/512 : ℝ) := by
    rw [show (13095890915763647/13100000000000000 : ℝ)+2*(17259069153/10480000000000 : ℝ)*(1411/10000 : ℝ)=(400060429081141/400000000000000 : ℝ) by norm_num, show 1+2*(31150140639208697/100000000000000000000 : ℝ)=(50031150140639208697/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13095890915763647/13100000000000000 : ℝ)*(X 1 0+X 2 0)+(17259069153/10480000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2111/512 : ℝ)) (lo := (1149/10000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (13095890915763647/13100000000000000 : ℝ)) (alpha := (17259069153/10480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13095890915763647/13100000000000000 : ℝ)*(X 0 1+X 2 1)+(17259069153/10480000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2111/512 : ℝ)) (lo := (1149/10000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (13095890915763647/13100000000000000 : ℝ)) (alpha := (17259069153/10480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13095890915763647/13100000000000000 : ℝ)*(X 0 2+X 1 2)+(17259069153/10480000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2111/512 : ℝ)) (lo := (1149/10000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (13095890915763647/13100000000000000 : ℝ)) (alpha := (17259069153/10480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-528842503/2500000000 : ℝ)*X 0 0+(2695485889/5000000000 : ℝ)*X 0 1+(1053476761/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344245549/10000000000 : ℝ)*X 1 0+(-2178029499/10000000000 : ℝ)*X 1 1+(164605743/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344245577/10000000000 : ℝ)*X 2 0+(5267383757/10000000000 : ℝ)*X 2 1+(-2178029489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1087351349/2500000000 : ℝ)*X 0 0+(4225568867/10000000000 : ℝ)*X 0 1+(1119189999/2500000000 : ℝ)*X 0 2+(1087351349/2500000000 : ℝ)*X 1 0+(4225568867/10000000000 : ℝ)*X 1 1+(1119189999/2500000000 : ℝ)*X 1 2+(1087351349/2500000000 : ℝ)*X 2 0+(4225568867/10000000000 : ℝ)*X 2 1+(1119189999/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2115374727/10000000000 : ℝ)*X 0 0+(1316923747/2500000000 : ℝ)*X 0 1+(1347664849/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656345133/5000000000 : ℝ)*X 1 0+(-128422157/625000000 : ℝ)*X 1 1+(5390658797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656345021/5000000000 : ℝ)*X 2 0+(1347664811/2500000000 : ℝ)*X 2 1+(-2054754207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349414941/10000000000 : ℝ)*X 0 0+(4476126529/10000000000 : ℝ)*X 0 1+(4226204491/10000000000 : ℝ)*X 0 2+(4349414941/10000000000 : ℝ)*X 1 0+(4476126529/10000000000 : ℝ)*X 1 1+(4226204491/10000000000 : ℝ)*X 1 2+(4349414941/10000000000 : ℝ)*X 2 0+(4476126529/10000000000 : ℝ)*X 2 1+(4226204491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3237130087236171534483/524000000000000000000000000 : ℝ) := by norm_num
    linear_combination (605305263/50000000000000 : ℝ)*(base19) + (1109016351/100000000000000 : ℝ)*(base23) + (19237633/25000000000000 : ℝ)*(lower2) + (74375439/50000000000000 : ℝ)*(upper3) + (6882441/10000000000000 : ℝ)*(upper5) + (6036267067190987/100000000000000 : ℝ)*(major0) + (6036267067190987/100000000000000 : ℝ)*(major1) + (6036267067190987/100000000000000 : ℝ)*(major2) + (4045717951045711/50000000000000 : ℝ)*(sp0) + (1618293439491839/20000000000000 : ℝ)*(sp1) + (809146729905337/10000000000000 : ℝ)*(sp2) + (1990523778596549/50000000000000 : ℝ)*(sp3) + (325059783/1000000000000 : ℝ)*(sp4) + (17963194841/100000000000000 : ℝ)*(sp7) + (3981065520387939/100000000000000 : ℝ)*(f.failure) + (8091468408069721/100000000000000 : ℝ)*(f.sum) + (1049808549089/524000000000000000000000000 : ℝ)*base66 + (1340406442346661/1310000000000000000000000000000 : ℝ)*base68 + (2124442068526661/1310000000000000000000000000000 : ℝ)*base70 + (20775283053976661/1310000000000000000000000000000 : ℝ)*base72 + (3419749783811/524000000000000000000000000 : ℝ)*base73 + (48669900350373339/1310000000000000000000000000000 : ℝ)*base75 + (2907458366173339/1310000000000000000000000000000 : ℝ)*base77 + (5878397847713339/1310000000000000000000000000000 : ℝ)*base79 + (95205872979/104800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1603051/10000000000000000000000 : ℝ)*base89 + (1603051/10000000000000000000000 : ℝ)*base91 + (1603051/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2339867599627432307241/524000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26768237/3125000000000 : ℝ)*(base19) + (66440799/10000000000000 : ℝ)*(base23) + (83175707/100000000000000 : ℝ)*(lower1) + (49773177/100000000000000 : ℝ)*(lower4) + (35082137/12500000000000 : ℝ)*(upper5) + (6066851699422467/100000000000000 : ℝ)*(major0) + (6066851699422467/100000000000000 : ℝ)*(major1) + (6066851699422467/100000000000000 : ℝ)*(major2) + (14234922487/100000000000000 : ℝ)*(sp0) + (4800602607/50000000000000 : ℝ)*(sp2) + (508278261433499/6250000000000 : ℝ)*(sp4) + (8132465561274887/100000000000000 : ℝ)*(sp5) + (8132456152245267/100000000000000 : ℝ)*(sp6) + (2000618416069957/50000000000000 : ℝ)*(sp7) + (2000618416069957/50000000000000 : ℝ)*(f.failure) + (8132466417858471/100000000000000 : ℝ)*(f.sum) + (107119776763/524000000000000000000000000 : ℝ)*base65 + (12055507604180899/1310000000000000000000000000000 : ℝ)*base67 + (9824598709590899/1310000000000000000000000000000 : ℝ)*base69 + (3356051178260899/1310000000000000000000000000000 : ℝ)*base71 + (2851664358763/524000000000000000000000000 : ℝ)*base73 + (36905069224809101/1310000000000000000000000000000 : ℝ)*base76 + (17612096694239101/1310000000000000000000000000000 : ℝ)*base78 + (14511144454899101/1310000000000000000000000000000 : ℝ)*base80 + (105977538867/104800000000000000000000000 : ℝ)*base81 + (17219587/5000000000000000000000 : ℝ)*base90 + (17219587/5000000000000000000000 : ℝ)*base92 + (17219587/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1252_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151624409/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1149/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11491/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1252_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1252_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151624409/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7067/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11491/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1252_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1252_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1252_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151624409/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7067/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11491/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1252_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

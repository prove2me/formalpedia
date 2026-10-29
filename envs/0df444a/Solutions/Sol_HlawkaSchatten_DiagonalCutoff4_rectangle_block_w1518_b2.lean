-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1518_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:56:34.84275+00:00
-- url     : https://prove2.me/submissions/4631c6f6-0e33-4c84-8bb2-cc96f96f62d9

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
theorem support_rectangle_w1518_s6_0 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-929595691/5000000000 : ℝ)*x 0 + (108649029/200000000 : ℝ)*x 1 + (5217935217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (929595691/5000000000 : ℝ)^4533 ≤ (2844706798363/25000000000000 : ℝ)^3509 := by
    have hnat : (929595691 : ℕ)^4533*25000000000000^3509 ≤ 2844706798363^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929595691 5000000000 2844706798363 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108649029/200000000 : ℝ)^4533 ≤ (9092683325647/20000000000000 : ℝ)^3509 := by
    have hnat : (108649029 : ℕ)^4533*20000000000000^3509 ≤ 9092683325647^3509*200000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108649029 200000000 9092683325647 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217935217/10000000000 : ℝ)^4533 ≤ (43157756168397/100000000000000 : ℝ)^3509 := by
    have hnat : (5217935217 : ℕ)^4533*100000000000000^3509 ≤ 43157756168397^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217935217 10000000000 43157756168397 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-929595691/5000000000 : ℝ), (108649029/200000000 : ℝ), (5217935217/10000000000 : ℝ)] ![(2844706798363/25000000000000 : ℝ), (9092683325647/20000000000000 : ℝ), (43157756168397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-929595691/5000000000 : ℝ)|^4533 ≤ (2844706798363/25000000000000 : ℝ)^3509
        have hw : |(-929595691/5000000000 : ℝ)|=(929595691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108649029/200000000 : ℝ)|^4533 ≤ (9092683325647/20000000000000 : ℝ)^3509
        have hw : |(108649029/200000000 : ℝ)|=(108649029/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217935217/10000000000 : ℝ)|^4533 ≤ (43157756168397/100000000000000 : ℝ)^3509
        have hw : |(5217935217/10000000000 : ℝ)|=(5217935217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s6_1 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351254287/10000000000 : ℝ)*x 0 + (-984521557/5000000000 : ℝ)*x 1 + (5217934767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351254287/10000000000 : ℝ)^4533 ≤ (8917501975253/20000000000000 : ℝ)^3509 := by
    have hnat : (5351254287 : ℕ)^4533*20000000000000^3509 ≤ 8917501975253^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351254287 10000000000 8917501975253 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (984521557/5000000000 : ℝ)^4533 ≤ (12254738752379/100000000000000 : ℝ)^3509 := by
    have hnat : (984521557 : ℕ)^4533*100000000000000^3509 ≤ 12254738752379^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984521557 5000000000 12254738752379 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217934767/10000000000 : ℝ)^4533 ≤ (1078943784007/2500000000000 : ℝ)^3509 := by
    have hnat : (5217934767 : ℕ)^4533*2500000000000^3509 ≤ 1078943784007^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217934767 10000000000 1078943784007 2500000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351254287/10000000000 : ℝ), (-984521557/5000000000 : ℝ), (5217934767/10000000000 : ℝ)] ![(8917501975253/20000000000000 : ℝ), (12254738752379/100000000000000 : ℝ), (1078943784007/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351254287/10000000000 : ℝ)|^4533 ≤ (8917501975253/20000000000000 : ℝ)^3509
        have hw : |(5351254287/10000000000 : ℝ)|=(5351254287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-984521557/5000000000 : ℝ)|^4533 ≤ (12254738752379/100000000000000 : ℝ)^3509
        have hw : |(-984521557/5000000000 : ℝ)|=(984521557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217934767/10000000000 : ℝ)|^4533 ≤ (1078943784007/2500000000000 : ℝ)^3509
        have hw : |(5217934767/10000000000 : ℝ)|=(5217934767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s6_2 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675627597/5000000000 : ℝ)*x 0 + (5217933853/10000000000 : ℝ)*x 1 + (-984521557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675627597/5000000000 : ℝ)^4533 ≤ (8917503927781/20000000000000 : ℝ)^3509 := by
    have hnat : (2675627597 : ℕ)^4533*20000000000000^3509 ≤ 8917503927781^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675627597 5000000000 8917503927781 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217933853/10000000000 : ℝ)^4533 ≤ (2157887079723/5000000000000 : ℝ)^3509 := by
    have hnat : (5217933853 : ℕ)^4533*5000000000000^3509 ≤ 2157887079723^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217933853 10000000000 2157887079723 5000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (984521557/5000000000 : ℝ)^4533 ≤ (12254738752379/100000000000000 : ℝ)^3509 := by
    have hnat : (984521557 : ℕ)^4533*100000000000000^3509 ≤ 12254738752379^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984521557 5000000000 12254738752379 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675627597/5000000000 : ℝ), (5217933853/10000000000 : ℝ), (-984521557/5000000000 : ℝ)] ![(8917503927781/20000000000000 : ℝ), (2157887079723/5000000000000 : ℝ), (12254738752379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675627597/5000000000 : ℝ)|^4533 ≤ (8917503927781/20000000000000 : ℝ)^3509
        have hw : |(2675627597/5000000000 : ℝ)|=(2675627597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217933853/10000000000 : ℝ)|^4533 ≤ (2157887079723/5000000000000 : ℝ)^3509
        have hw : |(5217933853/10000000000 : ℝ)|=(5217933853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-984521557/5000000000 : ℝ)|^4533 ≤ (12254738752379/100000000000000 : ℝ)^3509
        have hw : |(-984521557/5000000000 : ℝ)|=(984521557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s6_3 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4266986199/10000000000 : ℝ)*x 0 + (503580683/1250000000 : ℝ)*x 1 + (4517138459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4266986199/10000000000 : ℝ)^4533 ≤ (6655992623991/20000000000000 : ℝ)^3509 := by
    have hnat : (4266986199 : ℕ)^4533*20000000000000^3509 ≤ 6655992623991^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4266986199 10000000000 6655992623991 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503580683/1250000000 : ℝ)^4533 ≤ (30898411732993/100000000000000 : ℝ)^3509 := by
    have hnat : (503580683 : ℕ)^4533*100000000000000^3509 ≤ 30898411732993^3509*1250000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503580683 1250000000 30898411732993 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4517138459/10000000000 : ℝ)^4533 ≤ (8955406285289/25000000000000 : ℝ)^3509 := by
    have hnat : (4517138459 : ℕ)^4533*25000000000000^3509 ≤ 8955406285289^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517138459 10000000000 8955406285289 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4266986199/10000000000 : ℝ), (503580683/1250000000 : ℝ), (4517138459/10000000000 : ℝ)] ![(6655992623991/20000000000000 : ℝ), (30898411732993/100000000000000 : ℝ), (8955406285289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4266986199/10000000000 : ℝ)|^4533 ≤ (6655992623991/20000000000000 : ℝ)^3509
        have hw : |(4266986199/10000000000 : ℝ)|=(4266986199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(503580683/1250000000 : ℝ)|^4533 ≤ (30898411732993/100000000000000 : ℝ)^3509
        have hw : |(503580683/1250000000 : ℝ)|=(503580683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4517138459/10000000000 : ℝ)|^4533 ≤ (8955406285289/25000000000000 : ℝ)^3509
        have hw : |(4517138459/10000000000 : ℝ)|=(4517138459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s6_4 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-92961017/500000000 : ℝ)*x 0 + (5219040771/10000000000 : ℝ)*x 1 + (5431337573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (92961017/500000000 : ℝ)^4533 ≤ (11379056145907/100000000000000 : ℝ)^3509 := by
    have hnat : (92961017 : ℕ)^4533*100000000000000^3509 ≤ 11379056145907^3509*500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92961017 500000000 11379056145907 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219040771/10000000000 : ℝ)^4533 ≤ (8633913810323/20000000000000 : ℝ)^3509 := by
    have hnat : (5219040771 : ℕ)^4533*20000000000000^3509 ≤ 8633913810323^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219040771 10000000000 8633913810323 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431337573/10000000000 : ℝ)^4533 ≤ (45451374789411/100000000000000 : ℝ)^3509 := by
    have hnat : (5431337573 : ℕ)^4533*100000000000000^3509 ≤ 45451374789411^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431337573 10000000000 45451374789411 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-92961017/500000000 : ℝ), (5219040771/10000000000 : ℝ), (5431337573/10000000000 : ℝ)] ![(11379056145907/100000000000000 : ℝ), (8633913810323/20000000000000 : ℝ), (45451374789411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-92961017/500000000 : ℝ)|^4533 ≤ (11379056145907/100000000000000 : ℝ)^3509
        have hw : |(-92961017/500000000 : ℝ)|=(92961017/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219040771/10000000000 : ℝ)|^4533 ≤ (8633913810323/20000000000000 : ℝ)^3509
        have hw : |(5219040771/10000000000 : ℝ)|=(5219040771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431337573/10000000000 : ℝ)|^4533 ≤ (45451374789411/100000000000000 : ℝ)^3509
        have hw : |(5431337573/10000000000 : ℝ)|=(5431337573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s6_5 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2133526591/5000000000 : ℝ)*x 0 + (4514619301/10000000000 : ℝ)*x 1 + (4031181617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133526591/5000000000 : ℝ)^4533 ≤ (16640319002293/50000000000000 : ℝ)^3509 := by
    have hnat : (2133526591 : ℕ)^4533*50000000000000^3509 ≤ 16640319002293^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133526591 5000000000 16640319002293 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514619301/10000000000 : ℝ)^4533 ≤ (35795820115559/100000000000000 : ℝ)^3509 := by
    have hnat : (4514619301 : ℕ)^4533*100000000000000^3509 ≤ 35795820115559^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514619301 10000000000 35795820115559 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4031181617/10000000000 : ℝ)^4533 ≤ (15461770933129/50000000000000 : ℝ)^3509 := by
    have hnat : (4031181617 : ℕ)^4533*50000000000000^3509 ≤ 15461770933129^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031181617 10000000000 15461770933129 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133526591/5000000000 : ℝ), (4514619301/10000000000 : ℝ), (4031181617/10000000000 : ℝ)] ![(16640319002293/50000000000000 : ℝ), (35795820115559/100000000000000 : ℝ), (15461770933129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133526591/5000000000 : ℝ)|^4533 ≤ (16640319002293/50000000000000 : ℝ)^3509
        have hw : |(2133526591/5000000000 : ℝ)|=(2133526591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514619301/10000000000 : ℝ)|^4533 ≤ (35795820115559/100000000000000 : ℝ)^3509
        have hw : |(4514619301/10000000000 : ℝ)|=(4514619301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4031181617/10000000000 : ℝ)|^4533 ≤ (15461770933129/50000000000000 : ℝ)^3509
        have hw : |(4031181617/10000000000 : ℝ)|=(4031181617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1518_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5469/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10939/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5469/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5469/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5469/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5469/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5469/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5469/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5469/50000 : ℝ) ^ (4531/1024 : ℝ) ≤ (5590980778552717/100000000000000000000 : ℝ) := by
    have hpowers : (5469/50000 : ℝ)^4531 ≤ (5590980778552717/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5469 : ℕ)^4531*100000000000000000000^1024 ≤ 5590980778552717^1024*50000^4531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5469 50000 5590980778552717 100000000000000000000 4531 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5469/50000 : ℝ)) (X := (5590980778552717/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4531/1024 : ℝ) ≤ (13008796329804297/50000000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4531 ≤ (13008796329804297/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4531*50000000000000000000^1024 ≤ 13008796329804297^1024*100000^4531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 13008796329804297 50000000000000000000 4531 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (13008796329804297/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005590980778552717/50000000000000000000 : ℝ) ≤ (1000025269991531/1000000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (50005590980778552717/50000000000000000000 : ℝ)^1024 ≤ (1000025269991531/1000000000000000 : ℝ)^4531 := by
      have hnat : (50005590980778552717 : ℕ)^1024*1000000000000000^4531 ≤ 1000025269991531^4531*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005590980778552717 50000000000000000000 1000025269991531 1000000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000025269991531/1000000000000000 : ℝ)) (X := (50005590980778552717/50000000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100031608573438161311/100000000000000000000 : ℝ) ≤ (10000714262207301/10000000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (100031608573438161311/100000000000000000000 : ℝ)^1024 ≤ (10000714262207301/10000000000000000 : ℝ)^4531 := by
      have hnat : (100031608573438161311 : ℕ)^1024*10000000000000000^4531 ≤ 10000714262207301^4531*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100031608573438161311 100000000000000000000 10000714262207301 10000000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000714262207301/10000000000000000 : ℝ)) (X := (100031608573438161311/100000000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013008796329804297/25000000000000000000 : ℝ) ≤ (2500293956124823/2500000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (25013008796329804297/25000000000000000000 : ℝ)^1024 ≤ (2500293956124823/2500000000000000 : ℝ)^4531 := by
      have hnat : (25013008796329804297 : ℕ)^1024*2500000000000000^4531 ≤ 2500293956124823^4531*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013008796329804297 25000000000000000000 2500293956124823 2500000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500293956124823/2500000000000000 : ℝ)) (X := (25013008796329804297/25000000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5590980778552717/100000000000000000000 : ℝ) ≤ ((7573508564069248139/7575000000000000000 : ℝ)+2*(461562291991/454500000000000 : ℝ)*(5469/50000 : ℝ))^(4531/1024 : ℝ) := by
    rw [show (7573508564069248139/7575000000000000000 : ℝ)+2*(461562291991/454500000000000 : ℝ)*(5469/50000 : ℝ)=(1000025269991531/1000000000000000 : ℝ) by norm_num, show 1+2*(5590980778552717/100000000000000000000 : ℝ)=(50005590980778552717/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13008796329804297/50000000000000000000 : ℝ)+(5590980778552717/100000000000000000000 : ℝ) ≤ ((7573508564069248139/7575000000000000000 : ℝ)+(461562291991/454500000000000 : ℝ)*((15483/100000 : ℝ)+(5469/50000 : ℝ)))^(4531/1024 : ℝ) := by
    rw [show (7573508564069248139/7575000000000000000 : ℝ)+(461562291991/454500000000000 : ℝ)*((15483/100000 : ℝ)+(5469/50000 : ℝ))=(10000714262207301/10000000000000000 : ℝ) by norm_num, show 1+(13008796329804297/50000000000000000000 : ℝ)+(5590980778552717/100000000000000000000 : ℝ)=(100031608573438161311/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13008796329804297/50000000000000000000 : ℝ) ≤ ((7573508564069248139/7575000000000000000 : ℝ)+2*(461562291991/454500000000000 : ℝ)*(15483/100000 : ℝ))^(4531/1024 : ℝ) := by
    rw [show (7573508564069248139/7575000000000000000 : ℝ)+2*(461562291991/454500000000000 : ℝ)*(15483/100000 : ℝ)=(2500293956124823/2500000000000000 : ℝ) by norm_num, show 1+2*(13008796329804297/50000000000000000000 : ℝ)=(25013008796329804297/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7573508564069248139/7575000000000000000 : ℝ)*(X 1 0+X 2 0)+(461562291991/454500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (5469/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (7573508564069248139/7575000000000000000 : ℝ)) (alpha := (461562291991/454500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7573508564069248139/7575000000000000000 : ℝ)*(X 0 1+X 2 1)+(461562291991/454500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (5469/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (7573508564069248139/7575000000000000000 : ℝ)) (alpha := (461562291991/454500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7573508564069248139/7575000000000000000 : ℝ)*(X 0 2+X 1 2)+(461562291991/454500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (5469/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (7573508564069248139/7575000000000000000 : ℝ)) (alpha := (461562291991/454500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-929595691/5000000000 : ℝ)*X 0 0+(108649029/200000000 : ℝ)*X 0 1+(5217935217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351254287/10000000000 : ℝ)*X 1 0+(-984521557/5000000000 : ℝ)*X 1 1+(5217934767/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675627597/5000000000 : ℝ)*X 2 0+(5217933853/10000000000 : ℝ)*X 2 1+(-984521557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4266986199/10000000000 : ℝ)*X 0 0+(503580683/1250000000 : ℝ)*X 0 1+(4517138459/10000000000 : ℝ)*X 0 2+(4266986199/10000000000 : ℝ)*X 1 0+(503580683/1250000000 : ℝ)*X 1 1+(4517138459/10000000000 : ℝ)*X 1 2+(4266986199/10000000000 : ℝ)*X 2 0+(503580683/1250000000 : ℝ)*X 2 1+(4517138459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-92961017/500000000 : ℝ)*X 0 0+(5219040771/10000000000 : ℝ)*X 0 1+(5431337573/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2133526591/5000000000 : ℝ)*X 0 0+(4514619301/10000000000 : ℝ)*X 0 1+(4031181617/10000000000 : ℝ)*X 0 2+(2133526591/5000000000 : ℝ)*X 1 0+(4514619301/10000000000 : ℝ)*X 1 1+(4031181617/10000000000 : ℝ)*X 1 2+(2133526591/5000000000 : ℝ)*X 2 0+(4514619301/10000000000 : ℝ)*X 2 1+(4031181617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s6_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87749725357211946150670219/23671875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1387677521/100000000000000 : ℝ)*(base19) + (435359161/20000000000000 : ℝ)*(base23) + (268681/50000000000000 : ℝ)*(lower2) + (382621/3125000000000 : ℝ)*(upper3) + (2164347/1562500000000 : ℝ)*(upper5) + (104825306235883/3125000000000 : ℝ)*(major0) + (104825306235883/3125000000000 : ℝ)*(major1) + (104825306235883/3125000000000 : ℝ)*(major2) + (4661664196689927/100000000000000 : ℝ)*(sp0) + (46616835012277/1000000000000 : ℝ)*(sp1) + (582710339013677/12500000000000 : ℝ)*(sp2) + (2047123066819913/100000000000000 : ℝ)*(sp3) + (10346107647/50000000000000 : ℝ)*(sp4) + (2879951851/25000000000000 : ℝ)*(sp5) + (2047134586627317/100000000000000 : ℝ)*(f.failure) + (4661684888905221/100000000000000 : ℝ)*(f.sum) + (79963209638471/22725000000000000000000000000 : ℝ)*base65 + (222472967708097289/71015625000000000000000000000000 : ℝ)*base68 + (421681225771277711/71015625000000000000000000000000 : ℝ)*base69 + (512768557992347/138702392578125000000000000000 : ℝ)*base72 + (6689031016351/5681250000000000000000000000 : ℝ)*base74 + (64319560241588333/8876953125000000000000000000000 : ℝ)*base76 + (59920401494036041/17753906250000000000000000000000 : ℝ)*base78 + (503635475349972289/71015625000000000000000000000000 : ℝ)*base80 + (60669371715221/22725000000000000000000000000 : ℝ)*base81 + (25773947/5000000000000000000000 : ℝ)*base89 + (25773947/5000000000000000000000 : ℝ)*base91 + (25773947/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1518_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5469/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10939/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1518_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1518_box_0 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1646626853/10000000000 : ℝ)*x 0 + (1080437071/2000000000 : ℝ)*x 1 + (84409147/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1646626853/10000000000 : ℝ)^4533 ≤ (9727051040759/100000000000000 : ℝ)^3509 := by
    have hnat : (1646626853 : ℕ)^4533*100000000000000^3509 ≤ 9727051040759^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1646626853 10000000000 9727051040759 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080437071/2000000000 : ℝ)^4533 ≤ (22568237092829/50000000000000 : ℝ)^3509 := by
    have hnat : (1080437071 : ℕ)^4533*50000000000000^3509 ≤ 22568237092829^3509*2000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080437071 2000000000 22568237092829 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84409147/156250000 : ℝ)^4533 ≤ (45136474757711/100000000000000 : ℝ)^3509 := by
    have hnat : (84409147 : ℕ)^4533*100000000000000^3509 ≤ 45136474757711^3509*156250000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84409147 156250000 45136474757711 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1646626853/10000000000 : ℝ), (1080437071/2000000000 : ℝ), (84409147/156250000 : ℝ)] ![(9727051040759/100000000000000 : ℝ), (22568237092829/50000000000000 : ℝ), (45136474757711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1646626853/10000000000 : ℝ)|^4533 ≤ (9727051040759/100000000000000 : ℝ)^3509
        have hw : |(-1646626853/10000000000 : ℝ)|=(1646626853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080437071/2000000000 : ℝ)|^4533 ≤ (22568237092829/50000000000000 : ℝ)^3509
        have hw : |(1080437071/2000000000 : ℝ)|=(1080437071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84409147/156250000 : ℝ)|^4533 ≤ (45136474757711/100000000000000 : ℝ)^3509
        have hw : |(84409147/156250000 : ℝ)|=(84409147/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_box_1 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270850217/10000000000 : ℝ)*x 0 + (-1828855179/10000000000 : ℝ)*x 1 + (2701092767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270850217/10000000000 : ℝ)^4533 ≤ (43723971906239/100000000000000 : ℝ)^3509 := by
    have hnat : (5270850217 : ℕ)^4533*100000000000000^3509 ≤ 43723971906239^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270850217 10000000000 43723971906239 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1828855179/10000000000 : ℝ)^4533 ≤ (11139551957127/100000000000000 : ℝ)^3509 := by
    have hnat : (1828855179 : ℕ)^4533*100000000000000^3509 ≤ 11139551957127^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828855179 10000000000 11139551957127 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701092767/5000000000 : ℝ)^4533 ≤ (22568238058843/50000000000000 : ℝ)^3509 := by
    have hnat : (2701092767 : ℕ)^4533*50000000000000^3509 ≤ 22568238058843^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701092767 5000000000 22568238058843 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270850217/10000000000 : ℝ), (-1828855179/10000000000 : ℝ), (2701092767/5000000000 : ℝ)] ![(43723971906239/100000000000000 : ℝ), (11139551957127/100000000000000 : ℝ), (22568238058843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270850217/10000000000 : ℝ)|^4533 ≤ (43723971906239/100000000000000 : ℝ)^3509
        have hw : |(5270850217/10000000000 : ℝ)|=(5270850217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1828855179/10000000000 : ℝ)|^4533 ≤ (11139551957127/100000000000000 : ℝ)^3509
        have hw : |(-1828855179/10000000000 : ℝ)|=(1828855179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701092767/5000000000 : ℝ)|^4533 ≤ (22568238058843/50000000000000 : ℝ)^3509
        have hw : |(2701092767/5000000000 : ℝ)|=(2701092767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_box_2 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270850213/10000000000 : ℝ)*x 0 + (5402185429/10000000000 : ℝ)*x 1 + (-1828855329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270850213/10000000000 : ℝ)^4533 ≤ (21861985931687/50000000000000 : ℝ)^3509 := by
    have hnat : (5270850213 : ℕ)^4533*50000000000000^3509 ≤ 21861985931687^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270850213 10000000000 21861985931687 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402185429/10000000000 : ℝ)^4533 ≤ (22568237492187/50000000000000 : ℝ)^3509 := by
    have hnat : (5402185429 : ℕ)^4533*50000000000000^3509 ≤ 22568237492187^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402185429 10000000000 22568237492187 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1828855329/10000000000 : ℝ)^4533 ≤ (11139553137399/100000000000000 : ℝ)^3509 := by
    have hnat : (1828855329 : ℕ)^4533*100000000000000^3509 ≤ 11139553137399^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828855329 10000000000 11139553137399 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270850213/10000000000 : ℝ), (5402185429/10000000000 : ℝ), (-1828855329/10000000000 : ℝ)] ![(21861985931687/50000000000000 : ℝ), (22568237492187/50000000000000 : ℝ), (11139553137399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270850213/10000000000 : ℝ)|^4533 ≤ (21861985931687/50000000000000 : ℝ)^3509
        have hw : |(5270850213/10000000000 : ℝ)|=(5270850213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402185429/10000000000 : ℝ)|^4533 ≤ (22568237492187/50000000000000 : ℝ)^3509
        have hw : |(5402185429/10000000000 : ℝ)|=(5402185429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1828855329/10000000000 : ℝ)|^4533 ≤ (11139553137399/100000000000000 : ℝ)^3509
        have hw : |(-1828855329/10000000000 : ℝ)|=(1828855329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_box_3 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2234891133/5000000000 : ℝ)*x 0 + (521566461/1250000000 : ℝ)*x 1 + (2086265797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2234891133/5000000000 : ℝ)^4533 ≤ (35337235863007/100000000000000 : ℝ)^3509 := by
    have hnat : (2234891133 : ℕ)^4533*100000000000000^3509 ≤ 35337235863007^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234891133 5000000000 35337235863007 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521566461/1250000000 : ℝ)^4533 ≤ (32331382528951/100000000000000 : ℝ)^3509 := by
    have hnat : (521566461 : ℕ)^4533*100000000000000^3509 ≤ 32331382528951^3509*1250000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521566461 1250000000 32331382528951 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086265797/5000000000 : ℝ)^4533 ≤ (16165690794013/50000000000000 : ℝ)^3509 := by
    have hnat : (2086265797 : ℕ)^4533*50000000000000^3509 ≤ 16165690794013^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086265797 5000000000 16165690794013 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2234891133/5000000000 : ℝ), (521566461/1250000000 : ℝ), (2086265797/5000000000 : ℝ)] ![(35337235863007/100000000000000 : ℝ), (32331382528951/100000000000000 : ℝ), (16165690794013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2234891133/5000000000 : ℝ)|^4533 ≤ (35337235863007/100000000000000 : ℝ)^3509
        have hw : |(2234891133/5000000000 : ℝ)|=(2234891133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521566461/1250000000 : ℝ)|^4533 ≤ (32331382528951/100000000000000 : ℝ)^3509
        have hw : |(521566461/1250000000 : ℝ)|=(521566461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086265797/5000000000 : ℝ)|^4533 ≤ (16165690794013/50000000000000 : ℝ)^3509
        have hw : |(2086265797/5000000000 : ℝ)|=(2086265797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_box_4 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2077186141/10000000000 : ℝ)*x 0 + (1310953771/2500000000 : ℝ)*x 1 + (2621906243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2077186141/10000000000 : ℝ)^4533 ≤ (13131078214547/100000000000000 : ℝ)^3509 := by
    have hnat : (2077186141 : ℕ)^4533*100000000000000^3509 ≤ 13131078214547^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077186141 10000000000 13131078214547 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310953771/2500000000 : ℝ)^4533 ≤ (8686894956919/20000000000000 : ℝ)^3509 := by
    have hnat : (1310953771 : ℕ)^4533*20000000000000^3509 ≤ 8686894956919^3509*2500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310953771 2500000000 8686894956919 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621906243/5000000000 : ℝ)^4533 ≤ (43434446985627/100000000000000 : ℝ)^3509 := by
    have hnat : (2621906243 : ℕ)^4533*100000000000000^3509 ≤ 43434446985627^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621906243 5000000000 43434446985627 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2077186141/10000000000 : ℝ), (1310953771/2500000000 : ℝ), (2621906243/5000000000 : ℝ)] ![(13131078214547/100000000000000 : ℝ), (8686894956919/20000000000000 : ℝ), (43434446985627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2077186141/10000000000 : ℝ)|^4533 ≤ (13131078214547/100000000000000 : ℝ)^3509
        have hw : |(-2077186141/10000000000 : ℝ)|=(2077186141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310953771/2500000000 : ℝ)|^4533 ≤ (8686894956919/20000000000000 : ℝ)^3509
        have hw : |(1310953771/2500000000 : ℝ)|=(1310953771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621906243/5000000000 : ℝ)|^4533 ≤ (43434446985627/100000000000000 : ℝ)^3509
        have hw : |(2621906243/5000000000 : ℝ)|=(2621906243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_box_5 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690529901/5000000000 : ℝ)*x 0 + (-1894271633/10000000000 : ℝ)*x 1 + (5243814573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690529901/5000000000 : ℝ)^4533 ≤ (44908586696971/100000000000000 : ℝ)^3509 := by
    have hnat : (2690529901 : ℕ)^4533*100000000000000^3509 ≤ 44908586696971^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690529901 5000000000 44908586696971 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1894271633/10000000000 : ℝ)^4533 ≤ (11656943978683/100000000000000 : ℝ)^3509 := by
    have hnat : (1894271633 : ℕ)^4533*100000000000000^3509 ≤ 11656943978683^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894271633 10000000000 11656943978683 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243814573/10000000000 : ℝ)^4533 ≤ (21717234658411/50000000000000 : ℝ)^3509 := by
    have hnat : (5243814573 : ℕ)^4533*50000000000000^3509 ≤ 21717234658411^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243814573 10000000000 21717234658411 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690529901/5000000000 : ℝ), (-1894271633/10000000000 : ℝ), (5243814573/10000000000 : ℝ)] ![(44908586696971/100000000000000 : ℝ), (11656943978683/100000000000000 : ℝ), (21717234658411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690529901/5000000000 : ℝ)|^4533 ≤ (44908586696971/100000000000000 : ℝ)^3509
        have hw : |(2690529901/5000000000 : ℝ)|=(2690529901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1894271633/10000000000 : ℝ)|^4533 ≤ (11656943978683/100000000000000 : ℝ)^3509
        have hw : |(-1894271633/10000000000 : ℝ)|=(1894271633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243814573/10000000000 : ℝ)|^4533 ≤ (21717234658411/50000000000000 : ℝ)^3509
        have hw : |(5243814573/10000000000 : ℝ)|=(5243814573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_box_6 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381061731/10000000000 : ℝ)*x 0 + (2621906223/5000000000 : ℝ)*x 1 + (-1894271879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381061731/10000000000 : ℝ)^4533 ≤ (8981721498751/20000000000000 : ℝ)^3509 := by
    have hnat : (5381061731 : ℕ)^4533*20000000000000^3509 ≤ 8981721498751^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381061731 10000000000 8981721498751 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621906223/5000000000 : ℝ)^4533 ≤ (43434446557621/100000000000000 : ℝ)^3509 := by
    have hnat : (2621906223 : ℕ)^4533*100000000000000^3509 ≤ 43434446557621^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621906223 5000000000 43434446557621 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1894271879/10000000000 : ℝ)^4533 ≤ (5828472967141/50000000000000 : ℝ)^3509 := by
    have hnat : (1894271879 : ℕ)^4533*50000000000000^3509 ≤ 5828472967141^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894271879 10000000000 5828472967141 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381061731/10000000000 : ℝ), (2621906223/5000000000 : ℝ), (-1894271879/10000000000 : ℝ)] ![(8981721498751/20000000000000 : ℝ), (43434446557621/100000000000000 : ℝ), (5828472967141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381061731/10000000000 : ℝ)|^4533 ≤ (8981721498751/20000000000000 : ℝ)^3509
        have hw : |(5381061731/10000000000 : ℝ)|=(5381061731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621906223/5000000000 : ℝ)|^4533 ≤ (43434446557621/100000000000000 : ℝ)^3509
        have hw : |(2621906223/5000000000 : ℝ)|=(2621906223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1894271879/10000000000 : ℝ)|^4533 ≤ (5828472967141/50000000000000 : ℝ)^3509
        have hw : |(-1894271879/10000000000 : ℝ)|=(1894271879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_box_7 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4061741627/10000000000 : ℝ)*x 0 + (2188209251/5000000000 : ℝ)*x 1 + (875283673/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4061741627/10000000000 : ℝ)^4533 ≤ (6245343176211/20000000000000 : ℝ)^3509 := by
    have hnat : (4061741627 : ℕ)^4533*20000000000000^3509 ≤ 6245343176211^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4061741627 10000000000 6245343176211 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2188209251/5000000000 : ℝ)^4533 ≤ (6877328549427/20000000000000 : ℝ)^3509 := by
    have hnat : (2188209251 : ℕ)^4533*20000000000000^3509 ≤ 6877328549427^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188209251 5000000000 6877328549427 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (875283673/2000000000 : ℝ)^4533 ≤ (17193320678281/50000000000000 : ℝ)^3509 := by
    have hnat : (875283673 : ℕ)^4533*50000000000000^3509 ≤ 17193320678281^3509*2000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875283673 2000000000 17193320678281 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4061741627/10000000000 : ℝ), (2188209251/5000000000 : ℝ), (875283673/2000000000 : ℝ)] ![(6245343176211/20000000000000 : ℝ), (6877328549427/20000000000000 : ℝ), (17193320678281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4061741627/10000000000 : ℝ)|^4533 ≤ (6245343176211/20000000000000 : ℝ)^3509
        have hw : |(4061741627/10000000000 : ℝ)|=(4061741627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2188209251/5000000000 : ℝ)|^4533 ≤ (6877328549427/20000000000000 : ℝ)^3509
        have hw : |(2188209251/5000000000 : ℝ)|=(2188209251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(875283673/2000000000 : ℝ)|^4533 ≤ (17193320678281/50000000000000 : ℝ)^3509
        have hw : |(875283673/2000000000 : ℝ)|=(875283673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_box_8 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-397233421/2000000000 : ℝ)*x 0 + (102655927/200000000 : ℝ)*x 1 + (5422620801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (397233421/2000000000 : ℝ)^4533 ≤ (6196294219977/50000000000000 : ℝ)^3509 := by
    have hnat : (397233421 : ℕ)^4533*50000000000000^3509 ≤ 6196294219977^3509*2000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397233421 2000000000 6196294219977 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102655927/200000000 : ℝ)^4533 ≤ (42250246653059/100000000000000 : ℝ)^3509 := by
    have hnat : (102655927 : ℕ)^4533*100000000000000^3509 ≤ 42250246653059^3509*200000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102655927 200000000 42250246653059 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422620801/10000000000 : ℝ)^4533 ≤ (907143297909/2000000000000 : ℝ)^3509 := by
    have hnat : (5422620801 : ℕ)^4533*2000000000000^3509 ≤ 907143297909^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422620801 10000000000 907143297909 2000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-397233421/2000000000 : ℝ), (102655927/200000000 : ℝ), (5422620801/10000000000 : ℝ)] ![(6196294219977/50000000000000 : ℝ), (42250246653059/100000000000000 : ℝ), (907143297909/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-397233421/2000000000 : ℝ)|^4533 ≤ (6196294219977/50000000000000 : ℝ)^3509
        have hw : |(-397233421/2000000000 : ℝ)|=(397233421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(102655927/200000000 : ℝ)|^4533 ≤ (42250246653059/100000000000000 : ℝ)^3509
        have hw : |(102655927/200000000 : ℝ)|=(102655927/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422620801/10000000000 : ℝ)|^4533 ≤ (907143297909/2000000000000 : ℝ)^3509
        have hw : |(5422620801/10000000000 : ℝ)|=(5422620801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_box_9 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657077933/1250000000 : ℝ)*x 0 + (-1820169963/10000000000 : ℝ)*x 1 + (5422620807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657077933/1250000000 : ℝ)^4533 ≤ (43571575090817/100000000000000 : ℝ)^3509 := by
    have hnat : (657077933 : ℕ)^4533*100000000000000^3509 ≤ 43571575090817^3509*1250000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657077933 1250000000 43571575090817 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1820169963/10000000000 : ℝ)^4533 ≤ (442850397199/4000000000000 : ℝ)^3509 := by
    have hnat : (1820169963 : ℕ)^4533*4000000000000^3509 ≤ 442850397199^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1820169963 10000000000 442850397199 4000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422620807/10000000000 : ℝ)^4533 ≤ (22678582480141/50000000000000 : ℝ)^3509 := by
    have hnat : (5422620807 : ℕ)^4533*50000000000000^3509 ≤ 22678582480141^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422620807 10000000000 22678582480141 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657077933/1250000000 : ℝ), (-1820169963/10000000000 : ℝ), (5422620807/10000000000 : ℝ)] ![(43571575090817/100000000000000 : ℝ), (442850397199/4000000000000 : ℝ), (22678582480141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657077933/1250000000 : ℝ)|^4533 ≤ (43571575090817/100000000000000 : ℝ)^3509
        have hw : |(657077933/1250000000 : ℝ)|=(657077933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1820169963/10000000000 : ℝ)|^4533 ≤ (442850397199/4000000000000 : ℝ)^3509
        have hw : |(-1820169963/10000000000 : ℝ)|=(1820169963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422620807/10000000000 : ℝ)|^4533 ≤ (22678582480141/50000000000000 : ℝ)^3509
        have hw : |(5422620807/10000000000 : ℝ)|=(5422620807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_box_10 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42052987/80000000 : ℝ)*x 0 + (5422620913/10000000000 : ℝ)*x 1 + (-910084969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42052987/80000000 : ℝ)^4533 ≤ (21785787068913/50000000000000 : ℝ)^3509 := by
    have hnat : (42052987 : ℕ)^4533*50000000000000^3509 ≤ 21785787068913^3509*80000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42052987 80000000 21785787068913 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422620913/10000000000 : ℝ)^4533 ≤ (45357166105649/100000000000000 : ℝ)^3509 := by
    have hnat : (5422620913 : ℕ)^4533*100000000000000^3509 ≤ 45357166105649^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422620913 10000000000 45357166105649 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (910084969/5000000000 : ℝ)^4533 ≤ (11071259733537/100000000000000 : ℝ)^3509 := by
    have hnat : (910084969 : ℕ)^4533*100000000000000^3509 ≤ 11071259733537^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910084969 5000000000 11071259733537 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42052987/80000000 : ℝ), (5422620913/10000000000 : ℝ), (-910084969/5000000000 : ℝ)] ![(21785787068913/50000000000000 : ℝ), (45357166105649/100000000000000 : ℝ), (11071259733537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42052987/80000000 : ℝ)|^4533 ≤ (21785787068913/50000000000000 : ℝ)^3509
        have hw : |(42052987/80000000 : ℝ)|=(42052987/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422620913/10000000000 : ℝ)|^4533 ≤ (45357166105649/100000000000000 : ℝ)^3509
        have hw : |(5422620913/10000000000 : ℝ)|=(5422620913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-910084969/5000000000 : ℝ)|^4533 ≤ (11071259733537/100000000000000 : ℝ)^3509
        have hw : |(-910084969/5000000000 : ℝ)|=(910084969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_box_11 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4521282791/10000000000 : ℝ)*x 0 + (2073095357/5000000000 : ℝ)*x 1 + (4146190649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4521282791/10000000000 : ℝ)^4533 ≤ (8966021698467/25000000000000 : ℝ)^3509 := by
    have hnat : (4521282791 : ℕ)^4533*25000000000000^3509 ≤ 8966021698467^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521282791 10000000000 8966021698467 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2073095357/5000000000 : ℝ)^4533 ≤ (32067956921303/100000000000000 : ℝ)^3509 := by
    have hnat : (2073095357 : ℕ)^4533*100000000000000^3509 ≤ 32067956921303^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073095357 5000000000 32067956921303 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4146190649/10000000000 : ℝ)^4533 ≤ (6413591254373/20000000000000 : ℝ)^3509 := by
    have hnat : (4146190649 : ℕ)^4533*20000000000000^3509 ≤ 6413591254373^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146190649 10000000000 6413591254373 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4521282791/10000000000 : ℝ), (2073095357/5000000000 : ℝ), (4146190649/10000000000 : ℝ)] ![(8966021698467/25000000000000 : ℝ), (32067956921303/100000000000000 : ℝ), (6413591254373/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4521282791/10000000000 : ℝ)|^4533 ≤ (8966021698467/25000000000000 : ℝ)^3509
        have hw : |(4521282791/10000000000 : ℝ)|=(4521282791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2073095357/5000000000 : ℝ)|^4533 ≤ (32067956921303/100000000000000 : ℝ)^3509
        have hw : |(2073095357/5000000000 : ℝ)|=(2073095357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4146190649/10000000000 : ℝ)|^4533 ≤ (6413591254373/20000000000000 : ℝ)^3509
        have hw : |(4146190649/10000000000 : ℝ)|=(4146190649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_box_12 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-868781741/5000000000 : ℝ)*x 0 + (5509654509/10000000000 : ℝ)*x 1 + (5228782453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868781741/5000000000 : ℝ)^4533 ≤ (2606630031193/25000000000000 : ℝ)^3509 := by
    have hnat : (868781741 : ℕ)^4533*25000000000000^3509 ≤ 2606630031193^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868781741 5000000000 2606630031193 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5509654509/10000000000 : ℝ)^4533 ≤ (2893736815197/6250000000000 : ℝ)^3509 := by
    have hnat : (5509654509 : ℕ)^4533*6250000000000^3509 ≤ 2893736815197^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509654509 10000000000 2893736815197 6250000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228782453/10000000000 : ℝ)^4533 ≤ (8654738164017/20000000000000 : ℝ)^3509 := by
    have hnat : (5228782453 : ℕ)^4533*20000000000000^3509 ≤ 8654738164017^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228782453 10000000000 8654738164017 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-868781741/5000000000 : ℝ), (5509654509/10000000000 : ℝ), (5228782453/10000000000 : ℝ)] ![(2606630031193/25000000000000 : ℝ), (2893736815197/6250000000000 : ℝ), (8654738164017/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-868781741/5000000000 : ℝ)|^4533 ≤ (2606630031193/25000000000000 : ℝ)^3509
        have hw : |(-868781741/5000000000 : ℝ)|=(868781741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5509654509/10000000000 : ℝ)|^4533 ≤ (2893736815197/6250000000000 : ℝ)^3509
        have hw : |(5509654509/10000000000 : ℝ)|=(5509654509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228782453/10000000000 : ℝ)|^4533 ≤ (8654738164017/20000000000000 : ℝ)^3509
        have hw : |(5228782453/10000000000 : ℝ)|=(5228782453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_box_13 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2695760589/5000000000 : ℝ)*x 0 + (-950150923/5000000000 : ℝ)*x 1 + (5228782563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2695760589/5000000000 : ℝ)^4533 ≤ (9004280807221/20000000000000 : ℝ)^3509 := by
    have hnat : (2695760589 : ℕ)^4533*20000000000000^3509 ≤ 9004280807221^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695760589 5000000000 9004280807221 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (950150923/5000000000 : ℝ)^4533 ≤ (11704903957729/100000000000000 : ℝ)^3509 := by
    have hnat : (950150923 : ℕ)^4533*100000000000000^3509 ≤ 11704903957729^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950150923 5000000000 11704903957729 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228782563/10000000000 : ℝ)^4533 ≤ (8654738399223/20000000000000 : ℝ)^3509 := by
    have hnat : (5228782563 : ℕ)^4533*20000000000000^3509 ≤ 8654738399223^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228782563 10000000000 8654738399223 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2695760589/5000000000 : ℝ), (-950150923/5000000000 : ℝ), (5228782563/10000000000 : ℝ)] ![(9004280807221/20000000000000 : ℝ), (11704903957729/100000000000000 : ℝ), (8654738399223/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2695760589/5000000000 : ℝ)|^4533 ≤ (9004280807221/20000000000000 : ℝ)^3509
        have hw : |(2695760589/5000000000 : ℝ)|=(2695760589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-950150923/5000000000 : ℝ)|^4533 ≤ (11704903957729/100000000000000 : ℝ)^3509
        have hw : |(-950150923/5000000000 : ℝ)|=(950150923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228782563/10000000000 : ℝ)|^4533 ≤ (8654738399223/20000000000000 : ℝ)^3509
        have hw : |(5228782563/10000000000 : ℝ)|=(5228782563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_box_14 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391521143/10000000000 : ℝ)*x 0 + (2614391257/5000000000 : ℝ)*x 1 + (-1900301959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391521143/10000000000 : ℝ)^4533 ≤ (45021403658551/100000000000000 : ℝ)^3509 := by
    have hnat : (5391521143 : ℕ)^4533*100000000000000^3509 ≤ 45021403658551^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391521143 10000000000 45021403658551 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614391257/5000000000 : ℝ)^4533 ≤ (43273691472247/100000000000000 : ℝ)^3509 := by
    have hnat : (2614391257 : ℕ)^4533*100000000000000^3509 ≤ 43273691472247^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614391257 5000000000 43273691472247 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1900301959/10000000000 : ℝ)^4533 ≤ (11704904856867/100000000000000 : ℝ)^3509 := by
    have hnat : (1900301959 : ℕ)^4533*100000000000000^3509 ≤ 11704904856867^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900301959 10000000000 11704904856867 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391521143/10000000000 : ℝ), (2614391257/5000000000 : ℝ), (-1900301959/10000000000 : ℝ)] ![(45021403658551/100000000000000 : ℝ), (43273691472247/100000000000000 : ℝ), (11704904856867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391521143/10000000000 : ℝ)|^4533 ≤ (45021403658551/100000000000000 : ℝ)^3509
        have hw : |(5391521143/10000000000 : ℝ)|=(5391521143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614391257/5000000000 : ℝ)|^4533 ≤ (43273691472247/100000000000000 : ℝ)^3509
        have hw : |(2614391257/5000000000 : ℝ)|=(2614391257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1900301959/10000000000 : ℝ)|^4533 ≤ (11704904856867/100000000000000 : ℝ)^3509
        have hw : |(-1900301959/10000000000 : ℝ)|=(1900301959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_box_15 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (402215233/1000000000 : ℝ)*x 0 + (2197873291/5000000000 : ℝ)*x 1 + (549468341/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (402215233/1000000000 : ℝ)^4533 ≤ (616681877303/2000000000000 : ℝ)^3509 := by
    have hnat : (402215233 : ℕ)^4533*2000000000000^3509 ≤ 616681877303^3509*1000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402215233 1000000000 616681877303 2000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197873291/5000000000 : ℝ)^4533 ≤ (17291476159387/50000000000000 : ℝ)^3509 := by
    have hnat : (2197873291 : ℕ)^4533*50000000000000^3509 ≤ 17291476159387^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197873291 5000000000 17291476159387 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549468341/1250000000 : ℝ)^4533 ≤ (6916590760521/20000000000000 : ℝ)^3509 := by
    have hnat : (549468341 : ℕ)^4533*20000000000000^3509 ≤ 6916590760521^3509*1250000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549468341 1250000000 6916590760521 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(402215233/1000000000 : ℝ), (2197873291/5000000000 : ℝ), (549468341/1250000000 : ℝ)] ![(616681877303/2000000000000 : ℝ), (17291476159387/50000000000000 : ℝ), (6916590760521/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(402215233/1000000000 : ℝ)|^4533 ≤ (616681877303/2000000000000 : ℝ)^3509
        have hw : |(402215233/1000000000 : ℝ)|=(402215233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2197873291/5000000000 : ℝ)|^4533 ≤ (17291476159387/50000000000000 : ℝ)^3509
        have hw : |(2197873291/5000000000 : ℝ)|=(2197873291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(549468341/1250000000 : ℝ)|^4533 ≤ (6916590760521/20000000000000 : ℝ)^3509
        have hw : |(549468341/1250000000 : ℝ)|=(549468341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1518_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10939/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63747/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1833/3125 : ℝ) ∧ (80383/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (2151/2500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10939/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10939/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10939/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10939/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10939/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10939/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10939/100000 : ℝ) ^ (4531/1024 : ℝ) ≤ (5593242880515159/100000000000000000000 : ℝ) := by
    have hpowers : (10939/100000 : ℝ)^4531 ≤ (5593242880515159/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10939 : ℕ)^4531*100000000000000000000^1024 ≤ 5593242880515159^1024*100000^4531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10939 100000 5593242880515159 100000000000000000000 4531 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10939/100000 : ℝ)) (X := (5593242880515159/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4531/1024 : ℝ) ≤ (13008796329804297/50000000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4531 ≤ (13008796329804297/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4531*50000000000000000000^1024 ≤ 13008796329804297^1024*100000^4531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 13008796329804297 50000000000000000000 4531 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (13008796329804297/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005593242880515159/50000000000000000000 : ℝ) ≤ (1000025280215287/1000000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (50005593242880515159/50000000000000000000 : ℝ)^1024 ≤ (1000025280215287/1000000000000000 : ℝ)^4531 := by
      have hnat : (50005593242880515159 : ℕ)^1024*1000000000000000^4531 ≤ 1000025280215287^4531*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005593242880515159 50000000000000000000 1000025280215287 1000000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000025280215287/1000000000000000 : ℝ)) (X := (50005593242880515159/50000000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100031610835540123753/100000000000000000000 : ℝ) ≤ (5000357156659001/5000000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (100031610835540123753/100000000000000000000 : ℝ)^1024 ≤ (5000357156659001/5000000000000000 : ℝ)^4531 := by
      have hnat : (100031610835540123753 : ℕ)^1024*5000000000000000^4531 ≤ 5000357156659001^4531*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100031610835540123753 100000000000000000000 5000357156659001 5000000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000357156659001/5000000000000000 : ℝ)) (X := (100031610835540123753/100000000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013008796329804297/25000000000000000000 : ℝ) ≤ (5000587912241567/5000000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (25013008796329804297/25000000000000000000 : ℝ)^1024 ≤ (5000587912241567/5000000000000000 : ℝ)^4531 := by
      have hnat : (25013008796329804297 : ℕ)^1024*5000000000000000^4531 ≤ 5000587912241567^4531*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013008796329804297 25000000000000000000 5000587912241567 5000000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000587912241567/5000000000000000 : ℝ)) (X := (25013008796329804297/25000000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5593242880515159/100000000000000000000 : ℝ) ≤ ((5678881473963985423/5680000000000000000 : ℝ)+2*(115377791283/113600000000000 : ℝ)*(10939/100000 : ℝ))^(4531/1024 : ℝ) := by
    rw [show (5678881473963985423/5680000000000000000 : ℝ)+2*(115377791283/113600000000000 : ℝ)*(10939/100000 : ℝ)=(1000025280215287/1000000000000000 : ℝ) by norm_num, show 1+2*(5593242880515159/100000000000000000000 : ℝ)=(50005593242880515159/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13008796329804297/50000000000000000000 : ℝ)+(5593242880515159/100000000000000000000 : ℝ) ≤ ((5678881473963985423/5680000000000000000 : ℝ)+(115377791283/113600000000000 : ℝ)*((15483/100000 : ℝ)+(10939/100000 : ℝ)))^(4531/1024 : ℝ) := by
    rw [show (5678881473963985423/5680000000000000000 : ℝ)+(115377791283/113600000000000 : ℝ)*((15483/100000 : ℝ)+(10939/100000 : ℝ))=(5000357156659001/5000000000000000 : ℝ) by norm_num, show 1+(13008796329804297/50000000000000000000 : ℝ)+(5593242880515159/100000000000000000000 : ℝ)=(100031610835540123753/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13008796329804297/50000000000000000000 : ℝ) ≤ ((5678881473963985423/5680000000000000000 : ℝ)+2*(115377791283/113600000000000 : ℝ)*(15483/100000 : ℝ))^(4531/1024 : ℝ) := by
    rw [show (5678881473963985423/5680000000000000000 : ℝ)+2*(115377791283/113600000000000 : ℝ)*(15483/100000 : ℝ)=(5000587912241567/5000000000000000 : ℝ) by norm_num, show 1+2*(13008796329804297/50000000000000000000 : ℝ)=(25013008796329804297/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5678881473963985423/5680000000000000000 : ℝ)*(X 1 0+X 2 0)+(115377791283/113600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (10939/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (5678881473963985423/5680000000000000000 : ℝ)) (alpha := (115377791283/113600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5678881473963985423/5680000000000000000 : ℝ)*(X 0 1+X 2 1)+(115377791283/113600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (10939/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (5678881473963985423/5680000000000000000 : ℝ)) (alpha := (115377791283/113600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5678881473963985423/5680000000000000000 : ℝ)*(X 0 2+X 1 2)+(115377791283/113600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (10939/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (5678881473963985423/5680000000000000000 : ℝ)) (alpha := (115377791283/113600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1646626853/10000000000 : ℝ)*X 0 0+(1080437071/2000000000 : ℝ)*X 0 1+(84409147/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270850217/10000000000 : ℝ)*X 1 0+(-1828855179/10000000000 : ℝ)*X 1 1+(2701092767/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270850213/10000000000 : ℝ)*X 2 0+(5402185429/10000000000 : ℝ)*X 2 1+(-1828855329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2234891133/5000000000 : ℝ)*X 0 0+(521566461/1250000000 : ℝ)*X 0 1+(2086265797/5000000000 : ℝ)*X 0 2+(2234891133/5000000000 : ℝ)*X 1 0+(521566461/1250000000 : ℝ)*X 1 1+(2086265797/5000000000 : ℝ)*X 1 2+(2234891133/5000000000 : ℝ)*X 2 0+(521566461/1250000000 : ℝ)*X 2 1+(2086265797/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2077186141/10000000000 : ℝ)*X 0 0+(1310953771/2500000000 : ℝ)*X 0 1+(2621906243/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2690529901/5000000000 : ℝ)*X 1 0+(-1894271633/10000000000 : ℝ)*X 1 1+(5243814573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5381061731/10000000000 : ℝ)*X 2 0+(2621906223/5000000000 : ℝ)*X 2 1+(-1894271879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4061741627/10000000000 : ℝ)*X 0 0+(2188209251/5000000000 : ℝ)*X 0 1+(875283673/2000000000 : ℝ)*X 0 2+(4061741627/10000000000 : ℝ)*X 1 0+(2188209251/5000000000 : ℝ)*X 1 1+(875283673/2000000000 : ℝ)*X 1 2+(4061741627/10000000000 : ℝ)*X 2 0+(2188209251/5000000000 : ℝ)*X 2 1+(875283673/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-397233421/2000000000 : ℝ)*X 0 0+(102655927/200000000 : ℝ)*X 0 1+(5422620801/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((657077933/1250000000 : ℝ)*X 1 0+(-1820169963/10000000000 : ℝ)*X 1 1+(5422620807/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((42052987/80000000 : ℝ)*X 2 0+(5422620913/10000000000 : ℝ)*X 2 1+(-910084969/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4521282791/10000000000 : ℝ)*X 0 0+(2073095357/5000000000 : ℝ)*X 0 1+(4146190649/10000000000 : ℝ)*X 0 2+(4521282791/10000000000 : ℝ)*X 1 0+(2073095357/5000000000 : ℝ)*X 1 1+(4146190649/10000000000 : ℝ)*X 1 2+(4521282791/10000000000 : ℝ)*X 2 0+(2073095357/5000000000 : ℝ)*X 2 1+(4146190649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-868781741/5000000000 : ℝ)*X 0 0+(5509654509/10000000000 : ℝ)*X 0 1+(5228782453/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2695760589/5000000000 : ℝ)*X 1 0+(-950150923/5000000000 : ℝ)*X 1 1+(5228782563/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5391521143/10000000000 : ℝ)*X 2 0+(2614391257/5000000000 : ℝ)*X 2 1+(-1900301959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((402215233/1000000000 : ℝ)*X 0 0+(2197873291/5000000000 : ℝ)*X 0 1+(549468341/1250000000 : ℝ)*X 0 2+(402215233/1000000000 : ℝ)*X 1 0+(2197873291/5000000000 : ℝ)*X 1 1+(549468341/1250000000 : ℝ)*X 1 2+(402215233/1000000000 : ℝ)*X 2 0+(2197873291/5000000000 : ℝ)*X 2 1+(549468341/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63747/100000 : ℝ) ≤ (-181035302329141845409199190414207/284000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65162351/50000000000000 : ℝ)*(upper1) + (109528907/100000000000000 : ℝ)*(upper4) + (327121033/100000000000000 : ℝ)*(upper5) + (2232247416363397/100000000000000 : ℝ)*(major0) + (2232247416363397/100000000000000 : ℝ)*(major1) + (2232247416363397/100000000000000 : ℝ)*(major2) + (21528297951/50000000000000 : ℝ)*(sp2) + (9032232621/100000000000000 : ℝ)*(sp3) + (312340131625407/10000000000000 : ℝ)*(sp4) + (3123425941687991/100000000000000 : ℝ)*(sp5) + (3123400521471003/100000000000000 : ℝ)*(sp6) + (681145248674263/50000000000000 : ℝ)*(sp7) + (8452362567/20000000000000 : ℝ)*(sp8) + (8818189457/50000000000000 : ℝ)*(sp13) + (1362299529581147/100000000000000 : ℝ)*(f.failure) + (624688715613381/20000000000000 : ℝ)*(f.sum) + (28072989632111/5680000000000000000000000000 : ℝ)*base65 + (304985681443688069/568000000000000000000000000000000 : ℝ)*base68 + (2731447765595688069/568000000000000000000000000000000 : ℝ)*base70 + (3605749396380311931/568000000000000000000000000000000 : ℝ)*base71 + (268695568689/5680000000000000000000000000 : ℝ)*base74 + (3501014249355688069/568000000000000000000000000000000 : ℝ)*base76 + (211911995579688069/568000000000000000000000000000000 : ℝ)*base78 + (52018696268311931/568000000000000000000000000000000 : ℝ)*base79 + (15502647075569/5680000000000000000000000000 : ℝ)*base82 + (8791477/5000000000000000000000 : ℝ)*base89 + (8791477/5000000000000000000000 : ℝ)*base91 + (8791477/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (1833/3125 : ℝ) ≤ (16658973605950179302461273734339/28400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11144761/50000000000000 : ℝ)*(lower0) + (3052681/100000000000000 : ℝ)*(lower1) + (6602477/20000000000000 : ℝ)*(lower4) + (287597/1250000000000 : ℝ)*(lower5) + (461776959485031/20000000000000 : ℝ)*(major0) + (461776959485031/20000000000000 : ℝ)*(major1) + (461776959485031/20000000000000 : ℝ)*(major2) + (398643216013407/12500000000000 : ℝ)*(sp0) + (159457163637843/5000000000000 : ℝ)*(sp1) + (3189146152440077/100000000000000 : ℝ)*(sp2) + (704534956638807/50000000000000 : ℝ)*(sp3) + (3622893353/100000000000000 : ℝ)*(sp5) + (148642027/20000000000000 : ℝ)*(sp6) + (1167542957/100000000000000 : ℝ)*(sp12) + (704534956638807/50000000000000 : ℝ)*(f.failure) + (797286723912553/25000000000000 : ℝ)*(f.sum) + (2220898874021/1136000000000000000000000000 : ℝ)*base65 + (805841684170646887/113600000000000000000000000000000 : ℝ)*base68 + (528223648106646887/113600000000000000000000000000000 : ℝ)*base70 + (40122772770646887/113600000000000000000000000000000 : ℝ)*base72 + (147165130877/45440000000000000000000000 : ℝ)*base73 + (47700480650646887/113600000000000000000000000000000 : ℝ)*base76 + (197401445666646887/113600000000000000000000000000000 : ℝ)*base78 + (903531681029353113/113600000000000000000000000000000 : ℝ)*base79 + (38067319817/9088000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (10523463/2500000000000000000000 : ℝ)*base90 + (10523463/2500000000000000000000 : ℝ)*base92 + (10523463/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80383/100000 : ℝ) ≤ (114148109370335053768811615647287/142000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3453057/50000000000000 : ℝ)*(upper0) + (2656959/12500000000000 : ℝ)*(upper1) + (9332349/100000000000000 : ℝ)*(upper2) + (1251031128180077/50000000000000 : ℝ)*(major0) + (1251031128180077/50000000000000 : ℝ)*(major1) + (1251031128180077/50000000000000 : ℝ)*(major2) + (27307754819/100000000000000 : ℝ)*(sp1) + (42332654647/100000000000000 : ℝ)*(sp2) + (2111541881/25000000000000 : ℝ)*(sp3) + (227046557/12500000000000 : ℝ)*(sp4) + (172518240155013/5000000000000 : ℝ)*(sp8) + (431292413964737/12500000000000 : ℝ)*(sp9) + (3450324286818069/100000000000000 : ℝ)*(sp10) + (30539082324839/2000000000000 : ℝ)*(sp11) + (763481281204737/50000000000000 : ℝ)*(f.failure) + (862591654868179/25000000000000 : ℝ)*(f.sum) + (3477638687129/2840000000000000000000000000 : ℝ)*base66 + (544740950242567571/284000000000000000000000000000000 : ℝ)*base67 + (124976861498567571/284000000000000000000000000000000 : ℝ)*base69 + (355834178297432429/284000000000000000000000000000000 : ℝ)*base72 + (69642974757871/2840000000000000000000000000 : ℝ)*base73 + (3583910403570567571/284000000000000000000000000000000 : ℝ)*base75 + (1236772420493432429/284000000000000000000000000000000 : ℝ)*base78 + (14758589285538567571/284000000000000000000000000000000 : ℝ)*base79 + (2698302041151/2840000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1274833/2500000000000000000000 : ℝ)*base90 + (1274833/2500000000000000000000 : ℝ)*base92 + (1274833/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-2151/2500 : ℝ) ≤ (-61086878620945481171014402290609/71000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6938817/50000000000000 : ℝ)*(lower0) + (7082559/50000000000000 : ℝ)*(lower1) + (2173323/5000000000000 : ℝ)*(lower4) + (635320208650713/25000000000000 : ℝ)*(major0) + (635320208650713/25000000000000 : ℝ)*(major1) + (635320208650713/25000000000000 : ℝ)*(major2) + (3096805879/100000000000000 : ℝ)*(sp0) + (4773290969/25000000000000 : ℝ)*(sp5) + (9748030221/20000000000000 : ℝ)*(sp6) + (5943667083/20000000000000 : ℝ)*(sp7) + (445042614870643/12500000000000 : ℝ)*(sp12) + (3560324922607147/100000000000000 : ℝ)*(sp13) + (1780147637809959/50000000000000 : ℝ)*(sp14) + (387716805209197/25000000000000 : ℝ)*(sp15) + (1550896939172203/100000000000000 : ℝ)*(f.failure) + (1780172007885511/50000000000000 : ℝ)*(f.sum) + (8177192743779/1420000000000000000000000000 : ℝ)*base65 + (1359230735184493401/142000000000000000000000000000000 : ℝ)*base68 + (1098989424856493401/142000000000000000000000000000000 : ℝ)*base70 + (1826902719176493401/142000000000000000000000000000000 : ℝ)*base72 + (3824488253141/1420000000000000000000000000 : ℝ)*base74 + (1322001964846493401/142000000000000000000000000000000 : ℝ)*base76 + (2456675177338493401/142000000000000000000000000000000 : ℝ)*base78 + (2211661043606493401/142000000000000000000000000000000 : ℝ)*base80 + (4117363850339/1420000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (35918373/5000000000000000000000 : ℝ)*base89 + (35918373/5000000000000000000000 : ℝ)*base91 + (35918373/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1518_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10939/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63747/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1833/3125 : ℝ) else (80383/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2151/2500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1518_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1518_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5469/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63747/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1833/3125 : ℝ) else (80383/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2151/2500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1518_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1518_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5469/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63747/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1833/3125 : ℝ) else (80383/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2151/2500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1518_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

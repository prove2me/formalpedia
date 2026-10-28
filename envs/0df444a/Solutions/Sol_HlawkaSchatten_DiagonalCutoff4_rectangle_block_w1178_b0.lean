-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1178_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:48:26.523064+00:00
-- url     : https://prove2.me/submissions/846eb029-e002-4e11-b133-c9530e04c1e7

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
theorem support_rectangle_w1178_s0_0 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-940234483/5000000000 : ℝ)*x 0 + (6046046897/10000000000 : ℝ)*x 1 + (4785008439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (940234483/5000000000 : ℝ)^8371 ≤ (5472342218137/50000000000000 : ℝ)^6323 := by
    have hnat : (940234483 : ℕ)^8371*50000000000000^6323 ≤ 5472342218137^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940234483 5000000000 5472342218137 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6046046897/10000000000 : ℝ)^8371 ≤ (51367782135227/100000000000000 : ℝ)^6323 := by
    have hnat : (6046046897 : ℕ)^8371*100000000000000^6323 ≤ 51367782135227^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6046046897 10000000000 51367782135227 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4785008439/10000000000 : ℝ)^8371 ≤ (18843766707651/50000000000000 : ℝ)^6323 := by
    have hnat : (4785008439 : ℕ)^8371*50000000000000^6323 ≤ 18843766707651^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4785008439 10000000000 18843766707651 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-940234483/5000000000 : ℝ), (6046046897/10000000000 : ℝ), (4785008439/10000000000 : ℝ)] ![(5472342218137/50000000000000 : ℝ), (51367782135227/100000000000000 : ℝ), (18843766707651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-940234483/5000000000 : ℝ)|^8371 ≤ (5472342218137/50000000000000 : ℝ)^6323
        have hw : |(-940234483/5000000000 : ℝ)|=(940234483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6046046897/10000000000 : ℝ)|^8371 ≤ (51367782135227/100000000000000 : ℝ)^6323
        have hw : |(6046046897/10000000000 : ℝ)|=(6046046897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4785008439/10000000000 : ℝ)|^8371 ≤ (18843766707651/50000000000000 : ℝ)^6323
        have hw : |(4785008439/10000000000 : ℝ)|=(4785008439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s0_1 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2757382711/5000000000 : ℝ)*x 0 + (-1301572673/5000000000 : ℝ)*x 1 + (957001687/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757382711/5000000000 : ℝ)^8371 ≤ (22739371818529/50000000000000 : ℝ)^6323 := by
    have hnat : (2757382711 : ℕ)^8371*50000000000000^6323 ≤ 22739371818529^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757382711 5000000000 22739371818529 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1301572673/5000000000 : ℝ)^8371 ≤ (841686148977/5000000000000 : ℝ)^6323 := by
    have hnat : (1301572673 : ℕ)^8371*5000000000000^6323 ≤ 841686148977^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301572673 5000000000 841686148977 5000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (957001687/2000000000 : ℝ)^8371 ≤ (37687533373593/100000000000000 : ℝ)^6323 := by
    have hnat : (957001687 : ℕ)^8371*100000000000000^6323 ≤ 37687533373593^6323*2000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957001687 2000000000 37687533373593 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757382711/5000000000 : ℝ), (-1301572673/5000000000 : ℝ), (957001687/2000000000 : ℝ)] ![(22739371818529/50000000000000 : ℝ), (841686148977/5000000000000 : ℝ), (37687533373593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757382711/5000000000 : ℝ)|^8371 ≤ (22739371818529/50000000000000 : ℝ)^6323
        have hw : |(2757382711/5000000000 : ℝ)|=(2757382711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1301572673/5000000000 : ℝ)|^8371 ≤ (841686148977/5000000000000 : ℝ)^6323
        have hw : |(-1301572673/5000000000 : ℝ)|=(1301572673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(957001687/2000000000 : ℝ)|^8371 ≤ (37687533373593/100000000000000 : ℝ)^6323
        have hw : |(957001687/2000000000 : ℝ)|=(957001687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s0_2 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1378691341/2500000000 : ℝ)*x 0 + (4785008453/10000000000 : ℝ)*x 1 + (-1301572699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1378691341/2500000000 : ℝ)^8371 ≤ (1819149720153/4000000000000 : ℝ)^6323 := by
    have hnat : (1378691341 : ℕ)^8371*4000000000000^6323 ≤ 1819149720153^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378691341 2500000000 1819149720153 4000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4785008453/10000000000 : ℝ)^8371 ≤ (37687533561283/100000000000000 : ℝ)^6323 := by
    have hnat : (4785008453 : ℕ)^8371*100000000000000^6323 ≤ 37687533561283^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4785008453 10000000000 37687533561283 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1301572699/5000000000 : ℝ)^8371 ≤ (4208430856181/25000000000000 : ℝ)^6323 := by
    have hnat : (1301572699 : ℕ)^8371*25000000000000^6323 ≤ 4208430856181^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301572699 5000000000 4208430856181 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1378691341/2500000000 : ℝ), (4785008453/10000000000 : ℝ), (-1301572699/5000000000 : ℝ)] ![(1819149720153/4000000000000 : ℝ), (37687533561283/100000000000000 : ℝ), (4208430856181/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1378691341/2500000000 : ℝ)|^8371 ≤ (1819149720153/4000000000000 : ℝ)^6323
        have hw : |(1378691341/2500000000 : ℝ)|=(1378691341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4785008453/10000000000 : ℝ)|^8371 ≤ (37687533561283/100000000000000 : ℝ)^6323
        have hw : |(4785008453/10000000000 : ℝ)|=(4785008453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1301572699/5000000000 : ℝ)|^8371 ≤ (4208430856181/25000000000000 : ℝ)^6323
        have hw : |(-1301572699/5000000000 : ℝ)|=(1301572699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s0_3 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (524761857/1250000000 : ℝ)*x 0 + (3119469269/10000000000 : ℝ)*x 1 + (705750019/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524761857/1250000000 : ℝ)^8371 ≤ (31692758736467/100000000000000 : ℝ)^6323 := by
    have hnat : (524761857 : ℕ)^8371*100000000000000^6323 ≤ 31692758736467^6323*1250000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524761857 1250000000 31692758736467 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3119469269/10000000000 : ℝ)^8371 ≤ (21390209114467/100000000000000 : ℝ)^6323 := by
    have hnat : (3119469269 : ℕ)^8371*100000000000000^6323 ≤ 21390209114467^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3119469269 10000000000 21390209114467 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (705750019/1250000000 : ℝ)^8371 ≤ (23458516065711/50000000000000 : ℝ)^6323 := by
    have hnat : (705750019 : ℕ)^8371*50000000000000^6323 ≤ 23458516065711^6323*1250000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      705750019 1250000000 23458516065711 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524761857/1250000000 : ℝ), (3119469269/10000000000 : ℝ), (705750019/1250000000 : ℝ)] ![(31692758736467/100000000000000 : ℝ), (21390209114467/100000000000000 : ℝ), (23458516065711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524761857/1250000000 : ℝ)|^8371 ≤ (31692758736467/100000000000000 : ℝ)^6323
        have hw : |(524761857/1250000000 : ℝ)|=(524761857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3119469269/10000000000 : ℝ)|^8371 ≤ (21390209114467/100000000000000 : ℝ)^6323
        have hw : |(3119469269/10000000000 : ℝ)|=(3119469269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(705750019/1250000000 : ℝ)|^8371 ≤ (23458516065711/50000000000000 : ℝ)^6323
        have hw : |(705750019/1250000000 : ℝ)|=(705750019/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s0_4 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-235688681/1250000000 : ℝ)*x 0 + (2408760347/5000000000 : ℝ)*x 1 + (3006194493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (235688681/1250000000 : ℝ)^8371 ≤ (343235620687/3125000000000 : ℝ)^6323 := by
    have hnat : (235688681 : ℕ)^8371*3125000000000^6323 ≤ 343235620687^6323*1250000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235688681 1250000000 343235620687 3125000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2408760347/5000000000 : ℝ)^8371 ≤ (1188341212961/3125000000000 : ℝ)^6323 := by
    have hnat : (2408760347 : ℕ)^8371*3125000000000^6323 ≤ 1188341212961^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2408760347 5000000000 1188341212961 3125000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3006194493/5000000000 : ℝ)^8371 ≤ (50989541302247/100000000000000 : ℝ)^6323 := by
    have hnat : (3006194493 : ℕ)^8371*100000000000000^6323 ≤ 50989541302247^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3006194493 5000000000 50989541302247 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-235688681/1250000000 : ℝ), (2408760347/5000000000 : ℝ), (3006194493/5000000000 : ℝ)] ![(343235620687/3125000000000 : ℝ), (1188341212961/3125000000000 : ℝ), (50989541302247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-235688681/1250000000 : ℝ)|^8371 ≤ (343235620687/3125000000000 : ℝ)^6323
        have hw : |(-235688681/1250000000 : ℝ)|=(235688681/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2408760347/5000000000 : ℝ)|^8371 ≤ (1188341212961/3125000000000 : ℝ)^6323
        have hw : |(2408760347/5000000000 : ℝ)|=(2408760347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3006194493/5000000000 : ℝ)|^8371 ≤ (50989541302247/100000000000000 : ℝ)^6323
        have hw : |(3006194493/5000000000 : ℝ)|=(3006194493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s0_5 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1292985381/2500000000 : ℝ)*x 0 + (-275153/2000000 : ℝ)*x 1 + (6012388719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292985381/2500000000 : ℝ)^8371 ≤ (41774080666789/100000000000000 : ℝ)^6323 := by
    have hnat : (1292985381 : ℕ)^8371*100000000000000^6323 ≤ 41774080666789^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292985381 2500000000 41774080666789 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275153/2000000 : ℝ)^8371 ≤ (3618190505407/50000000000000 : ℝ)^6323 := by
    have hnat : (275153 : ℕ)^8371*50000000000000^6323 ≤ 3618190505407^6323*2000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275153 2000000 3618190505407 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6012388719/10000000000 : ℝ)^8371 ≤ (50989538304469/100000000000000 : ℝ)^6323 := by
    have hnat : (6012388719 : ℕ)^8371*100000000000000^6323 ≤ 50989538304469^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6012388719 10000000000 50989538304469 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292985381/2500000000 : ℝ), (-275153/2000000 : ℝ), (6012388719/10000000000 : ℝ)] ![(41774080666789/100000000000000 : ℝ), (3618190505407/50000000000000 : ℝ), (50989538304469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292985381/2500000000 : ℝ)|^8371 ≤ (41774080666789/100000000000000 : ℝ)^6323
        have hw : |(1292985381/2500000000 : ℝ)|=(1292985381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-275153/2000000 : ℝ)|^8371 ≤ (3618190505407/50000000000000 : ℝ)^6323
        have hw : |(-275153/2000000 : ℝ)|=(275153/2000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6012388719/10000000000 : ℝ)|^8371 ≤ (50989538304469/100000000000000 : ℝ)^6323
        have hw : |(6012388719/10000000000 : ℝ)|=(6012388719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s0_6 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1292985369/2500000000 : ℝ)*x 0 + (1503097213/2500000000 : ℝ)*x 1 + (-1375764859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292985369/2500000000 : ℝ)^8371 ≤ (10443520038379/25000000000000 : ℝ)^6323 := by
    have hnat : (1292985369 : ℕ)^8371*25000000000000^6323 ≤ 10443520038379^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292985369 2500000000 10443520038379 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1503097213/2500000000 : ℝ)^8371 ≤ (3186846237359/6250000000000 : ℝ)^6323 := by
    have hnat : (1503097213 : ℕ)^8371*6250000000000^6323 ≤ 3186846237359^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503097213 2500000000 3186846237359 6250000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1375764859/10000000000 : ℝ)^8371 ≤ (904547503619/12500000000000 : ℝ)^6323 := by
    have hnat : (1375764859 : ℕ)^8371*12500000000000^6323 ≤ 904547503619^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375764859 10000000000 904547503619 12500000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292985369/2500000000 : ℝ), (1503097213/2500000000 : ℝ), (-1375764859/10000000000 : ℝ)] ![(10443520038379/25000000000000 : ℝ), (3186846237359/6250000000000 : ℝ), (904547503619/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292985369/2500000000 : ℝ)|^8371 ≤ (10443520038379/25000000000000 : ℝ)^6323
        have hw : |(1292985369/2500000000 : ℝ)|=(1292985369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1503097213/2500000000 : ℝ)|^8371 ≤ (3186846237359/6250000000000 : ℝ)^6323
        have hw : |(1503097213/2500000000 : ℝ)|=(1503097213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1375764859/10000000000 : ℝ)|^8371 ≤ (904547503619/12500000000000 : ℝ)^6323
        have hw : |(-1375764859/10000000000 : ℝ)|=(1375764859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s0_7 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1052048447/2500000000 : ℝ)*x 0 + (5450059/9765625 : ℝ)*x 1 + (3186904307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052048447/2500000000 : ℝ)^8371 ≤ (3179373201891/10000000000000 : ℝ)^6323 := by
    have hnat : (1052048447 : ℕ)^8371*10000000000000^6323 ≤ 3179373201891^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052048447 2500000000 3179373201891 10000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5450059/9765625 : ℝ)^8371 ≤ (46201753157173/100000000000000 : ℝ)^6323 := by
    have hnat : (5450059 : ℕ)^8371*100000000000000^6323 ≤ 46201753157173^6323*9765625^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450059 9765625 46201753157173 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3186904307/10000000000 : ℝ)^8371 ≤ (22004514811743/100000000000000 : ℝ)^6323 := by
    have hnat : (3186904307 : ℕ)^8371*100000000000000^6323 ≤ 22004514811743^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3186904307 10000000000 22004514811743 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052048447/2500000000 : ℝ), (5450059/9765625 : ℝ), (3186904307/10000000000 : ℝ)] ![(3179373201891/10000000000000 : ℝ), (46201753157173/100000000000000 : ℝ), (22004514811743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052048447/2500000000 : ℝ)|^8371 ≤ (3179373201891/10000000000000 : ℝ)^6323
        have hw : |(1052048447/2500000000 : ℝ)|=(1052048447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5450059/9765625 : ℝ)|^8371 ≤ (46201753157173/100000000000000 : ℝ)^6323
        have hw : |(5450059/9765625 : ℝ)|=(5450059/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3186904307/10000000000 : ℝ)|^8371 ≤ (22004514811743/100000000000000 : ℝ)^6323
        have hw : |(3186904307/10000000000 : ℝ)|=(3186904307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1178_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (561/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13839/50000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (4185/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4185 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4185*1^1024 ≤ 0^1024*1^4185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4185 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4185/1024 : ℝ) ≤ (1182016085958494587/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4185 ≤ (1182016085958494587/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4185*50000000000000000000^1024 ≤ 1182016085958494587^1024*5^4185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1182016085958494587 50000000000000000000 4185 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1182016085958494587/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4185 := by
      have hnat : (1 : ℕ)^1024*1^4185 ≤ 1^4185*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (51182016085958494587/50000000000000000000 : ℝ) ≤ (10057334541690131/10000000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (51182016085958494587/50000000000000000000 : ℝ)^1024 ≤ (10057334541690131/10000000000000000 : ℝ)^4185 := by
      have hnat : (51182016085958494587 : ℕ)^1024*10000000000000000^4185 ≤ 10057334541690131^4185*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51182016085958494587 50000000000000000000 10057334541690131 10000000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10057334541690131/10000000000000000 : ℝ)) (X := (51182016085958494587/50000000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (26182016085958494587/25000000000000000000 : ℝ) ≤ (5057334541690131/5000000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (26182016085958494587/25000000000000000000 : ℝ)^1024 ≤ (5057334541690131/5000000000000000 : ℝ)^4185 := by
      have hnat : (26182016085958494587 : ℕ)^1024*5000000000000000^4185 ≤ 5057334541690131^4185*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26182016085958494587 25000000000000000000 5057334541690131 5000000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5057334541690131/5000000000000000 : ℝ)) (X := (26182016085958494587/25000000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(57334541690131/4000000000000000 : ℝ)*(0 : ℝ))^(4185/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(57334541690131/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1182016085958494587/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(57334541690131/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4185/1024 : ℝ) := by
    rw [show (1 : ℝ)+(57334541690131/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10057334541690131/10000000000000000 : ℝ) by norm_num, show 1+(1182016085958494587/50000000000000000000 : ℝ)+(0 : ℝ)=(51182016085958494587/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1182016085958494587/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(57334541690131/4000000000000000 : ℝ)*(2/5 : ℝ))^(4185/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(57334541690131/4000000000000000 : ℝ)*(2/5 : ℝ)=(5057334541690131/5000000000000000 : ℝ) by norm_num, show 1+2*(1182016085958494587/50000000000000000000 : ℝ)=(26182016085958494587/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(57334541690131/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57334541690131/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(57334541690131/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57334541690131/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(57334541690131/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57334541690131/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-940234483/5000000000 : ℝ)*X 0 0+(6046046897/10000000000 : ℝ)*X 0 1+(4785008439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2757382711/5000000000 : ℝ)*X 1 0+(-1301572673/5000000000 : ℝ)*X 1 1+(957001687/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1378691341/2500000000 : ℝ)*X 2 0+(4785008453/10000000000 : ℝ)*X 2 1+(-1301572699/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((524761857/1250000000 : ℝ)*X 0 0+(3119469269/10000000000 : ℝ)*X 0 1+(705750019/1250000000 : ℝ)*X 0 2+(524761857/1250000000 : ℝ)*X 1 0+(3119469269/10000000000 : ℝ)*X 1 1+(705750019/1250000000 : ℝ)*X 1 2+(524761857/1250000000 : ℝ)*X 2 0+(3119469269/10000000000 : ℝ)*X 2 1+(705750019/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-235688681/1250000000 : ℝ)*X 0 0+(2408760347/5000000000 : ℝ)*X 0 1+(3006194493/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1292985381/2500000000 : ℝ)*X 1 0+(-275153/2000000 : ℝ)*X 1 1+(6012388719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1292985369/2500000000 : ℝ)*X 2 0+(1503097213/2500000000 : ℝ)*X 2 1+(-1375764859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1052048447/2500000000 : ℝ)*X 0 0+(5450059/9765625 : ℝ)*X 0 1+(3186904307/10000000000 : ℝ)*X 0 2+(1052048447/2500000000 : ℝ)*X 1 0+(5450059/9765625 : ℝ)*X 1 1+(3186904307/10000000000 : ℝ)*X 1 2+(1052048447/2500000000 : ℝ)*X 2 0+(5450059/9765625 : ℝ)*X 2 1+(3186904307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (156040199520639929441793/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14658329/50000000000000 : ℝ)*(base1) + (76559701/10000000000000 : ℝ)*(base19) + (354295717/50000000000000 : ℝ)*(base23) + (24332707/50000000000000 : ℝ)*(base24) + (177579139/100000000000000 : ℝ)*(upper3) + (297200853849801/50000000000000 : ℝ)*(major0) + (297200853849801/50000000000000 : ℝ)*(major1) + (297200853849801/50000000000000 : ℝ)*(major2) + (792999826445057/100000000000000 : ℝ)*(sp0) + (396500360384791/50000000000000 : ℝ)*(sp1) + (49562545569359/6250000000000 : ℝ)*(sp2) + (24737527298099/6250000000000 : ℝ)*(sp3) + (1689238193/100000000000000 : ℝ)*(sp4) + (84932473/6250000000000 : ℝ)*(sp7) + (39580182500581/10000000000000 : ℝ)*(f.failure) + (6195324112239/781250000000 : ℝ)*(f.sum) + (22290938186069/100000000000000000000000000000 : ℝ)*base66 + (412143132986069/200000000000000000000000000000 : ℝ)*base68 + (297722334986069/200000000000000000000000000000 : ℝ)*base70 + (1322234860386069/200000000000000000000000000000 : ℝ)*base72 + (187817656813931/100000000000000000000000000000 : ℝ)*base73 + (322291504786069/200000000000000000000000000000 : ℝ)*base76 + (266857502786069/200000000000000000000000000000 : ℝ)*base78 + (595375525186069/200000000000000000000000000000 : ℝ)*base80 + (240924754813931/100000000000000000000000000000 : ℝ)*base81 + (650569/250000000000000000000 : ℝ)*base89 + (650569/250000000000000000000 : ℝ)*base91 + (650569/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (199938744432286989921549/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (89907563/100000000000000 : ℝ)*(base1) + (399510319/20000000000000 : ℝ)*(base19) + (497988911/25000000000000 : ℝ)*(base23) + (108619459/50000000000000 : ℝ)*(upper3) + (11852687/5000000000000 : ℝ)*(upper5) + (313657816299907/50000000000000 : ℝ)*(major0) + (313657816299907/50000000000000 : ℝ)*(major1) + (313657816299907/50000000000000 : ℝ)*(major2) + (64021713/1562500000000 : ℝ)*(sp1) + (4130146409/100000000000000 : ℝ)*(sp2) + (83691244972723/10000000000000 : ℝ)*(sp4) + (20922656621961/2500000000000 : ℝ)*(sp5) + (418453118858807/50000000000000 : ℝ)*(sp6) + (208859274443701/50000000000000 : ℝ)*(sp7) + (83543727758993/20000000000000 : ℝ)*(f.failure) + (836912359819667/100000000000000 : ℝ)*(f.sum) + (246609584517817/100000000000000000000000000000 : ℝ)*base65 + (700026812282183/200000000000000000000000000000 : ℝ)*base68 + (898982719317817/200000000000000000000000000000 : ℝ)*base69 + (654387350117817/200000000000000000000000000000 : ℝ)*base71 + (31925902117817/100000000000000000000000000000 : ℝ)*base73 + (337467619317817/200000000000000000000000000000 : ℝ)*base75 + (982129574917817/200000000000000000000000000000 : ℝ)*base77 + (370014169282183/200000000000000000000000000000 : ℝ)*base80 + (455534737517817/100000000000000000000000000000 : ℝ)*base81 + (718043/500000000000000000000 : ℝ)*base90 + (718043/500000000000000000000 : ℝ)*base92 + (718043/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1178_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (561/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13839/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1178_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1178_s1_0 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-416504443/2000000000 : ℝ)*x 0 + (1423000277/2500000000 : ℝ)*x 1 + (626213907/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416504443/2000000000 : ℝ)^8371 ≤ (2505606960731/20000000000000 : ℝ)^6323 := by
    have hnat : (416504443 : ℕ)^8371*20000000000000^6323 ≤ 2505606960731^6323*2000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416504443 2000000000 2505606960731 20000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1423000277/2500000000 : ℝ)^8371 ≤ (11855942185313/25000000000000 : ℝ)^6323 := by
    have hnat : (1423000277 : ℕ)^8371*25000000000000^6323 ≤ 11855942185313^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1423000277 2500000000 11855942185313 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (626213907/1250000000 : ℝ)^8371 ≤ (20024098217521/50000000000000 : ℝ)^6323 := by
    have hnat : (626213907 : ℕ)^8371*50000000000000^6323 ≤ 20024098217521^6323*1250000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626213907 1250000000 20024098217521 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-416504443/2000000000 : ℝ), (1423000277/2500000000 : ℝ), (626213907/1250000000 : ℝ)] ![(2505606960731/20000000000000 : ℝ), (11855942185313/25000000000000 : ℝ), (20024098217521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-416504443/2000000000 : ℝ)|^8371 ≤ (2505606960731/20000000000000 : ℝ)^6323
        have hw : |(-416504443/2000000000 : ℝ)|=(416504443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1423000277/2500000000 : ℝ)|^8371 ≤ (11855942185313/25000000000000 : ℝ)^6323
        have hw : |(1423000277/2500000000 : ℝ)|=(1423000277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(626213907/1250000000 : ℝ)|^8371 ≤ (20024098217521/50000000000000 : ℝ)^6323
        have hw : |(626213907/1250000000 : ℝ)|=(626213907/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s1_1 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2708575403/5000000000 : ℝ)*x 0 + (-2450055723/10000000000 : ℝ)*x 1 + (2504855157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2708575403/5000000000 : ℝ)^8371 ≤ (11104018251539/25000000000000 : ℝ)^6323 := by
    have hnat : (2708575403 : ℕ)^8371*25000000000000^6323 ≤ 11104018251539^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708575403 5000000000 11104018251539 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2450055723/10000000000 : ℝ)^8371 ≤ (15535740521559/100000000000000 : ℝ)^6323 := by
    have hnat : (2450055723 : ℕ)^8371*100000000000000^6323 ≤ 15535740521559^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2450055723 10000000000 15535740521559 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2504855157/5000000000 : ℝ)^8371 ≤ (20024093232749/50000000000000 : ℝ)^6323 := by
    have hnat : (2504855157 : ℕ)^8371*50000000000000^6323 ≤ 20024093232749^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2504855157 5000000000 20024093232749 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2708575403/5000000000 : ℝ), (-2450055723/10000000000 : ℝ), (2504855157/5000000000 : ℝ)] ![(11104018251539/25000000000000 : ℝ), (15535740521559/100000000000000 : ℝ), (20024093232749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2708575403/5000000000 : ℝ)|^8371 ≤ (11104018251539/25000000000000 : ℝ)^6323
        have hw : |(2708575403/5000000000 : ℝ)|=(2708575403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2450055723/10000000000 : ℝ)|^8371 ≤ (15535740521559/100000000000000 : ℝ)^6323
        have hw : |(-2450055723/10000000000 : ℝ)|=(2450055723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2504855157/5000000000 : ℝ)|^8371 ≤ (20024093232749/50000000000000 : ℝ)^6323
        have hw : |(2504855157/5000000000 : ℝ)|=(2504855157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s1_2 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5417152897/10000000000 : ℝ)*x 0 + (5009708327/10000000000 : ℝ)*x 1 + (-612513881/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417152897/10000000000 : ℝ)^8371 ≤ (22208047851813/50000000000000 : ℝ)^6323 := by
    have hnat : (5417152897 : ℕ)^8371*50000000000000^6323 ≤ 22208047851813^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417152897 10000000000 22208047851813 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5009708327/10000000000 : ℝ)^8371 ≤ (20024082718161/50000000000000 : ℝ)^6323 := by
    have hnat : (5009708327 : ℕ)^8371*50000000000000^6323 ≤ 20024082718161^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5009708327 10000000000 20024082718161 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (612513881/2500000000 : ℝ)^8371 ≤ (3107147770199/20000000000000 : ℝ)^6323 := by
    have hnat : (612513881 : ℕ)^8371*20000000000000^6323 ≤ 3107147770199^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612513881 2500000000 3107147770199 20000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417152897/10000000000 : ℝ), (5009708327/10000000000 : ℝ), (-612513881/2500000000 : ℝ)] ![(22208047851813/50000000000000 : ℝ), (20024082718161/50000000000000 : ℝ), (3107147770199/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417152897/10000000000 : ℝ)|^8371 ≤ (22208047851813/50000000000000 : ℝ)^6323
        have hw : |(5417152897/10000000000 : ℝ)|=(5417152897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5009708327/10000000000 : ℝ)|^8371 ≤ (20024082718161/50000000000000 : ℝ)^6323
        have hw : |(5009708327/10000000000 : ℝ)|=(5009708327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-612513881/2500000000 : ℝ)|^8371 ≤ (3107147770199/20000000000000 : ℝ)^6323
        have hw : |(-612513881/2500000000 : ℝ)|=(612513881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s1_3 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4314374493/10000000000 : ℝ)*x 0 + (1841871929/5000000000 : ℝ)*x 1 + (1010145497/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314374493/10000000000 : ℝ)^8371 ≤ (32860098840839/100000000000000 : ℝ)^6323 := by
    have hnat : (4314374493 : ℕ)^8371*100000000000000^6323 ≤ 32860098840839^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314374493 10000000000 32860098840839 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1841871929/5000000000 : ℝ)^8371 ≤ (1066281592729/4000000000000 : ℝ)^6323 := by
    have hnat : (1841871929 : ℕ)^8371*4000000000000^6323 ≤ 1066281592729^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1841871929 5000000000 1066281592729 4000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1010145497/2000000000 : ℝ)^8371 ≤ (40482861324169/100000000000000 : ℝ)^6323 := by
    have hnat : (1010145497 : ℕ)^8371*100000000000000^6323 ≤ 40482861324169^6323*2000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010145497 2000000000 40482861324169 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314374493/10000000000 : ℝ), (1841871929/5000000000 : ℝ), (1010145497/2000000000 : ℝ)] ![(32860098840839/100000000000000 : ℝ), (1066281592729/4000000000000 : ℝ), (40482861324169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314374493/10000000000 : ℝ)|^8371 ≤ (32860098840839/100000000000000 : ℝ)^6323
        have hw : |(4314374493/10000000000 : ℝ)|=(4314374493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1841871929/5000000000 : ℝ)|^8371 ≤ (1066281592729/4000000000000 : ℝ)^6323
        have hw : |(1841871929/5000000000 : ℝ)|=(1841871929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1010145497/2000000000 : ℝ)|^8371 ≤ (40482861324169/100000000000000 : ℝ)^6323
        have hw : |(1010145497/2000000000 : ℝ)|=(1010145497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s1_4 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1041641467/5000000000 : ℝ)*x 0 + (5018899843/10000000000 : ℝ)*x 1 + (5682630357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041641467/5000000000 : ℝ)^8371 ≤ (6267046877193/50000000000000 : ℝ)^6323 := by
    have hnat : (1041641467 : ℕ)^8371*50000000000000^6323 ≤ 6267046877193^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041641467 5000000000 6267046877193 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5018899843/10000000000 : ℝ)^8371 ≤ (5018183953161/12500000000000 : ℝ)^6323 := by
    have hnat : (5018899843 : ℕ)^8371*12500000000000^6323 ≤ 5018183953161^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5018899843 10000000000 5018183953161 12500000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5682630357/10000000000 : ℝ)^8371 ≤ (4732043460873/10000000000000 : ℝ)^6323 := by
    have hnat : (5682630357 : ℕ)^8371*10000000000000^6323 ≤ 4732043460873^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5682630357 10000000000 4732043460873 10000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1041641467/5000000000 : ℝ), (5018899843/10000000000 : ℝ), (5682630357/10000000000 : ℝ)] ![(6267046877193/50000000000000 : ℝ), (5018183953161/12500000000000 : ℝ), (4732043460873/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1041641467/5000000000 : ℝ)|^8371 ≤ (6267046877193/50000000000000 : ℝ)^6323
        have hw : |(-1041641467/5000000000 : ℝ)|=(1041641467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5018899843/10000000000 : ℝ)|^8371 ≤ (5018183953161/12500000000000 : ℝ)^6323
        have hw : |(5018899843/10000000000 : ℝ)|=(5018899843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5682630357/10000000000 : ℝ)|^8371 ≤ (4732043460873/10000000000000 : ℝ)^6323
        have hw : |(5682630357/10000000000 : ℝ)|=(5682630357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s1_5 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5241911309/10000000000 : ℝ)*x 0 + (-888566717/5000000000 : ℝ)*x 1 + (5682632533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5241911309/10000000000 : ℝ)^8371 ≤ (21261957736211/50000000000000 : ℝ)^6323 := by
    have hnat : (5241911309 : ℕ)^8371*50000000000000^6323 ≤ 21261957736211^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241911309 10000000000 21261957736211 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (888566717/5000000000 : ℝ)^8371 ≤ (10155625917557/100000000000000 : ℝ)^6323 := by
    have hnat : (888566717 : ℕ)^8371*100000000000000^6323 ≤ 10155625917557^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888566717 5000000000 10155625917557 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5682632533/10000000000 : ℝ)^8371 ≤ (2957528662359/6250000000000 : ℝ)^6323 := by
    have hnat : (5682632533 : ℕ)^8371*6250000000000^6323 ≤ 2957528662359^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5682632533 10000000000 2957528662359 6250000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5241911309/10000000000 : ℝ), (-888566717/5000000000 : ℝ), (5682632533/10000000000 : ℝ)] ![(21261957736211/50000000000000 : ℝ), (10155625917557/100000000000000 : ℝ), (2957528662359/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5241911309/10000000000 : ℝ)|^8371 ≤ (21261957736211/50000000000000 : ℝ)^6323
        have hw : |(5241911309/10000000000 : ℝ)|=(5241911309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-888566717/5000000000 : ℝ)|^8371 ≤ (10155625917557/100000000000000 : ℝ)^6323
        have hw : |(-888566717/5000000000 : ℝ)|=(888566717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5682632533/10000000000 : ℝ)|^8371 ≤ (2957528662359/6250000000000 : ℝ)^6323
        have hw : |(5682632533/10000000000 : ℝ)|=(5682632533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s1_6 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2620955421/5000000000 : ℝ)*x 0 + (5682633563/10000000000 : ℝ)*x 1 + (-355426519/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2620955421/5000000000 : ℝ)^8371 ≤ (21261955228459/50000000000000 : ℝ)^6323 := by
    have hnat : (2620955421 : ℕ)^8371*50000000000000^6323 ≤ 21261955228459^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620955421 5000000000 21261955228459 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5682633563/10000000000 : ℝ)^8371 ≤ (47320469952839/100000000000000 : ℝ)^6323 := by
    have hnat : (5682633563 : ℕ)^8371*100000000000000^6323 ≤ 47320469952839^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5682633563 10000000000 47320469952839 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (355426519/2000000000 : ℝ)^8371 ≤ (1269452446257/12500000000000 : ℝ)^6323 := by
    have hnat : (355426519 : ℕ)^8371*12500000000000^6323 ≤ 1269452446257^6323*2000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355426519 2000000000 1269452446257 12500000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2620955421/5000000000 : ℝ), (5682633563/10000000000 : ℝ), (-355426519/2000000000 : ℝ)] ![(21261955228459/50000000000000 : ℝ), (47320469952839/100000000000000 : ℝ), (1269452446257/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2620955421/5000000000 : ℝ)|^8371 ≤ (21261955228459/50000000000000 : ℝ)^6323
        have hw : |(2620955421/5000000000 : ℝ)|=(2620955421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5682633563/10000000000 : ℝ)|^8371 ≤ (47320469952839/100000000000000 : ℝ)^6323
        have hw : |(5682633563/10000000000 : ℝ)|=(5682633563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-355426519/2000000000 : ℝ)|^8371 ≤ (1269452446257/12500000000000 : ℝ)^6323
        have hw : |(-355426519/2000000000 : ℝ)|=(355426519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s1_7 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4315887361/10000000000 : ℝ)*x 0 + (5032321387/10000000000 : ℝ)*x 1 + (3702511091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315887361/10000000000 : ℝ)^8371 ≤ (2054709656043/6250000000000 : ℝ)^6323 := by
    have hnat : (4315887361 : ℕ)^8371*6250000000000^6323 ≤ 2054709656043^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315887361 10000000000 2054709656043 6250000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5032321387/10000000000 : ℝ)^8371 ≤ (5035957848537/12500000000000 : ℝ)^6323 := by
    have hnat : (5032321387 : ℕ)^8371*12500000000000^6323 ≤ 5035957848537^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5032321387 10000000000 5035957848537 12500000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3702511091/10000000000 : ℝ)^8371 ≤ (26836982697243/100000000000000 : ℝ)^6323 := by
    have hnat : (3702511091 : ℕ)^8371*100000000000000^6323 ≤ 26836982697243^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3702511091 10000000000 26836982697243 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315887361/10000000000 : ℝ), (5032321387/10000000000 : ℝ), (3702511091/10000000000 : ℝ)] ![(2054709656043/6250000000000 : ℝ), (5035957848537/12500000000000 : ℝ), (26836982697243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315887361/10000000000 : ℝ)|^8371 ≤ (2054709656043/6250000000000 : ℝ)^6323
        have hw : |(4315887361/10000000000 : ℝ)|=(4315887361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5032321387/10000000000 : ℝ)|^8371 ≤ (5035957848537/12500000000000 : ℝ)^6323
        have hw : |(5032321387/10000000000 : ℝ)|=(5032321387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3702511091/10000000000 : ℝ)|^8371 ≤ (26836982697243/100000000000000 : ℝ)^6323
        have hw : |(3702511091/10000000000 : ℝ)|=(3702511091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1178_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13839/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (561/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5849/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5069/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13839/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (561/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13839/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (561/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13839/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (561/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13839/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (561/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13839/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (561/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13839/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (561/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (561/100000 : ℝ) ^ (4185/1024 : ℝ) ≤ (63125475493/100000000000000000000 : ℝ) := by
    have hpowers : (561/100000 : ℝ)^4185 ≤ (63125475493/100000000000000000000 : ℝ)^1024 := by
      have hnat : (561 : ℕ)^4185*100000000000000000000^1024 ≤ 63125475493^1024*100000^4185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        561 100000 63125475493 100000000000000000000 4185 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (561/100000 : ℝ)) (X := (63125475493/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13839/50000 : ℝ) ^ (4185/1024 : ℝ) ≤ (524870882667803141/100000000000000000000 : ℝ) := by
    have hpowers : (13839/50000 : ℝ)^4185 ≤ (524870882667803141/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13839 : ℕ)^4185*100000000000000000000^1024 ≤ 524870882667803141^1024*50000^4185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13839 50000 524870882667803141 100000000000000000000 4185 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13839/50000 : ℝ)) (X := (524870882667803141/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000063125475493/50000000000000000000 : ℝ) ≤ (39062500012067/39062500000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (50000000063125475493/50000000000000000000 : ℝ)^1024 ≤ (39062500012067/39062500000000 : ℝ)^4185 := by
      have hnat : (50000000063125475493 : ℕ)^1024*39062500000000^4185 ≤ 39062500012067^4185*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000063125475493 50000000000000000000 39062500012067 39062500000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39062500012067/39062500000000 : ℝ)) (X := (50000000063125475493/50000000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50262435472896639317/50000000000000000000 : ℝ) ≤ (10012817341211833/10000000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (50262435472896639317/50000000000000000000 : ℝ)^1024 ≤ (10012817341211833/10000000000000000 : ℝ)^4185 := by
      have hnat : (50262435472896639317 : ℕ)^1024*10000000000000000^4185 ≤ 10012817341211833^4185*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50262435472896639317 50000000000000000000 10012817341211833 10000000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012817341211833/10000000000000000 : ℝ)) (X := (50262435472896639317/50000000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50524870882667803141/50000000000000000000 : ℝ) ≤ (5012817339667257/5000000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (50524870882667803141/50000000000000000000 : ℝ)^1024 ≤ (5012817339667257/5000000000000000 : ℝ)^4185 := by
      have hnat : (50524870882667803141 : ℕ)^1024*5000000000000000^4185 ≤ 5012817339667257^4185*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50524870882667803141 50000000000000000000 5012817339667257 5000000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012817339667257/5000000000000000 : ℝ)) (X := (50524870882667803141/50000000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(63125475493/100000000000000000000 : ℝ) ≤ ((45192603171732481117/45195000000000000000 : ℝ)+2*(12817338122681/2711700000000000 : ℝ)*(561/100000 : ℝ))^(4185/1024 : ℝ) := by
    rw [show (45192603171732481117/45195000000000000000 : ℝ)+2*(12817338122681/2711700000000000 : ℝ)*(561/100000 : ℝ)=(39062500012067/39062500000000 : ℝ) by norm_num, show 1+2*(63125475493/100000000000000000000 : ℝ)=(50000000063125475493/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(524870882667803141/100000000000000000000 : ℝ)+(63125475493/100000000000000000000 : ℝ) ≤ ((45192603171732481117/45195000000000000000 : ℝ)+(12817338122681/2711700000000000 : ℝ)*((13839/50000 : ℝ)+(561/100000 : ℝ)))^(4185/1024 : ℝ) := by
    rw [show (45192603171732481117/45195000000000000000 : ℝ)+(12817338122681/2711700000000000 : ℝ)*((13839/50000 : ℝ)+(561/100000 : ℝ))=(10012817341211833/10000000000000000 : ℝ) by norm_num, show 1+(524870882667803141/100000000000000000000 : ℝ)+(63125475493/100000000000000000000 : ℝ)=(50262435472896639317/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(524870882667803141/100000000000000000000 : ℝ) ≤ ((45192603171732481117/45195000000000000000 : ℝ)+2*(12817338122681/2711700000000000 : ℝ)*(13839/50000 : ℝ))^(4185/1024 : ℝ) := by
    rw [show (45192603171732481117/45195000000000000000 : ℝ)+2*(12817338122681/2711700000000000 : ℝ)*(13839/50000 : ℝ)=(5012817339667257/5000000000000000 : ℝ) by norm_num, show 1+2*(524870882667803141/100000000000000000000 : ℝ)=(50524870882667803141/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (45192603171732481117/45195000000000000000 : ℝ)*(X 1 0+X 2 0)+(12817338122681/2711700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (561/100000 : ℝ)) (hi := (13839/50000 : ℝ)) (c := (45192603171732481117/45195000000000000000 : ℝ)) (alpha := (12817338122681/2711700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (45192603171732481117/45195000000000000000 : ℝ)*(X 0 1+X 2 1)+(12817338122681/2711700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (561/100000 : ℝ)) (hi := (13839/50000 : ℝ)) (c := (45192603171732481117/45195000000000000000 : ℝ)) (alpha := (12817338122681/2711700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (45192603171732481117/45195000000000000000 : ℝ)*(X 0 2+X 1 2)+(12817338122681/2711700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (561/100000 : ℝ)) (hi := (13839/50000 : ℝ)) (c := (45192603171732481117/45195000000000000000 : ℝ)) (alpha := (12817338122681/2711700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-416504443/2000000000 : ℝ)*X 0 0+(1423000277/2500000000 : ℝ)*X 0 1+(626213907/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2708575403/5000000000 : ℝ)*X 1 0+(-2450055723/10000000000 : ℝ)*X 1 1+(2504855157/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5417152897/10000000000 : ℝ)*X 2 0+(5009708327/10000000000 : ℝ)*X 2 1+(-612513881/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4314374493/10000000000 : ℝ)*X 0 0+(1841871929/5000000000 : ℝ)*X 0 1+(1010145497/2000000000 : ℝ)*X 0 2+(4314374493/10000000000 : ℝ)*X 1 0+(1841871929/5000000000 : ℝ)*X 1 1+(1010145497/2000000000 : ℝ)*X 1 2+(4314374493/10000000000 : ℝ)*X 2 0+(1841871929/5000000000 : ℝ)*X 2 1+(1010145497/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1041641467/5000000000 : ℝ)*X 0 0+(5018899843/10000000000 : ℝ)*X 0 1+(5682630357/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5241911309/10000000000 : ℝ)*X 1 0+(-888566717/5000000000 : ℝ)*X 1 1+(5682632533/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2620955421/5000000000 : ℝ)*X 2 0+(5682633563/10000000000 : ℝ)*X 2 1+(-355426519/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4315887361/10000000000 : ℝ)*X 0 0+(5032321387/10000000000 : ℝ)*X 0 1+(3702511091/10000000000 : ℝ)*X 0 2+(4315887361/10000000000 : ℝ)*X 1 0+(5032321387/10000000000 : ℝ)*X 1 1+(3702511091/10000000000 : ℝ)*X 1 2+(4315887361/10000000000 : ℝ)*X 2 0+(5032321387/10000000000 : ℝ)*X 2 1+(3702511091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (219625273492545617309/753250000000000000000000000 : ℝ) := by norm_num
    linear_combination (22004709/50000000000000 : ℝ)*(base1) + (380655159/50000000000000 : ℝ)*(base19) + (309073911/50000000000000 : ℝ)*(base23) + (106577727/25000000000000 : ℝ)*(lower2) + (22508883/25000000000000 : ℝ)*(lower4) + (219719293781123/20000000000000 : ℝ)*(major0) + (219719293781123/20000000000000 : ℝ)*(major1) + (219719293781123/20000000000000 : ℝ)*(major2) + (1465653302429473/100000000000000 : ℝ)*(sp0) + (366413940882321/25000000000000 : ℝ)*(sp1) + (1465653182085673/100000000000000 : ℝ)*(sp2) + (457210224527/62500000000 : ℝ)*(sp3) + (1633209773/50000000000000 : ℝ)*(sp4) + (1362303053/50000000000000 : ℝ)*(sp6) + (365768201626309/50000000000000 : ℝ)*(f.failure) + (1465656524839601/100000000000000 : ℝ)*(f.sum) + (48449333595833/13558500000000000000000000000 : ℝ)*base65 + (6979195143868413173/2711700000000000000000000000000000 : ℝ)*base67 + (3189964714793186827/2711700000000000000000000000000000 : ℝ)*base70 + (8267195855772986827/2711700000000000000000000000000000 : ℝ)*base72 + (37747098842407/27117000000000000000000000000 : ℝ)*base73 + (17463890264235386827/2711700000000000000000000000000000 : ℝ)*base76 + (10742517972487713173/2711700000000000000000000000000000 : ℝ)*base77 + (3816139764540513173/2711700000000000000000000000000000 : ℝ)*base79 + (11447784589237/27117000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (83959/1250000000000000000000 : ℝ)*base90 + (83959/1250000000000000000000 : ℝ)*base92 + (83959/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (666411469325467732020796953/376625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (155053481/10000000000000 : ℝ)*(base19) + (2124189259/100000000000000 : ℝ)*(base23) + (69078503/25000000000000 : ℝ)*(upper2) + (416297957/100000000000000 : ℝ)*(upper3) + (88588599/50000000000000 : ℝ)*(upper5) + (1129309587244291/100000000000000 : ℝ)*(major0) + (1129309587244291/100000000000000 : ℝ)*(major1) + (1129309587244291/100000000000000 : ℝ)*(major2) + (8633507247/100000000000000 : ℝ)*(sp1) + (1755024607/12500000000000 : ℝ)*(sp2) + (301326275504381/20000000000000 : ℝ)*(sp4) + (188327649184981/12500000000000 : ℝ)*(sp5) + (150661521313579/10000000000000 : ℝ)*(sp6) + (375993868992839/50000000000000 : ℝ)*(sp7) + (375993868992839/50000000000000 : ℝ)*(f.failure) + (301326275504381/20000000000000 : ℝ)*(f.sum) + (832323094288691/135585000000000000000000000000 : ℝ)*base65 + (130193321209229290859/13558500000000000000000000000000000 : ℝ)*base68 + (55276539327573709141/13558500000000000000000000000000000 : ℝ)*base69 + (51050584165367209141/13558500000000000000000000000000000 : ℝ)*base71 + (96159004081517/67792500000000000000000000000 : ℝ)*base74 + (79290399236339209141/13558500000000000000000000000000000 : ℝ)*base75 + (86814722300834209141/13558500000000000000000000000000000 : ℝ)*base77 + (29534231778401209141/13558500000000000000000000000000000 : ℝ)*base79 + (323567415268331/135585000000000000000000000000 : ℝ)*base81 + (10150989/1250000000000000000000 : ℝ)*base90 + (10150989/1250000000000000000000 : ℝ)*base92 + (10150989/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1178_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13839/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (561/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5849/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5069/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1178_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1178_s2_0 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2133848593/10000000000 : ℝ)*x 0 + (5504090021/10000000000 : ℝ)*x 1 + (161404689/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133848593/10000000000 : ℝ)^8371 ≤ (12938435979761/100000000000000 : ℝ)^6323 := by
    have hnat : (2133848593 : ℕ)^8371*100000000000000^6323 ≤ 12938435979761^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133848593 10000000000 12938435979761 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5504090021/10000000000 : ℝ)^8371 ≤ (22681114090241/50000000000000 : ℝ)^6323 := by
    have hnat : (5504090021 : ℕ)^8371*50000000000000^6323 ≤ 22681114090241^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504090021 10000000000 22681114090241 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161404689/312500000 : ℝ)^8371 ≤ (8339867165591/20000000000000 : ℝ)^6323 := by
    have hnat : (161404689 : ℕ)^8371*20000000000000^6323 ≤ 8339867165591^6323*312500000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161404689 312500000 8339867165591 20000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2133848593/10000000000 : ℝ), (5504090021/10000000000 : ℝ), (161404689/312500000 : ℝ)] ![(12938435979761/100000000000000 : ℝ), (22681114090241/50000000000000 : ℝ), (8339867165591/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2133848593/10000000000 : ℝ)|^8371 ≤ (12938435979761/100000000000000 : ℝ)^6323
        have hw : |(-2133848593/10000000000 : ℝ)|=(2133848593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5504090021/10000000000 : ℝ)|^8371 ≤ (22681114090241/50000000000000 : ℝ)^6323
        have hw : |(5504090021/10000000000 : ℝ)|=(5504090021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161404689/312500000 : ℝ)|^8371 ≤ (8339867165591/20000000000000 : ℝ)^6323
        have hw : |(161404689/312500000 : ℝ)|=(161404689/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s2_1 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5372331903/10000000000 : ℝ)*x 0 + (-2309924151/10000000000 : ℝ)*x 1 + (5164953341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372331903/10000000000 : ℝ)^8371 ≤ (43930224098753/100000000000000 : ℝ)^6323 := by
    have hnat : (5372331903 : ℕ)^8371*100000000000000^6323 ≤ 43930224098753^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372331903 10000000000 43930224098753 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2309924151/10000000000 : ℝ)^8371 ≤ (14370404858591/100000000000000 : ℝ)^6323 := by
    have hnat : (2309924151 : ℕ)^8371*100000000000000^6323 ≤ 14370404858591^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2309924151 10000000000 14370404858591 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5164953341/10000000000 : ℝ)^8371 ≤ (41699371025223/100000000000000 : ℝ)^6323 := by
    have hnat : (5164953341 : ℕ)^8371*100000000000000^6323 ≤ 41699371025223^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5164953341 10000000000 41699371025223 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372331903/10000000000 : ℝ), (-2309924151/10000000000 : ℝ), (5164953341/10000000000 : ℝ)] ![(43930224098753/100000000000000 : ℝ), (14370404858591/100000000000000 : ℝ), (41699371025223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372331903/10000000000 : ℝ)|^8371 ≤ (43930224098753/100000000000000 : ℝ)^6323
        have hw : |(5372331903/10000000000 : ℝ)|=(5372331903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2309924151/10000000000 : ℝ)|^8371 ≤ (14370404858591/100000000000000 : ℝ)^6323
        have hw : |(-2309924151/10000000000 : ℝ)|=(2309924151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5164953341/10000000000 : ℝ)|^8371 ≤ (41699371025223/100000000000000 : ℝ)^6323
        have hw : |(5164953341/10000000000 : ℝ)|=(5164953341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s2_2 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5372332893/10000000000 : ℝ)*x 0 + (5164951869/10000000000 : ℝ)*x 1 + (-57748119/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372332893/10000000000 : ℝ)^8371 ≤ (8786046963233/20000000000000 : ℝ)^6323 := by
    have hnat : (5372332893 : ℕ)^8371*20000000000000^6323 ≤ 8786046963233^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372332893 10000000000 8786046963233 20000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5164951869/10000000000 : ℝ)^8371 ≤ (41699355291733/100000000000000 : ℝ)^6323 := by
    have hnat : (5164951869 : ℕ)^8371*100000000000000^6323 ≤ 41699355291733^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5164951869 10000000000 41699355291733 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57748119/250000000 : ℝ)^8371 ≤ (718520493721/5000000000000 : ℝ)^6323 := by
    have hnat : (57748119 : ℕ)^8371*5000000000000^6323 ≤ 718520493721^6323*250000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57748119 250000000 718520493721 5000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372332893/10000000000 : ℝ), (5164951869/10000000000 : ℝ), (-57748119/250000000 : ℝ)] ![(8786046963233/20000000000000 : ℝ), (41699355291733/100000000000000 : ℝ), (718520493721/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372332893/10000000000 : ℝ)|^8371 ≤ (8786046963233/20000000000000 : ℝ)^6323
        have hw : |(5372332893/10000000000 : ℝ)|=(5372332893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5164951869/10000000000 : ℝ)|^8371 ≤ (41699355291733/100000000000000 : ℝ)^6323
        have hw : |(5164951869/10000000000 : ℝ)|=(5164951869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-57748119/250000000 : ℝ)|^8371 ≤ (718520493721/5000000000000 : ℝ)^6323
        have hw : |(-57748119/250000000 : ℝ)|=(57748119/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s2_3 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087417769/2500000000 : ℝ)*x 0 + (4022974621/10000000000 : ℝ)*x 1 + (2351223911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087417769/2500000000 : ℝ)^8371 ≤ (8304119402027/25000000000000 : ℝ)^6323 := by
    have hnat : (1087417769 : ℕ)^8371*25000000000000^6323 ≤ 8304119402027^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087417769 2500000000 8304119402027 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4022974621/10000000000 : ℝ)^8371 ≤ (14977226490577/50000000000000 : ℝ)^6323 := by
    have hnat : (4022974621 : ℕ)^8371*50000000000000^6323 ≤ 14977226490577^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022974621 10000000000 14977226490577 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2351223911/5000000000 : ℝ)^8371 ≤ (7365813878513/20000000000000 : ℝ)^6323 := by
    have hnat : (2351223911 : ℕ)^8371*20000000000000^6323 ≤ 7365813878513^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2351223911 5000000000 7365813878513 20000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087417769/2500000000 : ℝ), (4022974621/10000000000 : ℝ), (2351223911/5000000000 : ℝ)] ![(8304119402027/25000000000000 : ℝ), (14977226490577/50000000000000 : ℝ), (7365813878513/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087417769/2500000000 : ℝ)|^8371 ≤ (8304119402027/25000000000000 : ℝ)^6323
        have hw : |(1087417769/2500000000 : ℝ)|=(1087417769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4022974621/10000000000 : ℝ)|^8371 ≤ (14977226490577/50000000000000 : ℝ)^6323
        have hw : |(4022974621/10000000000 : ℝ)|=(4022974621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2351223911/5000000000 : ℝ)|^8371 ≤ (7365813878513/20000000000000 : ℝ)^6323
        have hw : |(2351223911/5000000000 : ℝ)|=(2351223911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s2_4 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2133940881/10000000000 : ℝ)*x 0 + (1291807789/2500000000 : ℝ)*x 1 + (2750893603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133940881/10000000000 : ℝ)^8371 ≤ (3234794203317/25000000000000 : ℝ)^6323 := by
    have hnat : (2133940881 : ℕ)^8371*25000000000000^6323 ≤ 3234794203317^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133940881 10000000000 3234794203317 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1291807789/2500000000 : ℝ)^8371 ≤ (2607732451099/6250000000000 : ℝ)^6323 := by
    have hnat : (1291807789 : ℕ)^8371*6250000000000^6323 ≤ 2607732451099^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291807789 2500000000 2607732451099 6250000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2750893603/5000000000 : ℝ)^8371 ≤ (11334275989503/25000000000000 : ℝ)^6323 := by
    have hnat : (2750893603 : ℕ)^8371*25000000000000^6323 ≤ 11334275989503^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750893603 5000000000 11334275989503 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2133940881/10000000000 : ℝ), (1291807789/2500000000 : ℝ), (2750893603/5000000000 : ℝ)] ![(3234794203317/25000000000000 : ℝ), (2607732451099/6250000000000 : ℝ), (11334275989503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2133940881/10000000000 : ℝ)|^8371 ≤ (3234794203317/25000000000000 : ℝ)^6323
        have hw : |(-2133940881/10000000000 : ℝ)|=(2133940881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1291807789/2500000000 : ℝ)|^8371 ≤ (2607732451099/6250000000000 : ℝ)^6323
        have hw : |(1291807789/2500000000 : ℝ)|=(1291807789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2750893603/5000000000 : ℝ)|^8371 ≤ (11334275989503/25000000000000 : ℝ)^6323
        have hw : |(2750893603/5000000000 : ℝ)|=(2750893603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s2_5 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (660759853/1250000000 : ℝ)*x 0 + (-493272233/2500000000 : ℝ)*x 1 + (5501787209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660759853/1250000000 : ℝ)^8371 ≤ (42998913489369/100000000000000 : ℝ)^6323 := by
    have hnat : (660759853 : ℕ)^8371*100000000000000^6323 ≤ 42998913489369^6323*1250000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660759853 1250000000 42998913489369 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (493272233/2500000000 : ℝ)^8371 ≤ (583199125531/5000000000000 : ℝ)^6323 := by
    have hnat : (493272233 : ℕ)^8371*5000000000000^6323 ≤ 583199125531^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493272233 2500000000 583199125531 5000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5501787209/10000000000 : ℝ)^8371 ≤ (45337103990741/100000000000000 : ℝ)^6323 := by
    have hnat : (5501787209 : ℕ)^8371*100000000000000^6323 ≤ 45337103990741^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501787209 10000000000 45337103990741 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660759853/1250000000 : ℝ), (-493272233/2500000000 : ℝ), (5501787209/10000000000 : ℝ)] ![(42998913489369/100000000000000 : ℝ), (583199125531/5000000000000 : ℝ), (45337103990741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660759853/1250000000 : ℝ)|^8371 ≤ (42998913489369/100000000000000 : ℝ)^6323
        have hw : |(660759853/1250000000 : ℝ)|=(660759853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-493272233/2500000000 : ℝ)|^8371 ≤ (583199125531/5000000000000 : ℝ)^6323
        have hw : |(-493272233/2500000000 : ℝ)|=(493272233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5501787209/10000000000 : ℝ)|^8371 ≤ (45337103990741/100000000000000 : ℝ)^6323
        have hw : |(5501787209/10000000000 : ℝ)|=(5501787209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s2_6 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (660759871/1250000000 : ℝ)*x 0 + (550178721/1000000000 : ℝ)*x 1 + (-493272183/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660759871/1250000000 : ℝ)^8371 ≤ (21499457520057/50000000000000 : ℝ)^6323 := by
    have hnat : (660759871 : ℕ)^8371*50000000000000^6323 ≤ 21499457520057^6323*1250000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660759871 1250000000 21499457520057 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550178721/1000000000 : ℝ)^8371 ≤ (906742080033/2000000000000 : ℝ)^6323 := by
    have hnat : (550178721 : ℕ)^8371*2000000000000^6323 ≤ 906742080033^6323*1000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550178721 1000000000 906742080033 2000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (493272183/2500000000 : ℝ)^8371 ≤ (1457997618171/12500000000000 : ℝ)^6323 := by
    have hnat : (493272183 : ℕ)^8371*12500000000000^6323 ≤ 1457997618171^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493272183 2500000000 1457997618171 12500000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660759871/1250000000 : ℝ), (550178721/1000000000 : ℝ), (-493272183/2500000000 : ℝ)] ![(21499457520057/50000000000000 : ℝ), (906742080033/2000000000000 : ℝ), (1457997618171/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660759871/1250000000 : ℝ)|^8371 ≤ (21499457520057/50000000000000 : ℝ)^6323
        have hw : |(660759871/1250000000 : ℝ)|=(660759871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(550178721/1000000000 : ℝ)|^8371 ≤ (906742080033/2000000000000 : ℝ)^6323
        have hw : |(550178721/1000000000 : ℝ)|=(550178721/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-493272183/2500000000 : ℝ)|^8371 ≤ (1457997618171/12500000000000 : ℝ)^6323
        have hw : |(-493272183/2500000000 : ℝ)|=(493272183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s2_7 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (217492891/500000000 : ℝ)*x 0 + (2348940061/5000000000 : ℝ)*x 1 + (4027586003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217492891/500000000 : ℝ)^8371 ≤ (33218365603789/100000000000000 : ℝ)^6323 := by
    have hnat : (217492891 : ℕ)^8371*100000000000000^6323 ≤ 33218365603789^6323*500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217492891 500000000 33218365603789 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2348940061/5000000000 : ℝ)^8371 ≤ (36781716103027/100000000000000 : ℝ)^6323 := by
    have hnat : (2348940061 : ℕ)^8371*100000000000000^6323 ≤ 36781716103027^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2348940061 5000000000 36781716103027 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4027586003/10000000000 : ℝ)^8371 ≤ (1499995913489/5000000000000 : ℝ)^6323 := by
    have hnat : (4027586003 : ℕ)^8371*5000000000000^6323 ≤ 1499995913489^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027586003 10000000000 1499995913489 5000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217492891/500000000 : ℝ), (2348940061/5000000000 : ℝ), (4027586003/10000000000 : ℝ)] ![(33218365603789/100000000000000 : ℝ), (36781716103027/100000000000000 : ℝ), (1499995913489/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217492891/500000000 : ℝ)|^8371 ≤ (33218365603789/100000000000000 : ℝ)^6323
        have hw : |(217492891/500000000 : ℝ)|=(217492891/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2348940061/5000000000 : ℝ)|^8371 ≤ (36781716103027/100000000000000 : ℝ)^6323
        have hw : |(2348940061/5000000000 : ℝ)|=(2348940061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4027586003/10000000000 : ℝ)|^8371 ≤ (1499995913489/5000000000000 : ℝ)^6323
        have hw : |(4027586003/10000000000 : ℝ)|=(4027586003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1178_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5069/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5849/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (923/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8199/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5069/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5849/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5069/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5849/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5069/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5849/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5069/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5849/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5069/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5849/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5069/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5849/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5849/100000 : ℝ) ^ (4185/1024 : ℝ) ≤ (914468058186517/100000000000000000000 : ℝ) := by
    have hpowers : (5849/100000 : ℝ)^4185 ≤ (914468058186517/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5849 : ℕ)^4185*100000000000000000000^1024 ≤ 914468058186517^1024*100000^4185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5849 100000 914468058186517 100000000000000000000 4185 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5849/100000 : ℝ)) (X := (914468058186517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5069/25000 : ℝ) ^ (4185/1024 : ℝ) ≤ (36782068908024849/25000000000000000000 : ℝ) := by
    have hpowers : (5069/25000 : ℝ)^4185 ≤ (36782068908024849/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5069 : ℕ)^4185*25000000000000000000^1024 ≤ 36782068908024849^1024*25000^4185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5069 25000 36782068908024849 25000000000000000000 4185 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5069/25000 : ℝ)) (X := (36782068908024849/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000914468058186517/50000000000000000000 : ℝ) ≤ (10000044750720369/10000000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (50000914468058186517/50000000000000000000 : ℝ)^1024 ≤ (10000044750720369/10000000000000000 : ℝ)^4185 := by
      have hnat : (50000914468058186517 : ℕ)^1024*10000000000000000^4185 ≤ 10000044750720369^4185*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000914468058186517 50000000000000000000 10000044750720369 10000000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000044750720369/10000000000000000 : ℝ)) (X := (50000914468058186517/50000000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100148042743690285913/100000000000000000000 : ℝ) ≤ (625226271036941/625000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (100148042743690285913/100000000000000000000 : ℝ)^1024 ≤ (625226271036941/625000000000000 : ℝ)^4185 := by
      have hnat : (100148042743690285913 : ℕ)^1024*625000000000000^4185 ≤ 625226271036941^4185*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100148042743690285913 100000000000000000000 625226271036941 625000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625226271036941/625000000000000 : ℝ)) (X := (100148042743690285913/100000000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12536782068908024849/12500000000000000000 : ℝ) ≤ (10007195922461743/10000000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (12536782068908024849/12500000000000000000 : ℝ)^1024 ≤ (10007195922461743/10000000000000000 : ℝ)^4185 := by
      have hnat : (12536782068908024849 : ℕ)^1024*10000000000000000^4185 ≤ 10007195922461743^4185*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12536782068908024849 12500000000000000000 10007195922461743 10000000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007195922461743/10000000000000000 : ℝ)) (X := (12536782068908024849/12500000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(914468058186517/100000000000000000000 : ℝ) ≤ ((144228818415127467037/144270000000000000000 : ℝ)+2*(3575585870687/1442700000000000 : ℝ)*(5849/100000 : ℝ))^(4185/1024 : ℝ) := by
    rw [show (144228818415127467037/144270000000000000000 : ℝ)+2*(3575585870687/1442700000000000 : ℝ)*(5849/100000 : ℝ)=(10000044750720369/10000000000000000 : ℝ) by norm_num, show 1+2*(914468058186517/100000000000000000000 : ℝ)=(50000914468058186517/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36782068908024849/25000000000000000000 : ℝ)+(914468058186517/100000000000000000000 : ℝ) ≤ ((144228818415127467037/144270000000000000000 : ℝ)+(3575585870687/1442700000000000 : ℝ)*((5069/25000 : ℝ)+(5849/100000 : ℝ)))^(4185/1024 : ℝ) := by
    rw [show (144228818415127467037/144270000000000000000 : ℝ)+(3575585870687/1442700000000000 : ℝ)*((5069/25000 : ℝ)+(5849/100000 : ℝ))=(625226271036941/625000000000000 : ℝ) by norm_num, show 1+(36782068908024849/25000000000000000000 : ℝ)+(914468058186517/100000000000000000000 : ℝ)=(100148042743690285913/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36782068908024849/25000000000000000000 : ℝ) ≤ ((144228818415127467037/144270000000000000000 : ℝ)+2*(3575585870687/1442700000000000 : ℝ)*(5069/25000 : ℝ))^(4185/1024 : ℝ) := by
    rw [show (144228818415127467037/144270000000000000000 : ℝ)+2*(3575585870687/1442700000000000 : ℝ)*(5069/25000 : ℝ)=(10007195922461743/10000000000000000 : ℝ) by norm_num, show 1+2*(36782068908024849/25000000000000000000 : ℝ)=(12536782068908024849/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (144228818415127467037/144270000000000000000 : ℝ)*(X 1 0+X 2 0)+(3575585870687/1442700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (5849/100000 : ℝ)) (hi := (5069/25000 : ℝ)) (c := (144228818415127467037/144270000000000000000 : ℝ)) (alpha := (3575585870687/1442700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (144228818415127467037/144270000000000000000 : ℝ)*(X 0 1+X 2 1)+(3575585870687/1442700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (5849/100000 : ℝ)) (hi := (5069/25000 : ℝ)) (c := (144228818415127467037/144270000000000000000 : ℝ)) (alpha := (3575585870687/1442700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (144228818415127467037/144270000000000000000 : ℝ)*(X 0 2+X 1 2)+(3575585870687/1442700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (5849/100000 : ℝ)) (hi := (5069/25000 : ℝ)) (c := (144228818415127467037/144270000000000000000 : ℝ)) (alpha := (3575585870687/1442700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2133848593/10000000000 : ℝ)*X 0 0+(5504090021/10000000000 : ℝ)*X 0 1+(161404689/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5372331903/10000000000 : ℝ)*X 1 0+(-2309924151/10000000000 : ℝ)*X 1 1+(5164953341/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5372332893/10000000000 : ℝ)*X 2 0+(5164951869/10000000000 : ℝ)*X 2 1+(-57748119/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1087417769/2500000000 : ℝ)*X 0 0+(4022974621/10000000000 : ℝ)*X 0 1+(2351223911/5000000000 : ℝ)*X 0 2+(1087417769/2500000000 : ℝ)*X 1 0+(4022974621/10000000000 : ℝ)*X 1 1+(2351223911/5000000000 : ℝ)*X 1 2+(1087417769/2500000000 : ℝ)*X 2 0+(4022974621/10000000000 : ℝ)*X 2 1+(2351223911/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2133940881/10000000000 : ℝ)*X 0 0+(1291807789/2500000000 : ℝ)*X 0 1+(2750893603/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((660759853/1250000000 : ℝ)*X 1 0+(-493272233/2500000000 : ℝ)*X 1 1+(5501787209/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((660759871/1250000000 : ℝ)*X 2 0+(550178721/1000000000 : ℝ)*X 2 1+(-493272183/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((217492891/500000000 : ℝ)*X 0 0+(2348940061/5000000000 : ℝ)*X 0 1+(4027586003/10000000000 : ℝ)*X 0 2+(217492891/500000000 : ℝ)*X 1 0+(2348940061/5000000000 : ℝ)*X 1 1+(4027586003/10000000000 : ℝ)*X 1 2+(217492891/500000000 : ℝ)*X 2 0+(2348940061/5000000000 : ℝ)*X 2 1+(4027586003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2885598203885094824437582279/400750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (781044377/100000000000000 : ℝ)*(base19) + (135771063/12500000000000 : ℝ)*(base23) + (14310901/20000000000000 : ℝ)*(upper2) + (23183707/5000000000000 : ℝ)*(upper3) + (199552139/100000000000000 : ℝ)*(upper4) + (1105109989998467/50000000000000 : ℝ)*(major0) + (1105109989998467/50000000000000 : ℝ)*(major1) + (1105109989998467/50000000000000 : ℝ)*(major2) + (1474333079154003/50000000000000 : ℝ)*(sp0) + (294869165016309/10000000000000 : ℝ)*(sp1) + (2948691345038963/100000000000000 : ℝ)*(sp2) + (1471735148036261/100000000000000 : ℝ)*(sp3) + (26272899461/100000000000000 : ℝ)*(sp4) + (2428146729/20000000000000 : ℝ)*(sp7) + (294349457753981/20000000000000 : ℝ)*(f.failure) + (1474346215603733/50000000000000 : ℝ)*(f.sum) + (353955562095337/72135000000000000000000000000 : ℝ)*base66 + (15274319273389855907/2404500000000000000000000000000000 : ℝ)*base68 + (22346369554720855907/2404500000000000000000000000000000 : ℝ)*base70 + (1656792257958355907/2404500000000000000000000000000000 : ℝ)*base72 + (53607794332777/72135000000000000000000000000 : ℝ)*base74 + (9477012916582855907/2404500000000000000000000000000000 : ℝ)*base76 + (25056063035158855907/2404500000000000000000000000000000 : ℝ)*base78 + (16286269461012355907/2404500000000000000000000000000000 : ℝ)*base80 + (444447517290937/72135000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1992831/500000000000000000000 : ℝ)*base90 + (1992831/500000000000000000000 : ℝ)*base92 + (1992831/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (764023064466618447549054973/80150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2162405793/100000000000000 : ℝ)*(base19) + (464932533/20000000000000 : ℝ)*(base23) + (32480447/12500000000000 : ℝ)*(upper3) + (15900679/100000000000000 : ℝ)*(lower4) + (50733173/25000000000000 : ℝ)*(upper5) + (224045919155729/10000000000000 : ℝ)*(major0) + (224045919155729/10000000000000 : ℝ)*(major1) + (224045919155729/10000000000000 : ℝ)*(major2) + (21189949761/100000000000000 : ℝ)*(sp1) + (1215001827/5000000000000 : ℝ)*(sp2) + (1494517504099151/50000000000000 : ℝ)*(sp4) + (747252913960687/25000000000000 : ℝ)*(sp5) + (2989008383499097/100000000000000 : ℝ)*(sp6) + (745941528584551/50000000000000 : ℝ)*(sp7) + (745941528584551/50000000000000 : ℝ)*(f.failure) + (1494517504099151/50000000000000 : ℝ)*(f.sum) + (1169502630227/180337500000000000000000000 : ℝ)*base66 + (2557259639380565009/480900000000000000000000000000000 : ℝ)*base68 + (6029461495506365009/480900000000000000000000000000000 : ℝ)*base70 + (4846287671757665009/480900000000000000000000000000000 : ℝ)*base72 + (16405390864873/14427000000000000000000000000 : ℝ)*base74 + (6850063302445265009/480900000000000000000000000000000 : ℝ)*base76 + (4739676268360565009/480900000000000000000000000000000 : ℝ)*base78 + (2288795058986765009/480900000000000000000000000000000 : ℝ)*base80 + (22456554738127/3606750000000000000000000000 : ℝ)*base82 + (16842099/1250000000000000000000 : ℝ)*base89 + (16842099/1250000000000000000000 : ℝ)*base91 + (16842099/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1178_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5069/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5849/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (923/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8199/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1178_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1178_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (923/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8199/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1178_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1178_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1178_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (923/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8199/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1178_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

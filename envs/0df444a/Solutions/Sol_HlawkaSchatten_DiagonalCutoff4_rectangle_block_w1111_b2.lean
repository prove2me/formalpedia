-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1111_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:05:03.210234+00:00
-- url     : https://prove2.me/submissions/da10a519-e907-43c7-b606-dd56e45a501e

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
theorem support_rectangle_w1111_s6_0 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-545440819/2500000000 : ℝ)*x 0 + (2697001047/5000000000 : ℝ)*x 1 + (2632418129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545440819/2500000000 : ℝ)^519 ≤ (13254272778141/100000000000000 : ℝ)^391 := by
    have hnat : (545440819 : ℕ)^519*100000000000000^391 ≤ 13254272778141^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545440819 2500000000 13254272778141 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697001047/5000000000 : ℝ)^519 ≤ (22035250926229/50000000000000 : ℝ)^391 := by
    have hnat : (2697001047 : ℕ)^519*50000000000000^391 ≤ 22035250926229^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697001047 5000000000 22035250926229 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632418129/5000000000 : ℝ)^519 ≤ (42675225355393/100000000000000 : ℝ)^391 := by
    have hnat : (2632418129 : ℕ)^519*100000000000000^391 ≤ 42675225355393^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632418129 5000000000 42675225355393 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-545440819/2500000000 : ℝ), (2697001047/5000000000 : ℝ), (2632418129/5000000000 : ℝ)] ![(13254272778141/100000000000000 : ℝ), (22035250926229/50000000000000 : ℝ), (42675225355393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-545440819/2500000000 : ℝ)|^519 ≤ (13254272778141/100000000000000 : ℝ)^391
        have hw : |(-545440819/2500000000 : ℝ)|=(545440819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697001047/5000000000 : ℝ)|^519 ≤ (22035250926229/50000000000000 : ℝ)^391
        have hw : |(2697001047/5000000000 : ℝ)|=(2697001047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632418129/5000000000 : ℝ)|^519 ≤ (42675225355393/100000000000000 : ℝ)^391
        have hw : |(2632418129/5000000000 : ℝ)|=(2632418129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s6_1 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1336241701/2500000000 : ℝ)*x 0 + (-561823071/2500000000 : ℝ)*x 1 + (5264836259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336241701/2500000000 : ℝ)^519 ≤ (5442438697417/12500000000000 : ℝ)^391 := by
    have hnat : (1336241701 : ℕ)^519*12500000000000^391 ≤ 5442438697417^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336241701 2500000000 5442438697417 12500000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561823071/2500000000 : ℝ)^519 ≤ (1723158129001/12500000000000 : ℝ)^391 := by
    have hnat : (561823071 : ℕ)^519*12500000000000^391 ≤ 1723158129001^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561823071 2500000000 1723158129001 12500000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264836259/10000000000 : ℝ)^519 ≤ (5334403170769/12500000000000 : ℝ)^391 := by
    have hnat : (5264836259 : ℕ)^519*12500000000000^391 ≤ 5334403170769^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264836259 10000000000 5334403170769 12500000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336241701/2500000000 : ℝ), (-561823071/2500000000 : ℝ), (5264836259/10000000000 : ℝ)] ![(5442438697417/12500000000000 : ℝ), (1723158129001/12500000000000 : ℝ), (5334403170769/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336241701/2500000000 : ℝ)|^519 ≤ (5442438697417/12500000000000 : ℝ)^391
        have hw : |(1336241701/2500000000 : ℝ)|=(1336241701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-561823071/2500000000 : ℝ)|^519 ≤ (1723158129001/12500000000000 : ℝ)^391
        have hw : |(-561823071/2500000000 : ℝ)|=(561823071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264836259/10000000000 : ℝ)|^519 ≤ (5334403170769/12500000000000 : ℝ)^391
        have hw : |(5264836259/10000000000 : ℝ)|=(5264836259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s6_2 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1068993361/2000000000 : ℝ)*x 0 + (658104533/1250000000 : ℝ)*x 1 + (-2247292277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068993361/2000000000 : ℝ)^519 ≤ (43539509590149/100000000000000 : ℝ)^391 := by
    have hnat : (1068993361 : ℕ)^519*100000000000000^391 ≤ 43539509590149^391*2000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068993361 2000000000 43539509590149 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658104533/1250000000 : ℝ)^519 ≤ (10668806354987/25000000000000 : ℝ)^391 := by
    have hnat : (658104533 : ℕ)^519*25000000000000^391 ≤ 10668806354987^391*1250000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658104533 1250000000 10668806354987 25000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247292277/10000000000 : ℝ)^519 ≤ (3446316243753/25000000000000 : ℝ)^391 := by
    have hnat : (2247292277 : ℕ)^519*25000000000000^391 ≤ 3446316243753^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247292277 10000000000 3446316243753 25000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068993361/2000000000 : ℝ), (658104533/1250000000 : ℝ), (-2247292277/10000000000 : ℝ)] ![(43539509590149/100000000000000 : ℝ), (10668806354987/25000000000000 : ℝ), (3446316243753/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068993361/2000000000 : ℝ)|^519 ≤ (43539509590149/100000000000000 : ℝ)^391
        have hw : |(1068993361/2000000000 : ℝ)|=(1068993361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658104533/1250000000 : ℝ)|^519 ≤ (10668806354987/25000000000000 : ℝ)^391
        have hw : |(658104533/1250000000 : ℝ)|=(658104533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2247292277/10000000000 : ℝ)|^519 ≤ (3446316243753/25000000000000 : ℝ)^391
        have hw : |(-2247292277/10000000000 : ℝ)|=(2247292277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s6_3 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4369038253/10000000000 : ℝ)*x 0 + (530400471/1250000000 : ℝ)*x 1 + (4393178/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369038253/10000000000 : ℝ)^519 ≤ (3331658643763/10000000000000 : ℝ)^391 := by
    have hnat : (4369038253 : ℕ)^519*10000000000000^391 ≤ 3331658643763^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369038253 10000000000 3331658643763 10000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530400471/1250000000 : ℝ)^519 ≤ (32048936773399/100000000000000 : ℝ)^391 := by
    have hnat : (530400471 : ℕ)^519*100000000000000^391 ≤ 32048936773399^391*1250000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530400471 1250000000 32048936773399 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4393178/9765625 : ℝ)^519 ≤ (34634476770601/100000000000000 : ℝ)^391 := by
    have hnat : (4393178 : ℕ)^519*100000000000000^391 ≤ 34634476770601^391*9765625^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4393178 9765625 34634476770601 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369038253/10000000000 : ℝ), (530400471/1250000000 : ℝ), (4393178/9765625 : ℝ)] ![(3331658643763/10000000000000 : ℝ), (32048936773399/100000000000000 : ℝ), (34634476770601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369038253/10000000000 : ℝ)|^519 ≤ (3331658643763/10000000000000 : ℝ)^391
        have hw : |(4369038253/10000000000 : ℝ)|=(4369038253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(530400471/1250000000 : ℝ)|^519 ≤ (32048936773399/100000000000000 : ℝ)^391
        have hw : |(530400471/1250000000 : ℝ)|=(530400471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4393178/9765625 : ℝ)|^519 ≤ (34634476770601/100000000000000 : ℝ)^391
        have hw : |(4393178/9765625 : ℝ)|=(4393178/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s6_4 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-545442091/2500000000 : ℝ)*x 0 + (1316290597/2500000000 : ℝ)*x 1 + (10534521/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545442091/2500000000 : ℝ)^519 ≤ (13254313806689/100000000000000 : ℝ)^391 := by
    have hnat : (545442091 : ℕ)^519*100000000000000^391 ≤ 13254313806689^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545442091 2500000000 13254313806689 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316290597/2500000000 : ℝ)^519 ≤ (21339367150793/50000000000000 : ℝ)^391 := by
    have hnat : (1316290597 : ℕ)^519*50000000000000^391 ≤ 21339367150793^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316290597 2500000000 21339367150793 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10534521/19531250 : ℝ)^519 ≤ (44066951880657/100000000000000 : ℝ)^391 := by
    have hnat : (10534521 : ℕ)^519*100000000000000^391 ≤ 44066951880657^391*19531250^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10534521 19531250 44066951880657 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-545442091/2500000000 : ℝ), (1316290597/2500000000 : ℝ), (10534521/19531250 : ℝ)] ![(13254313806689/100000000000000 : ℝ), (21339367150793/50000000000000 : ℝ), (44066951880657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-545442091/2500000000 : ℝ)|^519 ≤ (13254313806689/100000000000000 : ℝ)^391
        have hw : |(-545442091/2500000000 : ℝ)|=(545442091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316290597/2500000000 : ℝ)|^519 ≤ (21339367150793/50000000000000 : ℝ)^391
        have hw : |(1316290597/2500000000 : ℝ)|=(1316290597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10534521/19531250 : ℝ)|^519 ≤ (44066951880657/100000000000000 : ℝ)^391
        have hw : |(10534521/19531250 : ℝ)|=(10534521/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s6_5 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312318343/10000000000 : ℝ)*x 0 + (-132403361/625000000 : ℝ)*x 1 + (1348418679/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312318343/10000000000 : ℝ)^519 ≤ (5398356136251/12500000000000 : ℝ)^391 := by
    have hnat : (5312318343 : ℕ)^519*12500000000000^391 ≤ 5398356136251^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312318343 10000000000 5398356136251 12500000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132403361/625000000 : ℝ)^519 ≤ (6373099702389/50000000000000 : ℝ)^391 := by
    have hnat : (132403361 : ℕ)^519*50000000000000^391 ≤ 6373099702389^391*625000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132403361 625000000 6373099702389 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348418679/2500000000 : ℝ)^519 ≤ (22033475745123/50000000000000 : ℝ)^391 := by
    have hnat : (1348418679 : ℕ)^519*50000000000000^391 ≤ 22033475745123^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348418679 2500000000 22033475745123 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312318343/10000000000 : ℝ), (-132403361/625000000 : ℝ), (1348418679/2500000000 : ℝ)] ![(5398356136251/12500000000000 : ℝ), (6373099702389/50000000000000 : ℝ), (22033475745123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312318343/10000000000 : ℝ)|^519 ≤ (5398356136251/12500000000000 : ℝ)^391
        have hw : |(5312318343/10000000000 : ℝ)|=(5312318343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-132403361/625000000 : ℝ)|^519 ≤ (6373099702389/50000000000000 : ℝ)^391
        have hw : |(-132403361/625000000 : ℝ)|=(132403361/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348418679/2500000000 : ℝ)|^519 ≤ (22033475745123/50000000000000 : ℝ)^391
        have hw : |(1348418679/2500000000 : ℝ)|=(1348418679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s6_6 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2656159183/5000000000 : ℝ)*x 0 + (2696837337/5000000000 : ℝ)*x 1 + (-1059226901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656159183/5000000000 : ℝ)^519 ≤ (43186849338199/100000000000000 : ℝ)^391 := by
    have hnat : (2656159183 : ℕ)^519*100000000000000^391 ≤ 43186849338199^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656159183 5000000000 43186849338199 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696837337/5000000000 : ℝ)^519 ≤ (2754184439673/6250000000000 : ℝ)^391 := by
    have hnat : (2696837337 : ℕ)^519*6250000000000^391 ≤ 2754184439673^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696837337 5000000000 2754184439673 6250000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059226901/5000000000 : ℝ)^519 ≤ (509847984497/4000000000000 : ℝ)^391 := by
    have hnat : (1059226901 : ℕ)^519*4000000000000^391 ≤ 509847984497^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059226901 5000000000 509847984497 4000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656159183/5000000000 : ℝ), (2696837337/5000000000 : ℝ), (-1059226901/5000000000 : ℝ)] ![(43186849338199/100000000000000 : ℝ), (2754184439673/6250000000000 : ℝ), (509847984497/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656159183/5000000000 : ℝ)|^519 ≤ (43186849338199/100000000000000 : ℝ)^391
        have hw : |(2656159183/5000000000 : ℝ)|=(2656159183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696837337/5000000000 : ℝ)|^519 ≤ (2754184439673/6250000000000 : ℝ)^391
        have hw : |(2696837337/5000000000 : ℝ)|=(2696837337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1059226901/5000000000 : ℝ)|^519 ≤ (509847984497/4000000000000 : ℝ)^391
        have hw : |(-1059226901/5000000000 : ℝ)|=(1059226901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s6_7 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4369048247/10000000000 : ℝ)*x 0 + (1124492321/2500000000 : ℝ)*x 1 + (848770219/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369048247/10000000000 : ℝ)^519 ≤ (8329171899171/25000000000000 : ℝ)^391 := by
    have hnat : (4369048247 : ℕ)^519*25000000000000^391 ≤ 8329171899171^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369048247 10000000000 8329171899171 25000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124492321/2500000000 : ℝ)^519 ≤ (34627885609649/100000000000000 : ℝ)^391 := by
    have hnat : (1124492321 : ℕ)^519*100000000000000^391 ≤ 34627885609649^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124492321 2500000000 34627885609649 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848770219/2000000000 : ℝ)^519 ≤ (32055426776507/100000000000000 : ℝ)^391 := by
    have hnat : (848770219 : ℕ)^519*100000000000000^391 ≤ 32055426776507^391*2000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848770219 2000000000 32055426776507 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369048247/10000000000 : ℝ), (1124492321/2500000000 : ℝ), (848770219/2000000000 : ℝ)] ![(8329171899171/25000000000000 : ℝ), (34627885609649/100000000000000 : ℝ), (32055426776507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369048247/10000000000 : ℝ)|^519 ≤ (8329171899171/25000000000000 : ℝ)^391
        have hw : |(4369048247/10000000000 : ℝ)|=(4369048247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124492321/2500000000 : ℝ)|^519 ≤ (34627885609649/100000000000000 : ℝ)^391
        have hw : |(1124492321/2500000000 : ℝ)|=(1124492321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848770219/2000000000 : ℝ)|^519 ≤ (32055426776507/100000000000000 : ℝ)^391
        have hw : |(848770219/2000000000 : ℝ)|=(848770219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1111_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1413/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (351/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3519/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3519/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3519/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3519/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3519/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3519/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11269/100000 : ℝ) ^ (8303/2048 : ℝ) ≤ (2865394609053499/20000000000000000000 : ℝ) := by
    have hpowers : (11269/100000 : ℝ)^8303 ≤ (2865394609053499/20000000000000000000 : ℝ)^2048 := by
      have hnat : (11269 : ℕ)^8303*20000000000000000000^2048 ≤ 2865394609053499^2048*100000^8303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11269 100000 2865394609053499 20000000000000000000 8303 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11269/100000 : ℝ)) (X := (2865394609053499/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3519/25000 : ℝ) ^ (8303/2048 : ℝ) ≤ (35299233388558397/100000000000000000000 : ℝ) := by
    have hpowers : (3519/25000 : ℝ)^8303 ≤ (35299233388558397/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3519 : ℕ)^8303*100000000000000000000^2048 ≤ 35299233388558397^2048*25000^8303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3519 25000 35299233388558397 100000000000000000000 8303 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3519/25000 : ℝ)) (X := (35299233388558397/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002865394609053499/10000000000000000000 : ℝ) ≤ (10000706695759377/10000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (10002865394609053499/10000000000000000000 : ℝ)^2048 ≤ (10000706695759377/10000000000000000 : ℝ)^8303 := by
      have hnat : (10002865394609053499 : ℕ)^2048*10000000000000000^8303 ≤ 10000706695759377^8303*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002865394609053499 10000000000000000000 10000706695759377 10000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000706695759377/10000000000000000 : ℝ)) (X := (10002865394609053499/10000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012406551608456473/25000000000000000000 : ℝ) ≤ (250030596012887/250000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (25012406551608456473/25000000000000000000 : ℝ)^2048 ≤ (250030596012887/250000000000000 : ℝ)^8303 := by
      have hnat : (25012406551608456473 : ℕ)^2048*250000000000000^8303 ≤ 250030596012887^8303*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012406551608456473 25000000000000000000 250030596012887 250000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250030596012887/250000000000000 : ℝ)) (X := (25012406551608456473/25000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035299233388558397/50000000000000000000 : ℝ) ≤ (10001740985271583/10000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (50035299233388558397/50000000000000000000 : ℝ)^2048 ≤ (10001740985271583/10000000000000000 : ℝ)^8303 := by
      have hnat : (50035299233388558397 : ℕ)^2048*10000000000000000^8303 ≤ 10001740985271583^8303*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035299233388558397 50000000000000000000 10001740985271583 10000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001740985271583/10000000000000000 : ℝ)) (X := (50035299233388558397/50000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2865394609053499/20000000000000000000 : ℝ) ≤ ((1122413131459340873/1122800000000000000 : ℝ)+2*(517144756103/280700000000000 : ℝ)*(11269/100000 : ℝ))^(8303/2048 : ℝ) := by
    rw [show (1122413131459340873/1122800000000000000 : ℝ)+2*(517144756103/280700000000000 : ℝ)*(11269/100000 : ℝ)=(10000706695759377/10000000000000000 : ℝ) by norm_num, show 1+2*(2865394609053499/20000000000000000000 : ℝ)=(10002865394609053499/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35299233388558397/100000000000000000000 : ℝ)+(2865394609053499/20000000000000000000 : ℝ) ≤ ((1122413131459340873/1122800000000000000 : ℝ)+(517144756103/280700000000000 : ℝ)*((3519/25000 : ℝ)+(11269/100000 : ℝ)))^(8303/2048 : ℝ) := by
    rw [show (1122413131459340873/1122800000000000000 : ℝ)+(517144756103/280700000000000 : ℝ)*((3519/25000 : ℝ)+(11269/100000 : ℝ))=(250030596012887/250000000000000 : ℝ) by norm_num, show 1+(35299233388558397/100000000000000000000 : ℝ)+(2865394609053499/20000000000000000000 : ℝ)=(25012406551608456473/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35299233388558397/100000000000000000000 : ℝ) ≤ ((1122413131459340873/1122800000000000000 : ℝ)+2*(517144756103/280700000000000 : ℝ)*(3519/25000 : ℝ))^(8303/2048 : ℝ) := by
    rw [show (1122413131459340873/1122800000000000000 : ℝ)+2*(517144756103/280700000000000 : ℝ)*(3519/25000 : ℝ)=(10001740985271583/10000000000000000 : ℝ) by norm_num, show 1+2*(35299233388558397/100000000000000000000 : ℝ)=(50035299233388558397/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1122413131459340873/1122800000000000000 : ℝ)*(X 1 0+X 2 0)+(517144756103/280700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (1122413131459340873/1122800000000000000 : ℝ)) (alpha := (517144756103/280700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1122413131459340873/1122800000000000000 : ℝ)*(X 0 1+X 2 1)+(517144756103/280700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (1122413131459340873/1122800000000000000 : ℝ)) (alpha := (517144756103/280700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1122413131459340873/1122800000000000000 : ℝ)*(X 0 2+X 1 2)+(517144756103/280700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (1122413131459340873/1122800000000000000 : ℝ)) (alpha := (517144756103/280700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-545440819/2500000000 : ℝ)*X 0 0+(2697001047/5000000000 : ℝ)*X 0 1+(2632418129/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336241701/2500000000 : ℝ)*X 1 0+(-561823071/2500000000 : ℝ)*X 1 1+(5264836259/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068993361/2000000000 : ℝ)*X 2 0+(658104533/1250000000 : ℝ)*X 2 1+(-2247292277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4369038253/10000000000 : ℝ)*X 0 0+(530400471/1250000000 : ℝ)*X 0 1+(4393178/9765625 : ℝ)*X 0 2+(4369038253/10000000000 : ℝ)*X 1 0+(530400471/1250000000 : ℝ)*X 1 1+(4393178/9765625 : ℝ)*X 1 2+(4369038253/10000000000 : ℝ)*X 2 0+(530400471/1250000000 : ℝ)*X 2 1+(4393178/9765625 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-545442091/2500000000 : ℝ)*X 0 0+(1316290597/2500000000 : ℝ)*X 0 1+(10534521/19531250 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312318343/10000000000 : ℝ)*X 1 0+(-132403361/625000000 : ℝ)*X 1 1+(1348418679/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656159183/5000000000 : ℝ)*X 2 0+(2696837337/5000000000 : ℝ)*X 2 1+(-1059226901/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4369048247/10000000000 : ℝ)*X 0 0+(1124492321/2500000000 : ℝ)*X 0 1+(848770219/2000000000 : ℝ)*X 0 2+(4369048247/10000000000 : ℝ)*X 1 0+(1124492321/2500000000 : ℝ)*X 1 1+(848770219/2000000000 : ℝ)*X 1 2+(4369048247/10000000000 : ℝ)*X 2 0+(1124492321/2500000000 : ℝ)*X 2 1+(848770219/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62914482716826156094776891/14035000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (454262367/50000000000000 : ℝ)*(base19) + (843505047/100000000000000 : ℝ)*(base23) + (3552701/10000000000000 : ℝ)*(lower2) + (28284437/25000000000000 : ℝ)*(upper3) + (37886241/50000000000000 : ℝ)*(upper5) + (1457165806968763/25000000000000 : ℝ)*(major0) + (1457165806968763/25000000000000 : ℝ)*(major1) + (1457165806968763/25000000000000 : ℝ)*(major2) + (1548402125181809/20000000000000 : ℝ)*(sp0) + (967754298357341/12500000000000 : ℝ)*(sp1) + (1548406890375683/20000000000000 : ℝ)*(sp2) + (1957638899229137/50000000000000 : ℝ)*(sp3) + (12334737209/50000000000000 : ℝ)*(sp4) + (13212485521/100000000000000 : ℝ)*(sp7) + (978822752735949/25000000000000 : ℝ)*(f.failure) + (3871017647691731/50000000000000 : ℝ)*(f.sum) + (94270693304061/14035000000000000000000000000 : ℝ)*base65 + (36482926174884843/4010000000000000000000000000000 : ℝ)*base68 + (105815770672474843/4010000000000000000000000000000 : ℝ)*base70 + (39434721303994843/4010000000000000000000000000000 : ℝ)*base72 + (5158412796727/1754375000000000000000000000 : ℝ)*base73 + (91710076802534843/4010000000000000000000000000000 : ℝ)*base76 + (51758849843624843/4010000000000000000000000000000 : ℝ)*base78 + (98419425870344843/4010000000000000000000000000000 : ℝ)*base80 + (2385694521689/877187500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (46325729/2500000000000000000000 : ℝ)*base89 + (46325729/2500000000000000000000 : ℝ)*base91 + (46325729/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (233180333590483302330410499/28070000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1817924287/100000000000000 : ℝ)*(base19) + (955721813/50000000000000 : ℝ)*(base23) + (39806753/25000000000000 : ℝ)*(upper3) + (7403141/20000000000000 : ℝ)*(lower4) + (214044077/100000000000000 : ℝ)*(upper5) + (2929132505102493/50000000000000 : ℝ)*(major0) + (2929132505102493/50000000000000 : ℝ)*(major1) + (2929132505102493/50000000000000 : ℝ)*(major2) + (50462819123/100000000000000 : ℝ)*(sp1) + (24430107227/50000000000000 : ℝ)*(sp2) + (7781354311773127/100000000000000 : ℝ)*(sp4) + (1945325507757429/25000000000000 : ℝ)*(sp5) + (7781303540115047/100000000000000 : ℝ)*(sp6) + (1967587715866729/50000000000000 : ℝ)*(sp7) + (1967587715866729/50000000000000 : ℝ)*(f.failure) + (7781354311773127/100000000000000 : ℝ)*(f.sum) + (8482982896391/1754375000000000000000000000 : ℝ)*base65 + (47669075638784627/8020000000000000000000000000000 : ℝ)*base67 + (4559372817464627/8020000000000000000000000000000 : ℝ)*base69 + (109543614169624627/8020000000000000000000000000000 : ℝ)*base71 + (10369234519891/7017500000000000000000000000 : ℝ)*base74 + (202566339705284627/8020000000000000000000000000000 : ℝ)*base75 + (32824461049784627/8020000000000000000000000000000 : ℝ)*base77 + (108486080929624627/8020000000000000000000000000000 : ℝ)*base79 + (15506251000691/1754375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (13951891/5000000000000000000000 : ℝ)*base90 + (13951891/5000000000000000000000 : ℝ)*base92 + (13951891/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1111_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1413/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (351/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1111_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1111_s7_0 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-218179347/1000000000 : ℝ)*x 0 + (5393631543/10000000000 : ℝ)*x 1 + (5265187123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218179347/1000000000 : ℝ)^519 ≤ (6627258128291/50000000000000 : ℝ)^391 := by
    have hnat : (218179347 : ℕ)^519*50000000000000^391 ≤ 6627258128291^391*1000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218179347 1000000000 6627258128291 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393631543/10000000000 : ℝ)^519 ≤ (4406648329121/10000000000000 : ℝ)^391 := by
    have hnat : (5393631543 : ℕ)^519*10000000000000^391 ≤ 4406648329121^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393631543 10000000000 4406648329121 10000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265187123/10000000000 : ℝ)^519 ≤ (10669750109241/25000000000000 : ℝ)^391 := by
    have hnat : (5265187123 : ℕ)^519*25000000000000^391 ≤ 10669750109241^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265187123 10000000000 10669750109241 25000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-218179347/1000000000 : ℝ), (5393631543/10000000000 : ℝ), (5265187123/10000000000 : ℝ)] ![(6627258128291/50000000000000 : ℝ), (4406648329121/10000000000000 : ℝ), (10669750109241/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-218179347/1000000000 : ℝ)|^519 ≤ (6627258128291/50000000000000 : ℝ)^391
        have hw : |(-218179347/1000000000 : ℝ)|=(218179347/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393631543/10000000000 : ℝ)|^519 ≤ (4406648329121/10000000000000 : ℝ)^391
        have hw : |(5393631543/10000000000 : ℝ)|=(5393631543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265187123/10000000000 : ℝ)|^519 ≤ (10669750109241/25000000000000 : ℝ)^391
        have hw : |(5265187123/10000000000 : ℝ)|=(5265187123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s7_1 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (66810931/125000000 : ℝ)*x 0 + (-1123475619/5000000000 : ℝ)*x 1 + (42121497/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66810931/125000000 : ℝ)^519 ≤ (43538511322011/100000000000000 : ℝ)^391 := by
    have hnat : (66810931 : ℕ)^519*100000000000000^391 ≤ 43538511322011^391*125000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66810931 125000000 43538511322011 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123475619/5000000000 : ℝ)^519 ≤ (13782488208153/100000000000000 : ℝ)^391 := by
    have hnat : (1123475619 : ℕ)^519*100000000000000^391 ≤ 13782488208153^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123475619 5000000000 13782488208153 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42121497/80000000 : ℝ)^519 ≤ (42679000458483/100000000000000 : ℝ)^391 := by
    have hnat : (42121497 : ℕ)^519*100000000000000^391 ≤ 42679000458483^391*80000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42121497 80000000 42679000458483 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66810931/125000000 : ℝ), (-1123475619/5000000000 : ℝ), (42121497/80000000 : ℝ)] ![(43538511322011/100000000000000 : ℝ), (13782488208153/100000000000000 : ℝ), (42679000458483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66810931/125000000 : ℝ)|^519 ≤ (43538511322011/100000000000000 : ℝ)^391
        have hw : |(66810931/125000000 : ℝ)|=(66810931/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1123475619/5000000000 : ℝ)|^519 ≤ (13782488208153/100000000000000 : ℝ)^391
        have hw : |(-1123475619/5000000000 : ℝ)|=(1123475619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42121497/80000000 : ℝ)|^519 ≤ (42679000458483/100000000000000 : ℝ)^391
        have hw : |(42121497/80000000 : ℝ)|=(42121497/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s7_2 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (66810931/125000000 : ℝ)*x 0 + (2632593563/5000000000 : ℝ)*x 1 + (-561737809/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66810931/125000000 : ℝ)^519 ≤ (43538511322011/100000000000000 : ℝ)^391 := by
    have hnat : (66810931 : ℕ)^519*100000000000000^391 ≤ 43538511322011^391*125000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66810931 125000000 43538511322011 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632593563/5000000000 : ℝ)^519 ≤ (42679000469243/100000000000000 : ℝ)^391 := by
    have hnat : (2632593563 : ℕ)^519*100000000000000^391 ≤ 42679000469243^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632593563 5000000000 42679000469243 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561737809/2500000000 : ℝ)^519 ≤ (13782488191869/100000000000000 : ℝ)^391 := by
    have hnat : (561737809 : ℕ)^519*100000000000000^391 ≤ 13782488191869^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561737809 2500000000 13782488191869 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66810931/125000000 : ℝ), (2632593563/5000000000 : ℝ), (-561737809/2500000000 : ℝ)] ![(43538511322011/100000000000000 : ℝ), (42679000469243/100000000000000 : ℝ), (13782488191869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66810931/125000000 : ℝ)|^519 ≤ (43538511322011/100000000000000 : ℝ)^391
        have hw : |(66810931/125000000 : ℝ)|=(66810931/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632593563/5000000000 : ℝ)|^519 ≤ (42679000469243/100000000000000 : ℝ)^391
        have hw : |(2632593563/5000000000 : ℝ)|=(2632593563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-561737809/2500000000 : ℝ)|^519 ≤ (13782488191869/100000000000000 : ℝ)^391
        have hw : |(-561737809/2500000000 : ℝ)|=(561737809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s7_3 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4369056659/10000000000 : ℝ)*x 0 + (4243914631/10000000000 : ℝ)*x 1 + (4497898613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369056659/10000000000 : ℝ)^519 ≤ (33316772742827/100000000000000 : ℝ)^391 := by
    have hnat : (4369056659 : ℕ)^519*100000000000000^391 ≤ 33316772742827^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369056659 10000000000 33316772742827 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4243914631/10000000000 : ℝ)^519 ≤ (32056063796349/100000000000000 : ℝ)^391 := by
    have hnat : (4243914631 : ℕ)^519*100000000000000^391 ≤ 32056063796349^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243914631 10000000000 32056063796349 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497898613/10000000000 : ℝ)^519 ≤ (4328395429797/12500000000000 : ℝ)^391 := by
    have hnat : (4497898613 : ℕ)^519*12500000000000^391 ≤ 4328395429797^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497898613 10000000000 4328395429797 12500000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369056659/10000000000 : ℝ), (4243914631/10000000000 : ℝ), (4497898613/10000000000 : ℝ)] ![(33316772742827/100000000000000 : ℝ), (32056063796349/100000000000000 : ℝ), (4328395429797/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369056659/10000000000 : ℝ)|^519 ≤ (33316772742827/100000000000000 : ℝ)^391
        have hw : |(4369056659/10000000000 : ℝ)|=(4369056659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4243914631/10000000000 : ℝ)|^519 ≤ (32056063796349/100000000000000 : ℝ)^391
        have hw : |(4243914631/10000000000 : ℝ)|=(4243914631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497898613/10000000000 : ℝ)|^519 ≤ (4328395429797/12500000000000 : ℝ)^391
        have hw : |(4497898613/10000000000 : ℝ)|=(4497898613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s7_4 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1090899227/5000000000 : ℝ)*x 0 + (5265509597/10000000000 : ℝ)*x 1 + (5393307891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090899227/5000000000 : ℝ)^519 ≤ (6627278223339/50000000000000 : ℝ)^391 := by
    have hnat : (1090899227 : ℕ)^519*50000000000000^391 ≤ 6627278223339^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090899227 5000000000 6627278223339 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265509597/10000000000 : ℝ)^519 ≤ (21341235061139/50000000000000 : ℝ)^391 := by
    have hnat : (5265509597 : ℕ)^519*50000000000000^391 ≤ 21341235061139^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265509597 10000000000 21341235061139 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393307891/10000000000 : ℝ)^519 ≤ (44062973415417/100000000000000 : ℝ)^391 := by
    have hnat : (5393307891 : ℕ)^519*100000000000000^391 ≤ 44062973415417^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393307891 10000000000 44062973415417 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1090899227/5000000000 : ℝ), (5265509597/10000000000 : ℝ), (5393307891/10000000000 : ℝ)] ![(6627278223339/50000000000000 : ℝ), (21341235061139/50000000000000 : ℝ), (44062973415417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1090899227/5000000000 : ℝ)|^519 ≤ (6627278223339/50000000000000 : ℝ)^391
        have hw : |(-1090899227/5000000000 : ℝ)|=(1090899227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265509597/10000000000 : ℝ)|^519 ≤ (21341235061139/50000000000000 : ℝ)^391
        have hw : |(5265509597/10000000000 : ℝ)|=(5265509597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393307891/10000000000 : ℝ)|^519 ≤ (44062973415417/100000000000000 : ℝ)^391
        have hw : |(5393307891/10000000000 : ℝ)|=(5393307891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s7_5 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312408181/10000000000 : ℝ)*x 0 + (-2118830471/10000000000 : ℝ)*x 1 + (2696653951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312408181/10000000000 : ℝ)^519 ≤ (1349619328949/3125000000000 : ℝ)^391 := by
    have hnat : (5312408181 : ℕ)^519*3125000000000^391 ≤ 1349619328949^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312408181 10000000000 1349619328949 3125000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2118830471/10000000000 : ℝ)^519 ≤ (6374603969001/50000000000000 : ℝ)^391 := by
    have hnat : (2118830471 : ℕ)^519*50000000000000^391 ≤ 6374603969001^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118830471 10000000000 6374603969001 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696653951/5000000000 : ℝ)^519 ≤ (22031486767353/50000000000000 : ℝ)^391 := by
    have hnat : (2696653951 : ℕ)^519*50000000000000^391 ≤ 22031486767353^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696653951 5000000000 22031486767353 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312408181/10000000000 : ℝ), (-2118830471/10000000000 : ℝ), (2696653951/5000000000 : ℝ)] ![(1349619328949/3125000000000 : ℝ), (6374603969001/50000000000000 : ℝ), (22031486767353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312408181/10000000000 : ℝ)|^519 ≤ (1349619328949/3125000000000 : ℝ)^391
        have hw : |(5312408181/10000000000 : ℝ)|=(5312408181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2118830471/10000000000 : ℝ)|^519 ≤ (6374603969001/50000000000000 : ℝ)^391
        have hw : |(-2118830471/10000000000 : ℝ)|=(2118830471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696653951/5000000000 : ℝ)|^519 ≤ (22031486767353/50000000000000 : ℝ)^391
        have hw : |(2696653951/5000000000 : ℝ)|=(2696653951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s7_6 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312408169/10000000000 : ℝ)*x 0 + (5393307921/10000000000 : ℝ)*x 1 + (-105941523/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312408169/10000000000 : ℝ)^519 ≤ (10796954599219/25000000000000 : ℝ)^391 := by
    have hnat : (5312408169 : ℕ)^519*25000000000000^391 ≤ 10796954599219^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312408169 10000000000 10796954599219 25000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393307921/10000000000 : ℝ)^519 ≤ (2753935858797/6250000000000 : ℝ)^391 := by
    have hnat : (5393307921 : ℕ)^519*6250000000000^391 ≤ 2753935858797^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393307921 10000000000 2753935858797 6250000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105941523/500000000 : ℝ)^519 ≤ (6374603925073/50000000000000 : ℝ)^391 := by
    have hnat : (105941523 : ℕ)^519*50000000000000^391 ≤ 6374603925073^391*500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105941523 500000000 6374603925073 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312408169/10000000000 : ℝ), (5393307921/10000000000 : ℝ), (-105941523/500000000 : ℝ)] ![(10796954599219/25000000000000 : ℝ), (2753935858797/6250000000000 : ℝ), (6374603925073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312408169/10000000000 : ℝ)|^519 ≤ (10796954599219/25000000000000 : ℝ)^391
        have hw : |(5312408169/10000000000 : ℝ)|=(5312408169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393307921/10000000000 : ℝ)|^519 ≤ (2753935858797/6250000000000 : ℝ)^391
        have hw : |(5393307921/10000000000 : ℝ)|=(5393307921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105941523/500000000 : ℝ)|^519 ≤ (6374603925073/50000000000000 : ℝ)^391
        have hw : |(-105941523/500000000 : ℝ)|=(105941523/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s7_7 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4369066489/10000000000 : ℝ)*x 0 + (449726097/1000000000 : ℝ)*x 1 + (4244554569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369066489/10000000000 : ℝ)^519 ≤ (33316872242013/100000000000000 : ℝ)^391 := by
    have hnat : (4369066489 : ℕ)^519*100000000000000^391 ≤ 33316872242013^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369066489 10000000000 33316872242013 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449726097/1000000000 : ℝ)^519 ≤ (6924129534791/20000000000000 : ℝ)^391 := by
    have hnat : (449726097 : ℕ)^519*20000000000000^391 ≤ 6924129534791^391*1000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449726097 1000000000 6924129534791 20000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4244554569/10000000000 : ℝ)^519 ≤ (32062480068451/100000000000000 : ℝ)^391 := by
    have hnat : (4244554569 : ℕ)^519*100000000000000^391 ≤ 32062480068451^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244554569 10000000000 32062480068451 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369066489/10000000000 : ℝ), (449726097/1000000000 : ℝ), (4244554569/10000000000 : ℝ)] ![(33316872242013/100000000000000 : ℝ), (6924129534791/20000000000000 : ℝ), (32062480068451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369066489/10000000000 : ℝ)|^519 ≤ (33316872242013/100000000000000 : ℝ)^391
        have hw : |(4369066489/10000000000 : ℝ)|=(4369066489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(449726097/1000000000 : ℝ)|^519 ≤ (6924129534791/20000000000000 : ℝ)^391
        have hw : |(449726097/1000000000 : ℝ)|=(449726097/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4244554569/10000000000 : ℝ)|^519 ≤ (32062480068451/100000000000000 : ℝ)^391
        have hw : |(4244554569/10000000000 : ℝ)|=(4244554569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1111_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (351/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1413/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11311/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (877/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (351/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1413/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (351/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1413/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (351/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1413/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (351/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1413/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (351/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1413/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (351/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1413/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1413/12500 : ℝ) ^ (8303/2048 : ℝ) ≤ (7254116430251999/50000000000000000000 : ℝ) := by
    have hpowers : (1413/12500 : ℝ)^8303 ≤ (7254116430251999/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1413 : ℕ)^8303*50000000000000000000^2048 ≤ 7254116430251999^2048*12500^8303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1413 12500 7254116430251999 50000000000000000000 8303 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1413/12500 : ℝ)) (X := (7254116430251999/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (351/2500 : ℝ) ^ (8303/2048 : ℝ) ≤ (34934649838616803/100000000000000000000 : ℝ) := by
    have hpowers : (351/2500 : ℝ)^8303 ≤ (34934649838616803/100000000000000000000 : ℝ)^2048 := by
      have hnat : (351 : ℕ)^8303*100000000000000000000^2048 ≤ 34934649838616803^2048*2500^8303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        351 2500 34934649838616803 100000000000000000000 8303 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (351/2500 : ℝ)) (X := (34934649838616803/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007254116430251999/25000000000000000000 : ℝ) ≤ (10000715635648157/10000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (25007254116430251999/25000000000000000000 : ℝ)^2048 ≤ (10000715635648157/10000000000000000 : ℝ)^8303 := by
      have hnat : (25007254116430251999 : ℕ)^2048*10000000000000000^8303 ≤ 10000715635648157^8303*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007254116430251999 25000000000000000000 10000715635648157 10000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000715635648157/10000000000000000 : ℝ)) (X := (25007254116430251999/25000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049442882699120801/100000000000000000000 : ℝ) ≤ (1000121932037859/1000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (100049442882699120801/100000000000000000000 : ℝ)^2048 ≤ (1000121932037859/1000000000000000 : ℝ)^8303 := by
      have hnat : (100049442882699120801 : ℕ)^2048*1000000000000000^8303 ≤ 1000121932037859^8303*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049442882699120801 100000000000000000000 1000121932037859 1000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000121932037859/1000000000000000 : ℝ)) (X := (100049442882699120801/100000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034934649838616803/50000000000000000000 : ℝ) ≤ (10001723005109023/10000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (50034934649838616803/50000000000000000000 : ℝ)^2048 ≤ (10001723005109023/10000000000000000 : ℝ)^8303 := by
      have hnat : (50034934649838616803 : ℕ)^2048*10000000000000000^8303 ≤ 10001723005109023^8303*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034934649838616803 50000000000000000000 10001723005109023 10000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001723005109023/10000000000000000 : ℝ)) (X := (50034934649838616803/50000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7254116430251999/50000000000000000000 : ℝ) ≤ ((94967259287318501/95000000000000000 : ℝ)+2*(503684730433/273600000000000 : ℝ)*(1413/12500 : ℝ))^(8303/2048 : ℝ) := by
    rw [show (94967259287318501/95000000000000000 : ℝ)+2*(503684730433/273600000000000 : ℝ)*(1413/12500 : ℝ)=(10000715635648157/10000000000000000 : ℝ) by norm_num, show 1+2*(7254116430251999/50000000000000000000 : ℝ)=(25007254116430251999/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34934649838616803/100000000000000000000 : ℝ)+(7254116430251999/50000000000000000000 : ℝ) ≤ ((94967259287318501/95000000000000000 : ℝ)+(503684730433/273600000000000 : ℝ)*((351/2500 : ℝ)+(1413/12500 : ℝ)))^(8303/2048 : ℝ) := by
    rw [show (94967259287318501/95000000000000000 : ℝ)+(503684730433/273600000000000 : ℝ)*((351/2500 : ℝ)+(1413/12500 : ℝ))=(1000121932037859/1000000000000000 : ℝ) by norm_num, show 1+(34934649838616803/100000000000000000000 : ℝ)+(7254116430251999/50000000000000000000 : ℝ)=(100049442882699120801/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34934649838616803/100000000000000000000 : ℝ) ≤ ((94967259287318501/95000000000000000 : ℝ)+2*(503684730433/273600000000000 : ℝ)*(351/2500 : ℝ))^(8303/2048 : ℝ) := by
    rw [show (94967259287318501/95000000000000000 : ℝ)+2*(503684730433/273600000000000 : ℝ)*(351/2500 : ℝ)=(10001723005109023/10000000000000000 : ℝ) by norm_num, show 1+2*(34934649838616803/100000000000000000000 : ℝ)=(50034934649838616803/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (94967259287318501/95000000000000000 : ℝ)*(X 1 0+X 2 0)+(503684730433/273600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (1413/12500 : ℝ)) (hi := (351/2500 : ℝ)) (c := (94967259287318501/95000000000000000 : ℝ)) (alpha := (503684730433/273600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (94967259287318501/95000000000000000 : ℝ)*(X 0 1+X 2 1)+(503684730433/273600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (1413/12500 : ℝ)) (hi := (351/2500 : ℝ)) (c := (94967259287318501/95000000000000000 : ℝ)) (alpha := (503684730433/273600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (94967259287318501/95000000000000000 : ℝ)*(X 0 2+X 1 2)+(503684730433/273600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (1413/12500 : ℝ)) (hi := (351/2500 : ℝ)) (c := (94967259287318501/95000000000000000 : ℝ)) (alpha := (503684730433/273600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-218179347/1000000000 : ℝ)*X 0 0+(5393631543/10000000000 : ℝ)*X 0 1+(5265187123/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((66810931/125000000 : ℝ)*X 1 0+(-1123475619/5000000000 : ℝ)*X 1 1+(42121497/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66810931/125000000 : ℝ)*X 2 0+(2632593563/5000000000 : ℝ)*X 2 1+(-561737809/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4369056659/10000000000 : ℝ)*X 0 0+(4243914631/10000000000 : ℝ)*X 0 1+(4497898613/10000000000 : ℝ)*X 0 2+(4369056659/10000000000 : ℝ)*X 1 0+(4243914631/10000000000 : ℝ)*X 1 1+(4497898613/10000000000 : ℝ)*X 1 2+(4369056659/10000000000 : ℝ)*X 2 0+(4243914631/10000000000 : ℝ)*X 2 1+(4497898613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1090899227/5000000000 : ℝ)*X 0 0+(5265509597/10000000000 : ℝ)*X 0 1+(5393307891/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312408181/10000000000 : ℝ)*X 1 0+(-2118830471/10000000000 : ℝ)*X 1 1+(2696653951/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312408169/10000000000 : ℝ)*X 2 0+(5393307921/10000000000 : ℝ)*X 2 1+(-105941523/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4369066489/10000000000 : ℝ)*X 0 0+(449726097/1000000000 : ℝ)*X 0 1+(4244554569/10000000000 : ℝ)*X 0 2+(4369066489/10000000000 : ℝ)*X 1 0+(449726097/1000000000 : ℝ)*X 1 1+(4244554569/10000000000 : ℝ)*X 1 2+(4369066489/10000000000 : ℝ)*X 2 0+(449726097/1000000000 : ℝ)*X 2 1+(4244554569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21105912238273152532496913/2375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (443307437/25000000000000 : ℝ)*(base19) + (330890077/20000000000000 : ℝ)*(base23) + (31743039/50000000000000 : ℝ)*(lower2) + (11185029/5000000000000 : ℝ)*(upper3) + (27658493/20000000000000 : ℝ)*(upper5) + (2930718324715077/50000000000000 : ℝ)*(major0) + (2930718324715077/50000000000000 : ℝ)*(major1) + (2930718324715077/50000000000000 : ℝ)*(major2) + (1946379722848519/25000000000000 : ℝ)*(sp0) + (1946391327697869/25000000000000 : ℝ)*(sp1) + (7785565429570839/100000000000000 : ℝ)*(sp2) + (984319947892391/25000000000000 : ℝ)*(sp3) + (12048156787/25000000000000 : ℝ)*(sp4) + (26127046181/100000000000000 : ℝ)*(sp7) + (1968652959307873/50000000000000 : ℝ)*(f.failure) + (973195885502653/12500000000000 : ℝ)*(f.sum) + (5897100897007/2280000000000000000000000000 : ℝ)*base65 + (102159363581995303/7125000000000000000000000000000 : ℝ)*base67 + (22039709538379697/7125000000000000000000000000000 : ℝ)*base70 + (61299180149620303/7125000000000000000000000000000 : ℝ)*base71 + (3948711180967/2280000000000000000000000000 : ℝ)*base73 + (168967017688120303/7125000000000000000000000000000 : ℝ)*base75 + (18197516939620303/7125000000000000000000000000000 : ℝ)*base77 + (36508615440745303/7125000000000000000000000000000 : ℝ)*base79 + (2551248595313/2280000000000000000000000000 : ℝ)*base82 + (52676933/5000000000000000000000 : ℝ)*base89 + (52676933/5000000000000000000000 : ℝ)*base91 + (52676933/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5058227613623002122827537/750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63151519/5000000000000 : ℝ)*(base19) + (667971303/50000000000000 : ℝ)*(base23) + (30720701/20000000000000 : ℝ)*(upper3) + (7578519/20000000000000 : ℝ)*(lower4) + (13903731/10000000000000 : ℝ)*(upper5) + (5890995154938079/100000000000000 : ℝ)*(major0) + (5890995154938079/100000000000000 : ℝ)*(major1) + (5890995154938079/100000000000000 : ℝ)*(major2) + (3409618847/10000000000000 : ℝ)*(sp1) + (37247487953/100000000000000 : ℝ)*(sp2) + (7824828816023003/100000000000000 : ℝ)*(sp4) + (7824793456804153/100000000000000 : ℝ)*(sp5) + (1956197558148111/25000000000000 : ℝ)*(sp6) + (1978580634521517/50000000000000 : ℝ)*(sp7) + (1978580634521517/50000000000000 : ℝ)*(f.failure) + (7824828816023003/100000000000000 : ℝ)*(f.sum) + (85611442246687/13680000000000000000000000000 : ℝ)*base65 + (16196128829353457/42750000000000000000000000000000 : ℝ)*base68 + (27413306568646543/42750000000000000000000000000000 : ℝ)*base69 + (12631643343646543/42750000000000000000000000000000 : ℝ)*base71 + (2429370598447/13680000000000000000000000000 : ℝ)*base73 + (944770633270396543/42750000000000000000000000000000 : ℝ)*base75 + (330469634770396543/42750000000000000000000000000000 : ℝ)*base77 + (116483531650396543/42750000000000000000000000000000 : ℝ)*base79 + (22049128909567/13680000000000000000000000000 : ℝ)*base81 + (6471743/5000000000000000000000 : ℝ)*base90 + (6471743/5000000000000000000000 : ℝ)*base92 + (6471743/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1111_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (351/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1413/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (877/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1111_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1111_s8_0 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-545450613/2500000000 : ℝ)*x 0 + (1348388237/2500000000 : ℝ)*x 1 + (5265259609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545450613/2500000000 : ℝ)^519 ≤ (2650917737173/20000000000000 : ℝ)^391 := by
    have hnat : (545450613 : ℕ)^519*20000000000000^391 ≤ 2650917737173^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545450613 2500000000 2650917737173 20000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348388237/2500000000 : ℝ)^519 ≤ (44065630953701/100000000000000 : ℝ)^391 := by
    have hnat : (1348388237 : ℕ)^519*100000000000000^391 ≤ 44065630953701^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348388237 2500000000 44065630953701 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265259609/10000000000 : ℝ)^519 ≤ (21339890174967/50000000000000 : ℝ)^391 := by
    have hnat : (5265259609 : ℕ)^519*50000000000000^391 ≤ 21339890174967^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265259609 10000000000 21339890174967 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-545450613/2500000000 : ℝ), (1348388237/2500000000 : ℝ), (5265259609/10000000000 : ℝ)] ![(2650917737173/20000000000000 : ℝ), (44065630953701/100000000000000 : ℝ), (21339890174967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-545450613/2500000000 : ℝ)|^519 ≤ (2650917737173/20000000000000 : ℝ)^391
        have hw : |(-545450613/2500000000 : ℝ)|=(545450613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348388237/2500000000 : ℝ)|^519 ≤ (44065630953701/100000000000000 : ℝ)^391
        have hw : |(1348388237/2500000000 : ℝ)|=(1348388237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265259609/10000000000 : ℝ)|^519 ≤ (21339890174967/50000000000000 : ℝ)^391
        have hw : |(5265259609/10000000000 : ℝ)|=(5265259609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s8_1 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1068970807/2000000000 : ℝ)*x 0 + (-2246882543/10000000000 : ℝ)*x 1 + (1316314913/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068970807/2000000000 : ℝ)^519 ≤ (4353829026031/10000000000000 : ℝ)^391 := by
    have hnat : (1068970807 : ℕ)^519*10000000000000^391 ≤ 4353829026031^391*2000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068970807 2000000000 4353829026031 10000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246882543/10000000000 : ℝ)^519 ≤ (13781928904653/100000000000000 : ℝ)^391 := by
    have hnat : (2246882543 : ℕ)^519*100000000000000^391 ≤ 13781928904653^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246882543 10000000000 13781928904653 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316314913/2500000000 : ℝ)^519 ≤ (21339890406297/50000000000000 : ℝ)^391 := by
    have hnat : (1316314913 : ℕ)^519*50000000000000^391 ≤ 21339890406297^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316314913 2500000000 21339890406297 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068970807/2000000000 : ℝ), (-2246882543/10000000000 : ℝ), (1316314913/2500000000 : ℝ)] ![(4353829026031/10000000000000 : ℝ), (13781928904653/100000000000000 : ℝ), (21339890406297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068970807/2000000000 : ℝ)|^519 ≤ (4353829026031/10000000000000 : ℝ)^391
        have hw : |(1068970807/2000000000 : ℝ)|=(1068970807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2246882543/10000000000 : ℝ)|^519 ≤ (13781928904653/100000000000000 : ℝ)^391
        have hw : |(-2246882543/10000000000 : ℝ)|=(2246882543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316314913/2500000000 : ℝ)|^519 ≤ (21339890406297/50000000000000 : ℝ)^391
        have hw : |(1316314913/2500000000 : ℝ)|=(1316314913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s8_2 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1068970833/2000000000 : ℝ)*x 0 + (5265259539/10000000000 : ℝ)*x 1 + (-56172063/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068970833/2000000000 : ℝ)^519 ≤ (8707658333187/20000000000000 : ℝ)^391 := by
    have hnat : (1068970833 : ℕ)^519*20000000000000^391 ≤ 8707658333187^391*2000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068970833 2000000000 8707658333187 20000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265259539/10000000000 : ℝ)^519 ≤ (1333743112399/3125000000000 : ℝ)^391 := by
    have hnat : (5265259539 : ℕ)^519*3125000000000^391 ≤ 1333743112399^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265259539 10000000000 1333743112399 3125000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56172063/250000000 : ℝ)^519 ≤ (861370544837/6250000000000 : ℝ)^391 := by
    have hnat : (56172063 : ℕ)^519*6250000000000^391 ≤ 861370544837^391*250000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56172063 250000000 861370544837 6250000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068970833/2000000000 : ℝ), (5265259539/10000000000 : ℝ), (-56172063/250000000 : ℝ)] ![(8707658333187/20000000000000 : ℝ), (1333743112399/3125000000000 : ℝ), (861370544837/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068970833/2000000000 : ℝ)|^519 ≤ (8707658333187/20000000000000 : ℝ)^391
        have hw : |(1068970833/2000000000 : ℝ)|=(1068970833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265259539/10000000000 : ℝ)|^519 ≤ (1333743112399/3125000000000 : ℝ)^391
        have hw : |(5265259539/10000000000 : ℝ)|=(5265259539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-56172063/250000000 : ℝ)|^519 ≤ (861370544837/6250000000000 : ℝ)^391
        have hw : |(-56172063/250000000 : ℝ)|=(56172063/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s8_3 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4369060399/10000000000 : ℝ)*x 0 + (4244063699/10000000000 : ℝ)*x 1 + (89954973/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369060399/10000000000 : ℝ)^519 ≤ (3331681059907/10000000000000 : ℝ)^391 := by
    have hnat : (4369060399 : ℕ)^519*10000000000000^391 ≤ 3331681059907^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369060399 10000000000 3331681059907 10000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4244063699/10000000000 : ℝ)^519 ≤ (32057558382923/100000000000000 : ℝ)^391 := by
    have hnat : (4244063699 : ℕ)^519*100000000000000^391 ≤ 32057558382923^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244063699 10000000000 32057558382923 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89954973/200000000 : ℝ)^519 ≤ (17312815506023/50000000000000 : ℝ)^391 := by
    have hnat : (89954973 : ℕ)^519*50000000000000^391 ≤ 17312815506023^391*200000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89954973 200000000 17312815506023 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369060399/10000000000 : ℝ), (4244063699/10000000000 : ℝ), (89954973/200000000 : ℝ)] ![(3331681059907/10000000000000 : ℝ), (32057558382923/100000000000000 : ℝ), (17312815506023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369060399/10000000000 : ℝ)|^519 ≤ (3331681059907/10000000000000 : ℝ)^391
        have hw : |(4369060399/10000000000 : ℝ)|=(4369060399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4244063699/10000000000 : ℝ)|^519 ≤ (32057558382923/100000000000000 : ℝ)^391
        have hw : |(4244063699/10000000000 : ℝ)|=(4244063699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(89954973/200000000 : ℝ)|^519 ≤ (17312815506023/50000000000000 : ℝ)^391
        have hw : |(89954973/200000000 : ℝ)|=(89954973/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s8_4 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-272725923/1250000000 : ℝ)*x 0 + (5265581313/10000000000 : ℝ)*x 1 + (1078646019/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272725923/1250000000 : ℝ)^519 ≤ (1656828557087/12500000000000 : ℝ)^391 := by
    have hnat : (272725923 : ℕ)^519*12500000000000^391 ≤ 1656828557087^391*1250000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272725923 1250000000 1656828557087 12500000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265581313/10000000000 : ℝ)^519 ≤ (42683241765887/100000000000000 : ℝ)^391 := by
    have hnat : (5265581313 : ℕ)^519*100000000000000^391 ≤ 42683241765887^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265581313 10000000000 42683241765887 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078646019/2000000000 : ℝ)^519 ≤ (44062129759359/100000000000000 : ℝ)^391 := by
    have hnat : (1078646019 : ℕ)^519*100000000000000^391 ≤ 44062129759359^391*2000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078646019 2000000000 44062129759359 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-272725923/1250000000 : ℝ), (5265581313/10000000000 : ℝ), (1078646019/2000000000 : ℝ)] ![(1656828557087/12500000000000 : ℝ), (42683241765887/100000000000000 : ℝ), (44062129759359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-272725923/1250000000 : ℝ)|^519 ≤ (1656828557087/12500000000000 : ℝ)^391
        have hw : |(-272725923/1250000000 : ℝ)|=(272725923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265581313/10000000000 : ℝ)|^519 ≤ (42683241765887/100000000000000 : ℝ)^391
        have hw : |(5265581313/10000000000 : ℝ)|=(5265581313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078646019/2000000000 : ℝ)|^519 ≤ (44062129759359/100000000000000 : ℝ)^391
        have hw : |(1078646019/2000000000 : ℝ)|=(1078646019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s8_5 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312426423/10000000000 : ℝ)*x 0 + (-1059455597/5000000000 : ℝ)*x 1 + (5393230297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312426423/10000000000 : ℝ)^519 ≤ (43188015375329/100000000000000 : ℝ)^391 := by
    have hnat : (5312426423 : ℕ)^519*100000000000000^391 ≤ 43188015375329^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312426423 10000000000 43188015375329 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059455597/5000000000 : ℝ)^519 ≤ (199216447931/1562500000000 : ℝ)^391 := by
    have hnat : (1059455597 : ℕ)^519*1562500000000^391 ≤ 199216447931^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059455597 5000000000 199216447931 1562500000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393230297/10000000000 : ℝ)^519 ≤ (2753883246871/6250000000000 : ℝ)^391 := by
    have hnat : (5393230297 : ℕ)^519*6250000000000^391 ≤ 2753883246871^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393230297 10000000000 2753883246871 6250000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312426423/10000000000 : ℝ), (-1059455597/5000000000 : ℝ), (5393230297/10000000000 : ℝ)] ![(43188015375329/100000000000000 : ℝ), (199216447931/1562500000000 : ℝ), (2753883246871/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312426423/10000000000 : ℝ)|^519 ≤ (43188015375329/100000000000000 : ℝ)^391
        have hw : |(5312426423/10000000000 : ℝ)|=(5312426423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1059455597/5000000000 : ℝ)|^519 ≤ (199216447931/1562500000000 : ℝ)^391
        have hw : |(-1059455597/5000000000 : ℝ)|=(1059455597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393230297/10000000000 : ℝ)|^519 ≤ (2753883246871/6250000000000 : ℝ)^391
        have hw : |(5393230297/10000000000 : ℝ)|=(5393230297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s8_6 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312425373/10000000000 : ℝ)*x 0 + (5393230219/10000000000 : ℝ)*x 1 + (-1059456359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312425373/10000000000 : ℝ)^519 ≤ (43188004044799/100000000000000 : ℝ)^391 := by
    have hnat : (5312425373 : ℕ)^519*100000000000000^391 ≤ 43188004044799^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312425373 10000000000 43188004044799 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393230219/10000000000 : ℝ)^519 ≤ (4406213110407/10000000000000 : ℝ)^391 := by
    have hnat : (5393230219 : ℕ)^519*10000000000000^391 ≤ 4406213110407^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393230219 10000000000 4406213110407 10000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059456359/5000000000 : ℝ)^519 ≤ (6374932419877/50000000000000 : ℝ)^391 := by
    have hnat : (1059456359 : ℕ)^519*50000000000000^391 ≤ 6374932419877^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059456359 5000000000 6374932419877 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312425373/10000000000 : ℝ), (5393230219/10000000000 : ℝ), (-1059456359/5000000000 : ℝ)] ![(43188004044799/100000000000000 : ℝ), (4406213110407/10000000000000 : ℝ), (6374932419877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312425373/10000000000 : ℝ)|^519 ≤ (43188004044799/100000000000000 : ℝ)^391
        have hw : |(5312425373/10000000000 : ℝ)|=(5312425373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393230219/10000000000 : ℝ)|^519 ≤ (4406213110407/10000000000000 : ℝ)^391
        have hw : |(5393230219/10000000000 : ℝ)|=(5393230219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1059456359/5000000000 : ℝ)|^519 ≤ (6374932419877/50000000000000 : ℝ)^391
        have hw : |(-1059456359/5000000000 : ℝ)|=(1059456359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s8_7 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4369069441/10000000000 : ℝ)*x 0 + (4497112543/10000000000 : ℝ)*x 1 + (4244702851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369069441/10000000000 : ℝ)^519 ≤ (33316902122149/100000000000000 : ℝ)^391 := by
    have hnat : (4369069441 : ℕ)^519*100000000000000^391 ≤ 33316902122149^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369069441 10000000000 33316902122149 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497112543/10000000000 : ℝ)^519 ≤ (34619131013853/100000000000000 : ℝ)^391 := by
    have hnat : (4497112543 : ℕ)^519*100000000000000^391 ≤ 34619131013853^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497112543 10000000000 34619131013853 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4244702851/10000000000 : ℝ)^519 ≤ (6412793369553/20000000000000 : ℝ)^391 := by
    have hnat : (4244702851 : ℕ)^519*20000000000000^391 ≤ 6412793369553^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244702851 10000000000 6412793369553 20000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369069441/10000000000 : ℝ), (4497112543/10000000000 : ℝ), (4244702851/10000000000 : ℝ)] ![(33316902122149/100000000000000 : ℝ), (34619131013853/100000000000000 : ℝ), (6412793369553/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369069441/10000000000 : ℝ)|^519 ≤ (33316902122149/100000000000000 : ℝ)^391
        have hw : |(4369069441/10000000000 : ℝ)|=(4369069441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497112543/10000000000 : ℝ)|^519 ≤ (34619131013853/100000000000000 : ℝ)^391
        have hw : |(4497112543/10000000000 : ℝ)|=(4497112543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4244702851/10000000000 : ℝ)|^519 ≤ (6412793369553/20000000000000 : ℝ)^391
        have hw : |(4244702851/10000000000 : ℝ)|=(4244702851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1111_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (877/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11313/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1403/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (877/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (877/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (877/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (877/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (877/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (877/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11311/100000 : ℝ) ^ (8303/2048 : ℝ) ≤ (14544691139788759/100000000000000000000 : ℝ) := by
    have hpowers : (11311/100000 : ℝ)^8303 ≤ (14544691139788759/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11311 : ℕ)^8303*100000000000000000000^2048 ≤ 14544691139788759^2048*100000^8303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11311 100000 14544691139788759 100000000000000000000 8303 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11311/100000 : ℝ)) (X := (14544691139788759/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (877/6250 : ℝ) ^ (8303/2048 : ℝ) ≤ (34854018022007609/100000000000000000000 : ℝ) := by
    have hpowers : (877/6250 : ℝ)^8303 ≤ (34854018022007609/100000000000000000000 : ℝ)^2048 := by
      have hnat : (877 : ℕ)^8303*100000000000000000000^2048 ≤ 34854018022007609^2048*6250^8303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        877 6250 34854018022007609 100000000000000000000 8303 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (877/6250 : ℝ)) (X := (34854018022007609/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014544691139788759/50000000000000000000 : ℝ) ≤ (10000717433798657/10000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (50014544691139788759/50000000000000000000 : ℝ)^2048 ≤ (10000717433798657/10000000000000000 : ℝ)^8303 := by
      have hnat : (50014544691139788759 : ℕ)^2048*10000000000000000^8303 ≤ 10000717433798657^8303*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014544691139788759 50000000000000000000 10000717433798657 10000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000717433798657/10000000000000000 : ℝ)) (X := (50014544691139788759/50000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253087419322612273/6250000000000000000 : ℝ) ≤ (5000609115604583/5000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (6253087419322612273/6250000000000000000 : ℝ)^2048 ≤ (5000609115604583/5000000000000000 : ℝ)^8303 := by
      have hnat : (6253087419322612273 : ℕ)^2048*5000000000000000^8303 ≤ 5000609115604583^8303*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253087419322612273 6250000000000000000 5000609115604583 5000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000609115604583/5000000000000000 : ℝ)) (X := (6253087419322612273/6250000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034854018022007609/50000000000000000000 : ℝ) ≤ (400068761144787/400000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (50034854018022007609/50000000000000000000 : ℝ)^2048 ≤ (400068761144787/400000000000000 : ℝ)^8303 := by
      have hnat : (50034854018022007609 : ℕ)^2048*400000000000000^8303 ≤ 400068761144787^8303*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034854018022007609 50000000000000000000 400068761144787 400000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400068761144787/400000000000000 : ℝ)) (X := (50034854018022007609/50000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14544691139788759/100000000000000000000 : ℝ) ≤ ((27200623098345611099/27210000000000000000 : ℝ)+2*(500797410509/272100000000000 : ℝ)*(11311/100000 : ℝ))^(8303/2048 : ℝ) := by
    rw [show (27200623098345611099/27210000000000000000 : ℝ)+2*(500797410509/272100000000000 : ℝ)*(11311/100000 : ℝ)=(10000717433798657/10000000000000000 : ℝ) by norm_num, show 1+2*(14544691139788759/100000000000000000000 : ℝ)=(50014544691139788759/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34854018022007609/100000000000000000000 : ℝ)+(14544691139788759/100000000000000000000 : ℝ) ≤ ((27200623098345611099/27210000000000000000 : ℝ)+(500797410509/272100000000000 : ℝ)*((877/6250 : ℝ)+(11311/100000 : ℝ)))^(8303/2048 : ℝ) := by
    rw [show (27200623098345611099/27210000000000000000 : ℝ)+(500797410509/272100000000000 : ℝ)*((877/6250 : ℝ)+(11311/100000 : ℝ))=(5000609115604583/5000000000000000 : ℝ) by norm_num, show 1+(34854018022007609/100000000000000000000 : ℝ)+(14544691139788759/100000000000000000000 : ℝ)=(6253087419322612273/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34854018022007609/100000000000000000000 : ℝ) ≤ ((27200623098345611099/27210000000000000000 : ℝ)+2*(500797410509/272100000000000 : ℝ)*(877/6250 : ℝ))^(8303/2048 : ℝ) := by
    rw [show (27200623098345611099/27210000000000000000 : ℝ)+2*(500797410509/272100000000000 : ℝ)*(877/6250 : ℝ)=(400068761144787/400000000000000 : ℝ) by norm_num, show 1+2*(34854018022007609/100000000000000000000 : ℝ)=(50034854018022007609/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27200623098345611099/27210000000000000000 : ℝ)*(X 1 0+X 2 0)+(500797410509/272100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (877/6250 : ℝ)) (c := (27200623098345611099/27210000000000000000 : ℝ)) (alpha := (500797410509/272100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27200623098345611099/27210000000000000000 : ℝ)*(X 0 1+X 2 1)+(500797410509/272100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (877/6250 : ℝ)) (c := (27200623098345611099/27210000000000000000 : ℝ)) (alpha := (500797410509/272100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27200623098345611099/27210000000000000000 : ℝ)*(X 0 2+X 1 2)+(500797410509/272100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (877/6250 : ℝ)) (c := (27200623098345611099/27210000000000000000 : ℝ)) (alpha := (500797410509/272100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-545450613/2500000000 : ℝ)*X 0 0+(1348388237/2500000000 : ℝ)*X 0 1+(5265259609/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068970807/2000000000 : ℝ)*X 1 0+(-2246882543/10000000000 : ℝ)*X 1 1+(1316314913/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068970833/2000000000 : ℝ)*X 2 0+(5265259539/10000000000 : ℝ)*X 2 1+(-56172063/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4369060399/10000000000 : ℝ)*X 0 0+(4244063699/10000000000 : ℝ)*X 0 1+(89954973/200000000 : ℝ)*X 0 2+(4369060399/10000000000 : ℝ)*X 1 0+(4244063699/10000000000 : ℝ)*X 1 1+(89954973/200000000 : ℝ)*X 1 2+(4369060399/10000000000 : ℝ)*X 2 0+(4244063699/10000000000 : ℝ)*X 2 1+(89954973/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-272725923/1250000000 : ℝ)*X 0 0+(5265581313/10000000000 : ℝ)*X 0 1+(1078646019/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312426423/10000000000 : ℝ)*X 1 0+(-1059455597/5000000000 : ℝ)*X 1 1+(5393230297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312425373/10000000000 : ℝ)*X 2 0+(5393230219/10000000000 : ℝ)*X 2 1+(-1059456359/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4369069441/10000000000 : ℝ)*X 0 0+(4497112543/10000000000 : ℝ)*X 0 1+(4244702851/10000000000 : ℝ)*X 0 2+(4369069441/10000000000 : ℝ)*X 1 0+(4497112543/10000000000 : ℝ)*X 1 1+(4244702851/10000000000 : ℝ)*X 1 2+(4369069441/10000000000 : ℝ)*X 2 0+(4497112543/10000000000 : ℝ)*X 2 1+(4244702851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (145678695414814335477765931/28343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (95261767/12500000000000 : ℝ)*(base19) + (419156469/50000000000000 : ℝ)*(base23) + (116639479/100000000000000 : ℝ)*(upper3) + (30296477/50000000000000 : ℝ)*(upper4) + (106825843/100000000000000 : ℝ)*(upper5) + (366768437689969/6250000000000 : ℝ)*(major0) + (366768437689969/6250000000000 : ℝ)*(major1) + (366768437689969/6250000000000 : ℝ)*(major2) + (7794655249615813/100000000000000 : ℝ)*(sp0) + (7794676188573771/100000000000000 : ℝ)*(sp1) + (7794676112354969/100000000000000 : ℝ)*(sp2) + (246369008727919/6250000000000 : ℝ)*(sp3) + (4340210419/20000000000000 : ℝ)*(sp4) + (8744440669/100000000000000 : ℝ)*(sp7) + (985478221021843/25000000000000 : ℝ)*(f.failure) + (1948669237666977/25000000000000 : ℝ)*(f.sum) + (127709877270709/13605000000000000000000000000 : ℝ)*base66 + (1783849035911909069/170062500000000000000000000000000 : ℝ)*base68 + (627035653806846569/170062500000000000000000000000000 : ℝ)*base70 + (3223327776502409069/170062500000000000000000000000000 : ℝ)*base72 + (19783593728507/6802500000000000000000000000 : ℝ)*base74 + (1924175383221278431/170062500000000000000000000000000 : ℝ)*base75 + (365185958246159069/170062500000000000000000000000000 : ℝ)*base78 + (5301595538158590931/170062500000000000000000000000000 : ℝ)*base79 + (60428078558059/13605000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (8605697/2500000000000000000000 : ℝ)*base90 + (8605697/2500000000000000000000 : ℝ)*base92 + (8605697/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1254819083829768798761346309/226750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4182829/12500000000000 : ℝ)*(base19) + (12818549/6250000000000 : ℝ)*(upper1) + (657981347/100000000000000 : ℝ)*(upper2) + (159152629/50000000000000 : ℝ)*(lower4) + (58972271/100000000000000 : ℝ)*(lower5) + (5897904812466209/100000000000000 : ℝ)*(major0) + (5897904812466209/100000000000000 : ℝ)*(major1) + (5897904812466209/100000000000000 : ℝ)*(major2) + (23287448511/100000000000000 : ℝ)*(sp0) + (10576953689/20000000000000 : ℝ)*(sp1) + (3916991728048263/50000000000000 : ℝ)*(sp4) + (7833953825313961/100000000000000 : ℝ)*(sp5) + (3917003371772519/50000000000000 : ℝ)*(sp6) + (990450674230741/25000000000000 : ℝ)*(sp7) + (990450674230741/25000000000000 : ℝ)*(f.failure) + (3917003371772519/50000000000000 : ℝ)*(f.sum) + (21262286125259/13605000000000000000000000000 : ℝ)*base66 + (20471103970952953691/2721000000000000000000000000000000 : ℝ)*base67 + (19864603914137953691/2721000000000000000000000000000000 : ℝ)*base69 + (16416695106788953691/2721000000000000000000000000000000 : ℝ)*base71 + (26532369215167/6802500000000000000000000000 : ℝ)*base74 + (39833905856610046309/2721000000000000000000000000000000 : ℝ)*base76 + (49467778473572953691/2721000000000000000000000000000000 : ℝ)*base77 + (17758200970376953691/2721000000000000000000000000000000 : ℝ)*base79 + (54684484816981/13605000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (38077239/2500000000000000000000 : ℝ)*base90 + (38077239/2500000000000000000000 : ℝ)*base92 + (38077239/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1111_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (877/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1111_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1111_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1111_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1111_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1111_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1111_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

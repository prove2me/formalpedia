-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1078_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:48:23.335303+00:00
-- url     : https://prove2.me/submissions/084126d6-f2fe-4b2a-a4df-62b517840dd3

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
theorem support_rectangle_w1078_s9_0 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1098938243/5000000000 : ℝ)*x 0 + (67426473/125000000 : ℝ)*x 1 + (2632349079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098938243/5000000000 : ℝ)^8271 ≤ (6674602949699/50000000000000 : ℝ)^6223 := by
    have hnat : (1098938243 : ℕ)^8271*50000000000000^6223 ≤ 6674602949699^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098938243 5000000000 6674602949699 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67426473/125000000 : ℝ)^8271 ≤ (44024555762639/100000000000000 : ℝ)^6223 := by
    have hnat : (67426473 : ℕ)^8271*100000000000000^6223 ≤ 44024555762639^6223*125000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67426473 125000000 44024555762639 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632349079/5000000000 : ℝ)^8271 ≤ (21313119166791/50000000000000 : ℝ)^6223 := by
    have hnat : (2632349079 : ℕ)^8271*50000000000000^6223 ≤ 21313119166791^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632349079 5000000000 21313119166791 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1098938243/5000000000 : ℝ), (67426473/125000000 : ℝ), (2632349079/5000000000 : ℝ)] ![(6674602949699/50000000000000 : ℝ), (44024555762639/100000000000000 : ℝ), (21313119166791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1098938243/5000000000 : ℝ)|^8271 ≤ (6674602949699/50000000000000 : ℝ)^6223
        have hw : |(-1098938243/5000000000 : ℝ)|=(1098938243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67426473/125000000 : ℝ)|^8271 ≤ (44024555762639/100000000000000 : ℝ)^6223
        have hw : |(67426473/125000000 : ℝ)|=(67426473/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632349079/5000000000 : ℝ)|^8271 ≤ (21313119166791/50000000000000 : ℝ)^6223
        have hw : |(2632349079/5000000000 : ℝ)|=(2632349079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s9_1 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344942599/10000000000 : ℝ)*x 0 + (-2263536339/10000000000 : ℝ)*x 1 + (2632349079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344942599/10000000000 : ℝ)^8271 ≤ (43491925362077/100000000000000 : ℝ)^6223 := by
    have hnat : (5344942599 : ℕ)^8271*100000000000000^6223 ≤ 43491925362077^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344942599 10000000000 43491925362077 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2263536339/10000000000 : ℝ)^8271 ≤ (6940918145167/50000000000000 : ℝ)^6223 := by
    have hnat : (2263536339 : ℕ)^8271*50000000000000^6223 ≤ 6940918145167^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263536339 10000000000 6940918145167 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632349079/5000000000 : ℝ)^8271 ≤ (21313119166791/50000000000000 : ℝ)^6223 := by
    have hnat : (2632349079 : ℕ)^8271*50000000000000^6223 ≤ 21313119166791^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632349079 5000000000 21313119166791 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344942599/10000000000 : ℝ), (-2263536339/10000000000 : ℝ), (2632349079/5000000000 : ℝ)] ![(43491925362077/100000000000000 : ℝ), (6940918145167/50000000000000 : ℝ), (21313119166791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344942599/10000000000 : ℝ)|^8271 ≤ (43491925362077/100000000000000 : ℝ)^6223
        have hw : |(5344942599/10000000000 : ℝ)|=(5344942599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2263536339/10000000000 : ℝ)|^8271 ≤ (6940918145167/50000000000000 : ℝ)^6223
        have hw : |(-2263536339/10000000000 : ℝ)|=(2263536339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632349079/5000000000 : ℝ)|^8271 ≤ (21313119166791/50000000000000 : ℝ)^6223
        have hw : |(2632349079/5000000000 : ℝ)|=(2632349079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s9_2 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344942599/10000000000 : ℝ)*x 0 + (2632349079/5000000000 : ℝ)*x 1 + (-2263536339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344942599/10000000000 : ℝ)^8271 ≤ (43491925362077/100000000000000 : ℝ)^6223 := by
    have hnat : (5344942599 : ℕ)^8271*100000000000000^6223 ≤ 43491925362077^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344942599 10000000000 43491925362077 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632349079/5000000000 : ℝ)^8271 ≤ (21313119166791/50000000000000 : ℝ)^6223 := by
    have hnat : (2632349079 : ℕ)^8271*50000000000000^6223 ≤ 21313119166791^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632349079 5000000000 21313119166791 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2263536339/10000000000 : ℝ)^8271 ≤ (6940918145167/50000000000000 : ℝ)^6223 := by
    have hnat : (2263536339 : ℕ)^8271*50000000000000^6223 ≤ 6940918145167^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263536339 10000000000 6940918145167 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344942599/10000000000 : ℝ), (2632349079/5000000000 : ℝ), (-2263536339/10000000000 : ℝ)] ![(43491925362077/100000000000000 : ℝ), (21313119166791/50000000000000 : ℝ), (6940918145167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344942599/10000000000 : ℝ)|^8271 ≤ (43491925362077/100000000000000 : ℝ)^6223
        have hw : |(5344942599/10000000000 : ℝ)|=(5344942599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632349079/5000000000 : ℝ)|^8271 ≤ (21313119166791/50000000000000 : ℝ)^6223
        have hw : |(2632349079/5000000000 : ℝ)|=(2632349079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2263536339/10000000000 : ℝ)|^8271 ≤ (6940918145167/50000000000000 : ℝ)^6223
        have hw : |(-2263536339/10000000000 : ℝ)|=(2263536339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s9_3 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1093442667/2500000000 : ℝ)*x 0 + (265532033/625000000 : ℝ)*x 1 + (900552293/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093442667/2500000000 : ℝ)^8271 ≤ (4164579100771/12500000000000 : ℝ)^6223 := by
    have hnat : (1093442667 : ℕ)^8271*12500000000000^6223 ≤ 4164579100771^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093442667 2500000000 4164579100771 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265532033/625000000 : ℝ)^8271 ≤ (1602725080871/5000000000000 : ℝ)^6223 := by
    have hnat : (265532033 : ℕ)^8271*5000000000000^6223 ≤ 1602725080871^6223*625000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265532033 625000000 1602725080871 5000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900552293/2000000000 : ℝ)^8271 ≤ (17314432778311/50000000000000 : ℝ)^6223 := by
    have hnat : (900552293 : ℕ)^8271*50000000000000^6223 ≤ 17314432778311^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900552293 2000000000 17314432778311 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093442667/2500000000 : ℝ), (265532033/625000000 : ℝ), (900552293/2000000000 : ℝ)] ![(4164579100771/12500000000000 : ℝ), (1602725080871/5000000000000 : ℝ), (17314432778311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093442667/2500000000 : ℝ)|^8271 ≤ (4164579100771/12500000000000 : ℝ)^6223
        have hw : |(1093442667/2500000000 : ℝ)|=(1093442667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(265532033/625000000 : ℝ)|^8271 ≤ (1602725080871/5000000000000 : ℝ)^6223
        have hw : |(265532033/625000000 : ℝ)|=(265532033/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900552293/2000000000 : ℝ)|^8271 ≤ (17314432778311/50000000000000 : ℝ)^6223
        have hw : |(900552293/2000000000 : ℝ)|=(900552293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s9_4 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1098940757/5000000000 : ℝ)*x 0 + (5265022313/10000000000 : ℝ)*x 1 + (1348448129/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098940757/5000000000 : ℝ)^8271 ≤ (13349246488159/100000000000000 : ℝ)^6223 := by
    have hnat : (1098940757 : ℕ)^8271*100000000000000^6223 ≤ 13349246488159^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098940757 5000000000 13349246488159 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265022313/10000000000 : ℝ)^8271 ≤ (5328715834267/12500000000000 : ℝ)^6223 := by
    have hnat : (5265022313 : ℕ)^8271*12500000000000^6223 ≤ 5328715834267^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265022313 10000000000 5328715834267 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348448129/2500000000 : ℝ)^8271 ≤ (2751314176267/6250000000000 : ℝ)^6223 := by
    have hnat : (1348448129 : ℕ)^8271*6250000000000^6223 ≤ 2751314176267^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348448129 2500000000 2751314176267 6250000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1098940757/5000000000 : ℝ), (5265022313/10000000000 : ℝ), (1348448129/2500000000 : ℝ)] ![(13349246488159/100000000000000 : ℝ), (5328715834267/12500000000000 : ℝ), (2751314176267/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1098940757/5000000000 : ℝ)|^8271 ≤ (13349246488159/100000000000000 : ℝ)^6223
        have hw : |(-1098940757/5000000000 : ℝ)|=(1098940757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265022313/10000000000 : ℝ)|^8271 ≤ (5328715834267/12500000000000 : ℝ)^6223
        have hw : |(5265022313/10000000000 : ℝ)|=(5265022313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348448129/2500000000 : ℝ)|^8271 ≤ (2751314176267/6250000000000 : ℝ)^6223
        have hw : |(1348448129/2500000000 : ℝ)|=(1348448129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s9_5 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2186890273/5000000000 : ℝ)*x 0 + (1125531163/2500000000 : ℝ)*x 1 + (849830327/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186890273/5000000000 : ℝ)^8271 ≤ (33316732813651/100000000000000 : ℝ)^6223 := by
    have hnat : (2186890273 : ℕ)^8271*100000000000000^6223 ≤ 33316732813651^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186890273 5000000000 33316732813651 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125531163/2500000000 : ℝ)^8271 ≤ (4327794560051/12500000000000 : ℝ)^6223 := by
    have hnat : (1125531163 : ℕ)^8271*12500000000000^6223 ≤ 4327794560051^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125531163 2500000000 4327794560051 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849830327/2000000000 : ℝ)^8271 ≤ (32060910682323/100000000000000 : ℝ)^6223 := by
    have hnat : (849830327 : ℕ)^8271*100000000000000^6223 ≤ 32060910682323^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849830327 2000000000 32060910682323 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186890273/5000000000 : ℝ), (1125531163/2500000000 : ℝ), (849830327/2000000000 : ℝ)] ![(33316732813651/100000000000000 : ℝ), (4327794560051/12500000000000 : ℝ), (32060910682323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186890273/5000000000 : ℝ)|^8271 ≤ (33316732813651/100000000000000 : ℝ)^6223
        have hw : |(2186890273/5000000000 : ℝ)|=(2186890273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125531163/2500000000 : ℝ)|^8271 ≤ (4327794560051/12500000000000 : ℝ)^6223
        have hw : |(1125531163/2500000000 : ℝ)|=(1125531163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849830327/2000000000 : ℝ)|^8271 ≤ (32060910682323/100000000000000 : ℝ)^6223
        have hw : |(849830327/2000000000 : ℝ)|=(849830327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1078_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11269/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1401/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1401/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2817/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1401/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2817/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1401/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2817/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1401/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2817/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1401/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2817/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1401/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2817/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2817/25000 : ℝ) ^ (4135/1024 : ℝ) ≤ (14834607197066631/100000000000000000000 : ℝ) := by
    have hpowers : (2817/25000 : ℝ)^4135 ≤ (14834607197066631/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2817 : ℕ)^4135*100000000000000000000^1024 ≤ 14834607197066631^1024*25000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2817 25000 14834607197066631 100000000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2817/25000 : ℝ)) (X := (14834607197066631/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1401/10000 : ℝ) ^ (4135/1024 : ℝ) ≤ (17873674375479973/50000000000000000000 : ℝ) := by
    have hpowers : (1401/10000 : ℝ)^4135 ≤ (17873674375479973/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1401 : ℕ)^4135*50000000000000000000^1024 ≤ 17873674375479973^1024*10000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1401 10000 17873674375479973 50000000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1401/10000 : ℝ)) (X := (17873674375479973/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014834607197066631/50000000000000000000 : ℝ) ≤ (10000734652606843/10000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (50014834607197066631/50000000000000000000 : ℝ)^1024 ≤ (10000734652606843/10000000000000000 : ℝ)^4135 := by
      have hnat : (50014834607197066631 : ℕ)^1024*10000000000000000^4135 ≤ 10000734652606843^4135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014834607197066631 50000000000000000000 10000734652606843 10000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000734652606843/10000000000000000 : ℝ)) (X := (50014834607197066631/50000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050581955948026577/100000000000000000000 : ℝ) ≤ (10001252383800293/10000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (100050581955948026577/100000000000000000000 : ℝ)^1024 ≤ (10001252383800293/10000000000000000 : ℝ)^4135 := by
      have hnat : (100050581955948026577 : ℕ)^1024*10000000000000000^4135 ≤ 10001252383800293^4135*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050581955948026577 100000000000000000000 10001252383800293 10000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001252383800293/10000000000000000 : ℝ)) (X := (100050581955948026577/100000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017873674375479973/25000000000000000000 : ℝ) ≤ (10001770114993743/10000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (25017873674375479973/25000000000000000000 : ℝ)^1024 ≤ (10001770114993743/10000000000000000 : ℝ)^4135 := by
      have hnat : (25017873674375479973 : ℕ)^1024*10000000000000000^4135 ≤ 10001770114993743^4135*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017873674375479973 25000000000000000000 10001770114993743 10000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001770114993743/10000000000000000 : ℝ)) (X := (25017873674375479973/25000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14834607197066631/100000000000000000000 : ℝ) ≤ ((4568391137878729051/4570000000000000000 : ℝ)+2*(10354623869/5484000000000 : ℝ)*(2817/25000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (4568391137878729051/4570000000000000000 : ℝ)+2*(10354623869/5484000000000 : ℝ)*(2817/25000 : ℝ)=(10000734652606843/10000000000000000 : ℝ) by norm_num, show 1+2*(14834607197066631/100000000000000000000 : ℝ)=(50014834607197066631/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17873674375479973/50000000000000000000 : ℝ)+(14834607197066631/100000000000000000000 : ℝ) ≤ ((4568391137878729051/4570000000000000000 : ℝ)+(10354623869/5484000000000 : ℝ)*((1401/10000 : ℝ)+(2817/25000 : ℝ)))^(4135/1024 : ℝ) := by
    rw [show (4568391137878729051/4570000000000000000 : ℝ)+(10354623869/5484000000000 : ℝ)*((1401/10000 : ℝ)+(2817/25000 : ℝ))=(10001252383800293/10000000000000000 : ℝ) by norm_num, show 1+(17873674375479973/50000000000000000000 : ℝ)+(14834607197066631/100000000000000000000 : ℝ)=(100050581955948026577/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17873674375479973/50000000000000000000 : ℝ) ≤ ((4568391137878729051/4570000000000000000 : ℝ)+2*(10354623869/5484000000000 : ℝ)*(1401/10000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (4568391137878729051/4570000000000000000 : ℝ)+2*(10354623869/5484000000000 : ℝ)*(1401/10000 : ℝ)=(10001770114993743/10000000000000000 : ℝ) by norm_num, show 1+2*(17873674375479973/50000000000000000000 : ℝ)=(25017873674375479973/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4568391137878729051/4570000000000000000 : ℝ)*(X 1 0+X 2 0)+(10354623869/5484000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (2817/25000 : ℝ)) (hi := (1401/10000 : ℝ)) (c := (4568391137878729051/4570000000000000000 : ℝ)) (alpha := (10354623869/5484000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4568391137878729051/4570000000000000000 : ℝ)*(X 0 1+X 2 1)+(10354623869/5484000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (2817/25000 : ℝ)) (hi := (1401/10000 : ℝ)) (c := (4568391137878729051/4570000000000000000 : ℝ)) (alpha := (10354623869/5484000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4568391137878729051/4570000000000000000 : ℝ)*(X 0 2+X 1 2)+(10354623869/5484000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (2817/25000 : ℝ)) (hi := (1401/10000 : ℝ)) (c := (4568391137878729051/4570000000000000000 : ℝ)) (alpha := (10354623869/5484000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1098938243/5000000000 : ℝ)*X 0 0+(67426473/125000000 : ℝ)*X 0 1+(2632349079/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344942599/10000000000 : ℝ)*X 1 0+(-2263536339/10000000000 : ℝ)*X 1 1+(2632349079/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344942599/10000000000 : ℝ)*X 2 0+(2632349079/5000000000 : ℝ)*X 2 1+(-2263536339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1093442667/2500000000 : ℝ)*X 0 0+(265532033/625000000 : ℝ)*X 0 1+(900552293/2000000000 : ℝ)*X 0 2+(1093442667/2500000000 : ℝ)*X 1 0+(265532033/625000000 : ℝ)*X 1 1+(900552293/2000000000 : ℝ)*X 1 2+(1093442667/2500000000 : ℝ)*X 2 0+(265532033/625000000 : ℝ)*X 2 1+(900552293/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1098940757/5000000000 : ℝ)*X 0 0+(5265022313/10000000000 : ℝ)*X 0 1+(1348448129/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2186890273/5000000000 : ℝ)*X 0 0+(1125531163/2500000000 : ℝ)*X 0 1+(849830327/2000000000 : ℝ)*X 0 2+(2186890273/5000000000 : ℝ)*X 1 0+(1125531163/2500000000 : ℝ)*X 1 1+(849830327/2000000000 : ℝ)*X 1 2+(2186890273/5000000000 : ℝ)*X 2 0+(1125531163/2500000000 : ℝ)*X 2 1+(849830327/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57341043610163428899780311/28562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (403721229/100000000000000 : ℝ)*(base19) + (376256951/100000000000000 : ℝ)*(base23) + (14679499/100000000000000 : ℝ)*(lower2) + (50920733/100000000000000 : ℝ)*(upper3) + (30490779/100000000000000 : ℝ)*(upper5) + (1457498347553587/25000000000000 : ℝ)*(major0) + (1457498347553587/25000000000000 : ℝ)*(major1) + (1457498347553587/25000000000000 : ℝ)*(major2) + (482925712016457/6250000000000 : ℝ)*(sp0) + (7726821852956189/100000000000000 : ℝ)*(sp1) + (1931705470105117/25000000000000 : ℝ)*(sp2) + (1966579247148413/50000000000000 : ℝ)*(sp3) + (5432207053/50000000000000 : ℝ)*(sp4) + (5962535649/100000000000000 : ℝ)*(sp5) + (157326578273299/4000000000000 : ℝ)*(f.failure) + (3863411128338709/50000000000000 : ℝ)*(f.sum) + (4232275766083/685500000000000000000000000 : ℝ)*base66 + (803447742532189/342750000000000000000000000000000 : ℝ)*base68 + (5951823514235782189/342750000000000000000000000000000 : ℝ)*base70 + (1644834944099782189/342750000000000000000000000000000 : ℝ)*base72 + (1072789786399/274200000000000000000000000 : ℝ)*base74 + (905854542178282189/342750000000000000000000000000000 : ℝ)*base76 + (3282467408322532189/342750000000000000000000000000000 : ℝ)*base78 + (291745781130967811/342750000000000000000000000000000 : ℝ)*base79 + (9387088585103/1371000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (357793/80000000000000000000 : ℝ)*base89 + (357793/80000000000000000000 : ℝ)*base91 + (357793/80000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1078_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1078_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1078_box_0 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-129301783/625000000 : ℝ)*x 0 + (1075440707/2000000000 : ℝ)*x 1 + (5377203199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129301783/625000000 : ℝ)^8271 ≤ (3079415277747/25000000000000 : ℝ)^6223 := by
    have hnat : (129301783 : ℕ)^8271*25000000000000^6223 ≤ 3079415277747^6223*625000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129301783 625000000 3079415277747 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075440707/2000000000 : ℝ)^8271 ≤ (43841171262067/100000000000000 : ℝ)^6223 := by
    have hnat : (1075440707 : ℕ)^8271*100000000000000^6223 ≤ 43841171262067^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075440707 2000000000 43841171262067 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377203199/10000000000 : ℝ)^8271 ≤ (43841167621047/100000000000000 : ℝ)^6223 := by
    have hnat : (5377203199 : ℕ)^8271*100000000000000^6223 ≤ 43841167621047^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377203199 10000000000 43841167621047 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-129301783/625000000 : ℝ), (1075440707/2000000000 : ℝ), (5377203199/10000000000 : ℝ)] ![(3079415277747/25000000000000 : ℝ), (43841171262067/100000000000000 : ℝ), (43841167621047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-129301783/625000000 : ℝ)|^8271 ≤ (3079415277747/25000000000000 : ℝ)^6223
        have hw : |(-129301783/625000000 : ℝ)|=(129301783/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075440707/2000000000 : ℝ)|^8271 ≤ (43841171262067/100000000000000 : ℝ)^6223
        have hw : |(1075440707/2000000000 : ℝ)|=(1075440707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377203199/10000000000 : ℝ)|^8271 ≤ (43841167621047/100000000000000 : ℝ)^6223
        have hw : |(5377203199/10000000000 : ℝ)|=(5377203199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_box_1 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1323834541/2500000000 : ℝ)*x 0 + (-272460561/1250000000 : ℝ)*x 1 + (1344300893/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323834541/2500000000 : ℝ)^8271 ≤ (21478138859569/50000000000000 : ℝ)^6223 := by
    have hnat : (1323834541 : ℕ)^8271*50000000000000^6223 ≤ 21478138859569^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323834541 2500000000 21478138859569 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272460561/1250000000 : ℝ)^8271 ≤ (1650318825217/12500000000000 : ℝ)^6223 := by
    have hnat : (272460561 : ℕ)^8271*12500000000000^6223 ≤ 1650318825217^6223*1250000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272460561 1250000000 1650318825217 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344300893/2500000000 : ℝ)^8271 ≤ (43841171663013/100000000000000 : ℝ)^6223 := by
    have hnat : (1344300893 : ℕ)^8271*100000000000000^6223 ≤ 43841171663013^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344300893 2500000000 43841171663013 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323834541/2500000000 : ℝ), (-272460561/1250000000 : ℝ), (1344300893/2500000000 : ℝ)] ![(21478138859569/50000000000000 : ℝ), (1650318825217/12500000000000 : ℝ), (43841171663013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323834541/2500000000 : ℝ)|^8271 ≤ (21478138859569/50000000000000 : ℝ)^6223
        have hw : |(1323834541/2500000000 : ℝ)|=(1323834541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-272460561/1250000000 : ℝ)|^8271 ≤ (1650318825217/12500000000000 : ℝ)^6223
        have hw : |(-272460561/1250000000 : ℝ)|=(272460561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344300893/2500000000 : ℝ)|^8271 ≤ (43841171663013/100000000000000 : ℝ)^6223
        have hw : |(1344300893/2500000000 : ℝ)|=(1344300893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_box_2 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2647669279/5000000000 : ℝ)*x 0 + (5377203309/10000000000 : ℝ)*x 1 + (-435936863/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647669279/5000000000 : ℝ)^8271 ≤ (21478140983583/50000000000000 : ℝ)^6223 := by
    have hnat : (2647669279 : ℕ)^8271*50000000000000^6223 ≤ 21478140983583^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647669279 5000000000 21478140983583 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377203309/10000000000 : ℝ)^8271 ≤ (5480146101631/12500000000000 : ℝ)^6223 := by
    have hnat : (5377203309 : ℕ)^8271*12500000000000^6223 ≤ 5480146101631^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377203309 10000000000 5480146101631 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (435936863/2000000000 : ℝ)^8271 ≤ (13202549209001/100000000000000 : ℝ)^6223 := by
    have hnat : (435936863 : ℕ)^8271*100000000000000^6223 ≤ 13202549209001^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435936863 2000000000 13202549209001 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647669279/5000000000 : ℝ), (5377203309/10000000000 : ℝ), (-435936863/2000000000 : ℝ)] ![(21478140983583/50000000000000 : ℝ), (5480146101631/12500000000000 : ℝ), (13202549209001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647669279/5000000000 : ℝ)|^8271 ≤ (21478140983583/50000000000000 : ℝ)^6223
        have hw : |(2647669279/5000000000 : ℝ)|=(2647669279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377203309/10000000000 : ℝ)|^8271 ≤ (5480146101631/12500000000000 : ℝ)^6223
        have hw : |(5377203309/10000000000 : ℝ)|=(5377203309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-435936863/2000000000 : ℝ)|^8271 ≤ (13202549209001/100000000000000 : ℝ)^6223
        have hw : |(-435936863/2000000000 : ℝ)|=(435936863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_box_3 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1120504351/2500000000 : ℝ)*x 0 + (4321800813/10000000000 : ℝ)*x 1 + (540225033/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1120504351/2500000000 : ℝ)^8271 ≤ (17208494811471/50000000000000 : ℝ)^6223 := by
    have hnat : (1120504351 : ℕ)^8271*50000000000000^6223 ≤ 17208494811471^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120504351 2500000000 17208494811471 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4321800813/10000000000 : ℝ)^8271 ≤ (32791507950757/100000000000000 : ℝ)^6223 := by
    have hnat : (4321800813 : ℕ)^8271*100000000000000^6223 ≤ 32791507950757^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321800813 10000000000 32791507950757 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540225033/1250000000 : ℝ)^8271 ≤ (32791502414361/100000000000000 : ℝ)^6223 := by
    have hnat : (540225033 : ℕ)^8271*100000000000000^6223 ≤ 32791502414361^6223*1250000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540225033 1250000000 32791502414361 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1120504351/2500000000 : ℝ), (4321800813/10000000000 : ℝ), (540225033/1250000000 : ℝ)] ![(17208494811471/50000000000000 : ℝ), (32791507950757/100000000000000 : ℝ), (32791502414361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1120504351/2500000000 : ℝ)|^8271 ≤ (17208494811471/50000000000000 : ℝ)^6223
        have hw : |(1120504351/2500000000 : ℝ)|=(1120504351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4321800813/10000000000 : ℝ)|^8271 ≤ (32791507950757/100000000000000 : ℝ)^6223
        have hw : |(4321800813/10000000000 : ℝ)|=(4321800813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540225033/1250000000 : ℝ)|^8271 ≤ (32791502414361/100000000000000 : ℝ)^6223
        have hw : |(540225033/1250000000 : ℝ)|=(540225033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_box_4 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2328303341/10000000000 : ℝ)*x 0 + (5280268729/10000000000 : ℝ)*x 1 + (2640134977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2328303341/10000000000 : ℝ)^8271 ≤ (14412230278409/100000000000000 : ℝ)^6223 := by
    have hnat : (2328303341 : ℕ)^8271*100000000000000^6223 ≤ 14412230278409^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2328303341 10000000000 14412230278409 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280268729/10000000000 : ℝ)^8271 ≤ (21396939129057/50000000000000 : ℝ)^6223 := by
    have hnat : (5280268729 : ℕ)^8271*50000000000000^6223 ≤ 21396939129057^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280268729 10000000000 21396939129057 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640134977/5000000000 : ℝ)^8271 ≤ (8558778290687/20000000000000 : ℝ)^6223 := by
    have hnat : (2640134977 : ℕ)^8271*20000000000000^6223 ≤ 8558778290687^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640134977 5000000000 8558778290687 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2328303341/10000000000 : ℝ), (5280268729/10000000000 : ℝ), (2640134977/5000000000 : ℝ)] ![(14412230278409/100000000000000 : ℝ), (21396939129057/50000000000000 : ℝ), (8558778290687/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2328303341/10000000000 : ℝ)|^8271 ≤ (14412230278409/100000000000000 : ℝ)^6223
        have hw : |(-2328303341/10000000000 : ℝ)|=(2328303341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280268729/10000000000 : ℝ)|^8271 ≤ (21396939129057/50000000000000 : ℝ)^6223
        have hw : |(5280268729/10000000000 : ℝ)|=(5280268729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640134977/5000000000 : ℝ)|^8271 ≤ (8558778290687/20000000000000 : ℝ)^6223
        have hw : |(2640134977/5000000000 : ℝ)|=(2640134977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_box_5 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681960259/5000000000 : ℝ)*x 0 + (-2217619137/10000000000 : ℝ)*x 1 + (5280270329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681960259/5000000000 : ℝ)^8271 ≤ (43697290093953/100000000000000 : ℝ)^6223 := by
    have hnat : (2681960259 : ℕ)^8271*100000000000000^6223 ≤ 43697290093953^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681960259 5000000000 43697290093953 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217619137/10000000000 : ℝ)^8271 ≤ (844300899797/6250000000000 : ℝ)^6223 := by
    have hnat : (2217619137 : ℕ)^8271*6250000000000^6223 ≤ 844300899797^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217619137 10000000000 844300899797 6250000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280270329/10000000000 : ℝ)^8271 ≤ (42793895492819/100000000000000 : ℝ)^6223 := by
    have hnat : (5280270329 : ℕ)^8271*100000000000000^6223 ≤ 42793895492819^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280270329 10000000000 42793895492819 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681960259/5000000000 : ℝ), (-2217619137/10000000000 : ℝ), (5280270329/10000000000 : ℝ)] ![(43697290093953/100000000000000 : ℝ), (844300899797/6250000000000 : ℝ), (42793895492819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681960259/5000000000 : ℝ)|^8271 ≤ (43697290093953/100000000000000 : ℝ)^6223
        have hw : |(2681960259/5000000000 : ℝ)|=(2681960259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2217619137/10000000000 : ℝ)|^8271 ≤ (844300899797/6250000000000 : ℝ)^6223
        have hw : |(-2217619137/10000000000 : ℝ)|=(2217619137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280270329/10000000000 : ℝ)|^8271 ≤ (42793895492819/100000000000000 : ℝ)^6223
        have hw : |(5280270329/10000000000 : ℝ)|=(5280270329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_box_6 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (134098067/250000000 : ℝ)*x 0 + (5280268151/10000000000 : ℝ)*x 1 + (-2217619143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134098067/250000000 : ℝ)^8271 ≤ (5462164187891/12500000000000 : ℝ)^6223 := by
    have hnat : (134098067 : ℕ)^8271*12500000000000^6223 ≤ 5462164187891^6223*250000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134098067 250000000 5462164187891 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280268151/10000000000 : ℝ)^8271 ≤ (21396936016039/50000000000000 : ℝ)^6223 := by
    have hnat : (5280268151 : ℕ)^8271*50000000000000^6223 ≤ 21396936016039^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280268151 10000000000 21396936016039 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2217619143/10000000000 : ℝ)^8271 ≤ (1350881444533/10000000000000 : ℝ)^6223 := by
    have hnat : (2217619143 : ℕ)^8271*10000000000000^6223 ≤ 1350881444533^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217619143 10000000000 1350881444533 10000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134098067/250000000 : ℝ), (5280268151/10000000000 : ℝ), (-2217619143/10000000000 : ℝ)] ![(5462164187891/12500000000000 : ℝ), (21396936016039/50000000000000 : ℝ), (1350881444533/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134098067/250000000 : ℝ)|^8271 ≤ (5462164187891/12500000000000 : ℝ)^6223
        have hw : |(134098067/250000000 : ℝ)|=(134098067/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280268151/10000000000 : ℝ)|^8271 ≤ (21396936016039/50000000000000 : ℝ)^6223
        have hw : |(5280268151/10000000000 : ℝ)|=(5280268151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2217619143/10000000000 : ℝ)|^8271 ≤ (1350881444533/10000000000000 : ℝ)^6223
        have hw : |(-2217619143/10000000000 : ℝ)|=(2217619143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_box_7 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4265189321/10000000000 : ℝ)*x 0 + (2215096401/5000000000 : ℝ)*x 1 + (4430193641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4265189321/10000000000 : ℝ)^8271 ≤ (32221842889081/100000000000000 : ℝ)^6223 := by
    have hnat : (4265189321 : ℕ)^8271*100000000000000^6223 ≤ 32221842889081^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4265189321 10000000000 32221842889081 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2215096401/5000000000 : ℝ)^8271 ≤ (8472268570689/25000000000000 : ℝ)^6223 := by
    have hnat : (2215096401 : ℕ)^8271*25000000000000^6223 ≤ 8472268570689^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215096401 5000000000 8472268570689 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4430193641/10000000000 : ℝ)^8271 ≤ (16944541406459/50000000000000 : ℝ)^6223 := by
    have hnat : (4430193641 : ℕ)^8271*50000000000000^6223 ≤ 16944541406459^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4430193641 10000000000 16944541406459 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4265189321/10000000000 : ℝ), (2215096401/5000000000 : ℝ), (4430193641/10000000000 : ℝ)] ![(32221842889081/100000000000000 : ℝ), (8472268570689/25000000000000 : ℝ), (16944541406459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4265189321/10000000000 : ℝ)|^8271 ≤ (32221842889081/100000000000000 : ℝ)^6223
        have hw : |(4265189321/10000000000 : ℝ)|=(4265189321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2215096401/5000000000 : ℝ)|^8271 ≤ (8472268570689/25000000000000 : ℝ)^6223
        have hw : |(2215096401/5000000000 : ℝ)|=(2215096401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4430193641/10000000000 : ℝ)|^8271 ≤ (16944541406459/50000000000000 : ℝ)^6223
        have hw : |(4430193641/10000000000 : ℝ)|=(4430193641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_box_8 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2274120691/10000000000 : ℝ)*x 0 + (2607234961/5000000000 : ℝ)*x 1 + (5386805443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2274120691/10000000000 : ℝ)^8271 ≤ (6984088501597/50000000000000 : ℝ)^6223 := by
    have hnat : (2274120691 : ℕ)^8271*50000000000000^6223 ≤ 6984088501597^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274120691 10000000000 6984088501597 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607234961/5000000000 : ℝ)^8271 ≤ (21043285657939/50000000000000 : ℝ)^6223 := by
    have hnat : (2607234961 : ℕ)^8271*50000000000000^6223 ≤ 21043285657939^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607234961 5000000000 21043285657939 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386805443/10000000000 : ℝ)^8271 ≤ (549315645839/1250000000000 : ℝ)^6223 := by
    have hnat : (5386805443 : ℕ)^8271*1250000000000^6223 ≤ 549315645839^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386805443 10000000000 549315645839 1250000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2274120691/10000000000 : ℝ), (2607234961/5000000000 : ℝ), (5386805443/10000000000 : ℝ)] ![(6984088501597/50000000000000 : ℝ), (21043285657939/50000000000000 : ℝ), (549315645839/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2274120691/10000000000 : ℝ)|^8271 ≤ (6984088501597/50000000000000 : ℝ)^6223
        have hw : |(-2274120691/10000000000 : ℝ)|=(2274120691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607234961/5000000000 : ℝ)|^8271 ≤ (21043285657939/50000000000000 : ℝ)^6223
        have hw : |(2607234961/5000000000 : ℝ)|=(2607234961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386805443/10000000000 : ℝ)|^8271 ≤ (549315645839/1250000000000 : ℝ)^6223
        have hw : |(5386805443/10000000000 : ℝ)|=(5386805443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_box_9 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1057708193/2000000000 : ℝ)*x 0 + (-1087928229/5000000000 : ℝ)*x 1 + (1077361073/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057708193/2000000000 : ℝ)^8271 ≤ (8576601436293/20000000000000 : ℝ)^6223 := by
    have hnat : (1057708193 : ℕ)^8271*20000000000000^6223 ≤ 8576601436293^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057708193 2000000000 8576601436293 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087928229/5000000000 : ℝ)^8271 ≤ (13171741985979/100000000000000 : ℝ)^6223 := by
    have hnat : (1087928229 : ℕ)^8271*100000000000000^6223 ≤ 13171741985979^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087928229 5000000000 13171741985979 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077361073/2000000000 : ℝ)^8271 ≤ (21972625410693/50000000000000 : ℝ)^6223 := by
    have hnat : (1077361073 : ℕ)^8271*50000000000000^6223 ≤ 21972625410693^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077361073 2000000000 21972625410693 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057708193/2000000000 : ℝ), (-1087928229/5000000000 : ℝ), (1077361073/2000000000 : ℝ)] ![(8576601436293/20000000000000 : ℝ), (13171741985979/100000000000000 : ℝ), (21972625410693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057708193/2000000000 : ℝ)|^8271 ≤ (8576601436293/20000000000000 : ℝ)^6223
        have hw : |(1057708193/2000000000 : ℝ)|=(1057708193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1087928229/5000000000 : ℝ)|^8271 ≤ (13171741985979/100000000000000 : ℝ)^6223
        have hw : |(-1087928229/5000000000 : ℝ)|=(1087928229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077361073/2000000000 : ℝ)|^8271 ≤ (21972625410693/50000000000000 : ℝ)^6223
        have hw : |(1077361073/2000000000 : ℝ)|=(1077361073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_box_10 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288541077/10000000000 : ℝ)*x 0 + (5386805399/10000000000 : ℝ)*x 1 + (-2175856261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288541077/10000000000 : ℝ)^8271 ≤ (8576601677703/20000000000000 : ℝ)^6223 := by
    have hnat : (5288541077 : ℕ)^8271*20000000000000^6223 ≤ 8576601677703^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288541077 10000000000 8576601677703 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386805399/10000000000 : ℝ)^8271 ≤ (43945251190039/100000000000000 : ℝ)^6223 := by
    have hnat : (5386805399 : ℕ)^8271*100000000000000^6223 ≤ 43945251190039^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386805399 10000000000 43945251190039 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2175856261/10000000000 : ℝ)^8271 ≤ (263434808019/2000000000000 : ℝ)^6223 := by
    have hnat : (2175856261 : ℕ)^8271*2000000000000^6223 ≤ 263434808019^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175856261 10000000000 263434808019 2000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288541077/10000000000 : ℝ), (5386805399/10000000000 : ℝ), (-2175856261/10000000000 : ℝ)] ![(8576601677703/20000000000000 : ℝ), (43945251190039/100000000000000 : ℝ), (263434808019/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288541077/10000000000 : ℝ)|^8271 ≤ (8576601677703/20000000000000 : ℝ)^6223
        have hw : |(5288541077/10000000000 : ℝ)|=(5288541077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386805399/10000000000 : ℝ)|^8271 ≤ (43945251190039/100000000000000 : ℝ)^6223
        have hw : |(5386805399/10000000000 : ℝ)|=(5386805399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2175856261/10000000000 : ℝ)|^8271 ≤ (263434808019/2000000000000 : ℝ)^6223
        have hw : |(-2175856261/10000000000 : ℝ)|=(2175856261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_box_11 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4503222219/10000000000 : ℝ)*x 0 + (4311057521/10000000000 : ℝ)*x 1 + (4311057703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4503222219/10000000000 : ℝ)^8271 ≤ (34633575264493/100000000000000 : ℝ)^6223 := by
    have hnat : (4503222219 : ℕ)^8271*100000000000000^6223 ≤ 34633575264493^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503222219 10000000000 34633575264493 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4311057521/10000000000 : ℝ)^8271 ≤ (32683211441147/100000000000000 : ℝ)^6223 := by
    have hnat : (4311057521 : ℕ)^8271*100000000000000^6223 ≤ 32683211441147^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311057521 10000000000 32683211441147 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4311057703/10000000000 : ℝ)^8271 ≤ (1307328531001/4000000000000 : ℝ)^6223 := by
    have hnat : (4311057703 : ℕ)^8271*4000000000000^6223 ≤ 1307328531001^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311057703 10000000000 1307328531001 4000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4503222219/10000000000 : ℝ), (4311057521/10000000000 : ℝ), (4311057703/10000000000 : ℝ)] ![(34633575264493/100000000000000 : ℝ), (32683211441147/100000000000000 : ℝ), (1307328531001/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4503222219/10000000000 : ℝ)|^8271 ≤ (34633575264493/100000000000000 : ℝ)^6223
        have hw : |(4503222219/10000000000 : ℝ)|=(4503222219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4311057521/10000000000 : ℝ)|^8271 ≤ (32683211441147/100000000000000 : ℝ)^6223
        have hw : |(4311057521/10000000000 : ℝ)|=(4311057521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4311057703/10000000000 : ℝ)|^8271 ≤ (1307328531001/4000000000000 : ℝ)^6223
        have hw : |(4311057703/10000000000 : ℝ)|=(4311057703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_box_12 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-212337171/1000000000 : ℝ)*x 0 + (1360419169/2500000000 : ℝ)*x 1 + (5272262159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212337171/1000000000 : ℝ)^8271 ≤ (12751143556683/100000000000000 : ℝ)^6223 := by
    have hnat : (212337171 : ℕ)^8271*100000000000000^6223 ≤ 12751143556683^6223*1000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212337171 1000000000 12751143556683 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360419169/2500000000 : ℝ)^8271 ≤ (22270600467637/50000000000000 : ℝ)^6223 := by
    have hnat : (1360419169 : ℕ)^8271*50000000000000^6223 ≤ 22270600467637^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360419169 2500000000 22270600467637 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272262159/10000000000 : ℝ)^8271 ≤ (42707655495407/100000000000000 : ℝ)^6223 := by
    have hnat : (5272262159 : ℕ)^8271*100000000000000^6223 ≤ 42707655495407^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272262159 10000000000 42707655495407 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-212337171/1000000000 : ℝ), (1360419169/2500000000 : ℝ), (5272262159/10000000000 : ℝ)] ![(12751143556683/100000000000000 : ℝ), (22270600467637/50000000000000 : ℝ), (42707655495407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-212337171/1000000000 : ℝ)|^8271 ≤ (12751143556683/100000000000000 : ℝ)^6223
        have hw : |(-212337171/1000000000 : ℝ)|=(212337171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360419169/2500000000 : ℝ)|^8271 ≤ (22270600467637/50000000000000 : ℝ)^6223
        have hw : |(1360419169/2500000000 : ℝ)|=(1360419169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272262159/10000000000 : ℝ)|^8271 ≤ (42707655495407/100000000000000 : ℝ)^6223
        have hw : |(5272262159/10000000000 : ℝ)|=(5272262159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_box_13 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369584457/10000000000 : ℝ)*x 0 + (-1110346773/5000000000 : ℝ)*x 1 + (131806567/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369584457/10000000000 : ℝ)^8271 ≤ (5469828419647/12500000000000 : ℝ)^6223 := by
    have hnat : (5369584457 : ℕ)^8271*12500000000000^6223 ≤ 5469828419647^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369584457 10000000000 5469828419647 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1110346773/5000000000 : ℝ)^8271 ≤ (6766855759983/50000000000000 : ℝ)^6223 := by
    have hnat : (1110346773 : ℕ)^8271*50000000000000^6223 ≤ 6766855759983^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110346773 5000000000 6766855759983 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131806567/250000000 : ℝ)^8271 ≤ (8541532220931/20000000000000 : ℝ)^6223 := by
    have hnat : (131806567 : ℕ)^8271*20000000000000^6223 ≤ 8541532220931^6223*250000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131806567 250000000 8541532220931 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369584457/10000000000 : ℝ), (-1110346773/5000000000 : ℝ), (131806567/250000000 : ℝ)] ![(5469828419647/12500000000000 : ℝ), (6766855759983/50000000000000 : ℝ), (8541532220931/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369584457/10000000000 : ℝ)|^8271 ≤ (5469828419647/12500000000000 : ℝ)^6223
        have hw : |(5369584457/10000000000 : ℝ)|=(5369584457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1110346773/5000000000 : ℝ)|^8271 ≤ (6766855759983/50000000000000 : ℝ)^6223
        have hw : |(-1110346773/5000000000 : ℝ)|=(1110346773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131806567/250000000 : ℝ)|^8271 ≤ (8541532220931/20000000000000 : ℝ)^6223
        have hw : |(131806567/250000000 : ℝ)|=(131806567/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_box_14 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (671198071/1250000000 : ℝ)*x 0 + (2636131003/5000000000 : ℝ)*x 1 + (-444138859/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671198071/1250000000 : ℝ)^8271 ≤ (10939657139863/25000000000000 : ℝ)^6223 := by
    have hnat : (671198071 : ℕ)^8271*25000000000000^6223 ≤ 10939657139863^6223*1250000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671198071 1250000000 10939657139863 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636131003/5000000000 : ℝ)^8271 ≤ (42707653848161/100000000000000 : ℝ)^6223 := by
    have hnat : (2636131003 : ℕ)^8271*100000000000000^6223 ≤ 42707653848161^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636131003 5000000000 42707653848161 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (444138859/2000000000 : ℝ)^8271 ≤ (13533717586887/100000000000000 : ℝ)^6223 := by
    have hnat : (444138859 : ℕ)^8271*100000000000000^6223 ≤ 13533717586887^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444138859 2000000000 13533717586887 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671198071/1250000000 : ℝ), (2636131003/5000000000 : ℝ), (-444138859/2000000000 : ℝ)] ![(10939657139863/25000000000000 : ℝ), (42707653848161/100000000000000 : ℝ), (13533717586887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671198071/1250000000 : ℝ)|^8271 ≤ (10939657139863/25000000000000 : ℝ)^6223
        have hw : |(671198071/1250000000 : ℝ)|=(671198071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636131003/5000000000 : ℝ)|^8271 ≤ (42707653848161/100000000000000 : ℝ)^6223
        have hw : |(2636131003/5000000000 : ℝ)|=(2636131003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-444138859/2000000000 : ℝ)|^8271 ≤ (13533717586887/100000000000000 : ℝ)^6223
        have hw : |(-444138859/2000000000 : ℝ)|=(444138859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_box_15 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1061762071/2500000000 : ℝ)*x 0 + (4439141271/10000000000 : ℝ)*x 1 + (4439142511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061762071/2500000000 : ℝ)^8271 ≤ (8009954786483/25000000000000 : ℝ)^6223 := by
    have hnat : (1061762071 : ℕ)^8271*25000000000000^6223 ≤ 8009954786483^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061762071 2500000000 8009954786483 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4439141271/10000000000 : ℝ)^8271 ≤ (33980084111097/100000000000000 : ℝ)^6223 := by
    have hnat : (4439141271 : ℕ)^8271*100000000000000^6223 ≤ 33980084111097^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4439141271 10000000000 33980084111097 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4439142511/10000000000 : ℝ)^8271 ≤ (1061878022707/3125000000000 : ℝ)^6223 := by
    have hnat : (4439142511 : ℕ)^8271*3125000000000^6223 ≤ 1061878022707^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4439142511 10000000000 1061878022707 3125000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061762071/2500000000 : ℝ), (4439141271/10000000000 : ℝ), (4439142511/10000000000 : ℝ)] ![(8009954786483/25000000000000 : ℝ), (33980084111097/100000000000000 : ℝ), (1061878022707/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061762071/2500000000 : ℝ)|^8271 ≤ (8009954786483/25000000000000 : ℝ)^6223
        have hw : |(1061762071/2500000000 : ℝ)|=(1061762071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4439141271/10000000000 : ℝ)|^8271 ≤ (33980084111097/100000000000000 : ℝ)^6223
        have hw : |(4439141271/10000000000 : ℝ)|=(4439141271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4439142511/10000000000 : ℝ)|^8271 ≤ (1061878022707/3125000000000 : ℝ)^6223
        have hw : |(4439142511/10000000000 : ℝ)|=(4439142511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1078_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2489/4000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(237/400 : ℝ) ∧ (7961/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (4149/5000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1401/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1401/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1401/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1401/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1401/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1401/10000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (11269/100000 : ℝ) ^ (4135/1024 : ℝ) ≤ (14839924156136409/100000000000000000000 : ℝ) := by
    have hpowers : (11269/100000 : ℝ)^4135 ≤ (14839924156136409/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11269 : ℕ)^4135*100000000000000000000^1024 ≤ 14839924156136409^1024*100000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11269 100000 14839924156136409 100000000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11269/100000 : ℝ)) (X := (14839924156136409/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1401/10000 : ℝ) ^ (4135/1024 : ℝ) ≤ (17873674375479973/50000000000000000000 : ℝ) := by
    have hpowers : (1401/10000 : ℝ)^4135 ≤ (17873674375479973/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1401 : ℕ)^4135*50000000000000000000^1024 ≤ 17873674375479973^1024*10000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1401 10000 17873674375479973 50000000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1401/10000 : ℝ)) (X := (17873674375479973/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014839924156136409/50000000000000000000 : ℝ) ≤ (5000367457944313/5000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (50014839924156136409/50000000000000000000 : ℝ)^1024 ≤ (5000367457944313/5000000000000000 : ℝ)^4135 := by
      have hnat : (50014839924156136409 : ℕ)^1024*5000000000000000^4135 ≤ 5000367457944313^4135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014839924156136409 50000000000000000000 5000367457944313 5000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000367457944313/5000000000000000 : ℝ)) (X := (50014839924156136409/50000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010117454581419271/20000000000000000000 : ℝ) ≤ (2500313128855121/2500000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (20010117454581419271/20000000000000000000 : ℝ)^1024 ≤ (2500313128855121/2500000000000000 : ℝ)^4135 := by
      have hnat : (20010117454581419271 : ℕ)^1024*2500000000000000^4135 ≤ 2500313128855121^4135*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010117454581419271 20000000000000000000 2500313128855121 2500000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500313128855121/2500000000000000 : ℝ)) (X := (20010117454581419271/20000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017873674375479973/25000000000000000000 : ℝ) ≤ (5000885057476171/5000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (25017873674375479973/25000000000000000000 : ℝ)^1024 ≤ (5000885057476171/5000000000000000 : ℝ)^4135 := by
      have hnat : (25017873674375479973 : ℕ)^1024*5000000000000000^4135 ≤ 5000885057476171^4135*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017873674375479973 25000000000000000000 5000885057476171 5000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000885057476171/5000000000000000 : ℝ)) (X := (25017873674375479973/25000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14839924156136409/100000000000000000000 : ℝ) ≤ ((13700174373100854131/13705000000000000000 : ℝ)+2*(258799765929/137050000000000 : ℝ)*(11269/100000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (13700174373100854131/13705000000000000000 : ℝ)+2*(258799765929/137050000000000 : ℝ)*(11269/100000 : ℝ)=(5000367457944313/5000000000000000 : ℝ) by norm_num, show 1+2*(14839924156136409/100000000000000000000 : ℝ)=(50014839924156136409/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17873674375479973/50000000000000000000 : ℝ)+(14839924156136409/100000000000000000000 : ℝ) ≤ ((13700174373100854131/13705000000000000000 : ℝ)+(258799765929/137050000000000 : ℝ)*((1401/10000 : ℝ)+(11269/100000 : ℝ)))^(4135/1024 : ℝ) := by
    rw [show (13700174373100854131/13705000000000000000 : ℝ)+(258799765929/137050000000000 : ℝ)*((1401/10000 : ℝ)+(11269/100000 : ℝ))=(2500313128855121/2500000000000000 : ℝ) by norm_num, show 1+(17873674375479973/50000000000000000000 : ℝ)+(14839924156136409/100000000000000000000 : ℝ)=(20010117454581419271/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17873674375479973/50000000000000000000 : ℝ) ≤ ((13700174373100854131/13705000000000000000 : ℝ)+2*(258799765929/137050000000000 : ℝ)*(1401/10000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (13700174373100854131/13705000000000000000 : ℝ)+2*(258799765929/137050000000000 : ℝ)*(1401/10000 : ℝ)=(5000885057476171/5000000000000000 : ℝ) by norm_num, show 1+2*(17873674375479973/50000000000000000000 : ℝ)=(25017873674375479973/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13700174373100854131/13705000000000000000 : ℝ)*(X 1 0+X 2 0)+(258799765929/137050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (1401/10000 : ℝ)) (c := (13700174373100854131/13705000000000000000 : ℝ)) (alpha := (258799765929/137050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13700174373100854131/13705000000000000000 : ℝ)*(X 0 1+X 2 1)+(258799765929/137050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (1401/10000 : ℝ)) (c := (13700174373100854131/13705000000000000000 : ℝ)) (alpha := (258799765929/137050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13700174373100854131/13705000000000000000 : ℝ)*(X 0 2+X 1 2)+(258799765929/137050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (1401/10000 : ℝ)) (c := (13700174373100854131/13705000000000000000 : ℝ)) (alpha := (258799765929/137050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-129301783/625000000 : ℝ)*X 0 0+(1075440707/2000000000 : ℝ)*X 0 1+(5377203199/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1323834541/2500000000 : ℝ)*X 1 0+(-272460561/1250000000 : ℝ)*X 1 1+(1344300893/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647669279/5000000000 : ℝ)*X 2 0+(5377203309/10000000000 : ℝ)*X 2 1+(-435936863/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1120504351/2500000000 : ℝ)*X 0 0+(4321800813/10000000000 : ℝ)*X 0 1+(540225033/1250000000 : ℝ)*X 0 2+(1120504351/2500000000 : ℝ)*X 1 0+(4321800813/10000000000 : ℝ)*X 1 1+(540225033/1250000000 : ℝ)*X 1 2+(1120504351/2500000000 : ℝ)*X 2 0+(4321800813/10000000000 : ℝ)*X 2 1+(540225033/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2328303341/10000000000 : ℝ)*X 0 0+(5280268729/10000000000 : ℝ)*X 0 1+(2640134977/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681960259/5000000000 : ℝ)*X 1 0+(-2217619137/10000000000 : ℝ)*X 1 1+(5280270329/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((134098067/250000000 : ℝ)*X 2 0+(5280268151/10000000000 : ℝ)*X 2 1+(-2217619143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4265189321/10000000000 : ℝ)*X 0 0+(2215096401/5000000000 : ℝ)*X 0 1+(4430193641/10000000000 : ℝ)*X 0 2+(4265189321/10000000000 : ℝ)*X 1 0+(2215096401/5000000000 : ℝ)*X 1 1+(4430193641/10000000000 : ℝ)*X 1 2+(4265189321/10000000000 : ℝ)*X 2 0+(2215096401/5000000000 : ℝ)*X 2 1+(4430193641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2274120691/10000000000 : ℝ)*X 0 0+(2607234961/5000000000 : ℝ)*X 0 1+(5386805443/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1057708193/2000000000 : ℝ)*X 1 0+(-1087928229/5000000000 : ℝ)*X 1 1+(1077361073/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288541077/10000000000 : ℝ)*X 2 0+(5386805399/10000000000 : ℝ)*X 2 1+(-2175856261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4503222219/10000000000 : ℝ)*X 0 0+(4311057521/10000000000 : ℝ)*X 0 1+(4311057703/10000000000 : ℝ)*X 0 2+(4503222219/10000000000 : ℝ)*X 1 0+(4311057521/10000000000 : ℝ)*X 1 1+(4311057703/10000000000 : ℝ)*X 1 2+(4503222219/10000000000 : ℝ)*X 2 0+(4311057521/10000000000 : ℝ)*X 2 1+(4311057703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-212337171/1000000000 : ℝ)*X 0 0+(1360419169/2500000000 : ℝ)*X 0 1+(5272262159/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369584457/10000000000 : ℝ)*X 1 0+(-1110346773/5000000000 : ℝ)*X 1 1+(131806567/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((671198071/1250000000 : ℝ)*X 2 0+(2636131003/5000000000 : ℝ)*X 2 1+(-444138859/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1061762071/2500000000 : ℝ)*X 0 0+(4439141271/10000000000 : ℝ)*X 0 1+(4439142511/10000000000 : ℝ)*X 0 2+(1061762071/2500000000 : ℝ)*X 1 0+(4439141271/10000000000 : ℝ)*X 1 1+(4439142511/10000000000 : ℝ)*X 1 2+(1061762071/2500000000 : ℝ)*X 2 0+(4439141271/10000000000 : ℝ)*X 2 1+(4439142511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2489/4000 : ℝ) ≤ (-53297645894999053386031517942607/85656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (249248901/100000000000000 : ℝ)*(lower2) + (197913913/100000000000000 : ℝ)*(lower3) + (492483673/100000000000000 : ℝ)*(upper5) + (966715767509999/25000000000000 : ℝ)*(major0) + (966715767509999/25000000000000 : ℝ)*(major1) + (966715767509999/25000000000000 : ℝ)*(major2) + (85364035107/100000000000000 : ℝ)*(sp2) + (766887441/3125000000000 : ℝ)*(sp3) + (20582849863353/400000000000 : ℝ)*(sp4) + (5145224334739333/100000000000000 : ℝ)*(sp5) + (2572814714773473/50000000000000 : ℝ)*(sp6) + (260872771171383/10000000000000 : ℝ)*(sp7) + (1163871901/50000000000000 : ℝ)*(sp12) + (3065367767/625000000000 : ℝ)*(sp13) + (1304376126055971/50000000000000 : ℝ)*(f.failure) + (5145714793582053/100000000000000 : ℝ)*(f.sum) + (1668071293567/856562500000000000000000000 : ℝ)*base66 + (4056958960085305869/342625000000000000000000000000000 : ℝ)*base67 + (5696069251708055869/342625000000000000000000000000000 : ℝ)*base69 + (2531960749753555869/342625000000000000000000000000000 : ℝ)*base71 + (20276524255193/13705000000000000000000000000 : ℝ)*base73 + (6948622708180869/342625000000000000000000000000000 : ℝ)*base75 + (331340426737944131/342625000000000000000000000000000 : ℝ)*base78 + (1664874723999430869/342625000000000000000000000000000 : ℝ)*base79 + (47058744253993/13705000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (521903/1000000000000000000000 : ℝ)*base90 + (521903/1000000000000000000000 : ℝ)*base92 + (521903/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (237/400 : ℝ) ≤ (40602600558219322913005810629927/68525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8882339/25000000000000 : ℝ)*(lower1) + (251588863/100000000000000 : ℝ)*(upper4) + (23478883/20000000000000 : ℝ)*(lower5) + (392997327550413/10000000000000 : ℝ)*(major0) + (392997327550413/10000000000000 : ℝ)*(major1) + (392997327550413/10000000000000 : ℝ)*(major2) + (324303353847129/6250000000000 : ℝ)*(sp0) + (5188851679062743/100000000000000 : ℝ)*(sp1) + (5188844805042989/100000000000000 : ℝ)*(sp2) + (2651312831762589/100000000000000 : ℝ)*(sp3) + (15010867543/100000000000000 : ℝ)*(sp5) + (85487841/390625000000 : ℝ)*(sp6) + (16281141609/100000000000000 : ℝ)*(sp7) + (13028376221/100000000000000 : ℝ)*(sp8) + (1325664556452099/50000000000000 : ℝ)*(f.failure) + (2594433344965143/50000000000000 : ℝ)*(f.sum) + (690739721843/1370500000000000000000000000 : ℝ)*base65 + (652628161033343897/137050000000000000000000000000000 : ℝ)*base68 + (1747456091593693897/137050000000000000000000000000000 : ℝ)*base70 + (2827036502476043897/137050000000000000000000000000000 : ℝ)*base72 + (614927341301/342625000000000000000000000 : ℝ)*base73 + (2040322074541893897/137050000000000000000000000000000 : ℝ)*base76 + (1336093127268843897/137050000000000000000000000000000 : ℝ)*base78 + (1227199225413093897/137050000000000000000000000000000 : ℝ)*base80 + (1316952611113/1370500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (5649393/1000000000000000000000 : ℝ)*base89 + (5649393/1000000000000000000000 : ℝ)*base91 + (5649393/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (7961/10000 : ℝ) ≤ (109108911038772875970320077423359/137050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (66697231/100000000000000 : ℝ)*(upper0) + (39640027/50000000000000 : ℝ)*(lower3) + (104649181/100000000000000 : ℝ)*(upper4) + (879638700348263/20000000000000 : ℝ)*(major0) + (879638700348263/20000000000000 : ℝ)*(major1) + (879638700348263/20000000000000 : ℝ)*(major2) + (55110057461/100000000000000 : ℝ)*(sp1) + (28363090877/25000000000000 : ℝ)*(sp2) + (55401940893/100000000000000 : ℝ)*(sp3) + (110855459/6250000000000 : ℝ)*(sp4) + (1160527421112133/20000000000000 : ℝ)*(sp8) + (5802583769190547/100000000000000 : ℝ)*(sp9) + (11605050853769/200000000000 : ℝ)*(sp10) + (741788806802373/25000000000000 : ℝ)*(sp11) + (185450664321899/6250000000000 : ℝ)*(f.failure) + (725329859906001/12500000000000 : ℝ)*(f.sum) + (13088985346787/2741000000000000000000000000 : ℝ)*base66 + (1742194430007775547/274100000000000000000000000000000 : ℝ)*base68 + (2350656727170975547/274100000000000000000000000000000 : ℝ)*base70 + (815924115048975547/274100000000000000000000000000000 : ℝ)*base72 + (50965171894027/2741000000000000000000000000 : ℝ)*base73 + (1322454975647424453/274100000000000000000000000000000 : ℝ)*base75 + (1463526070269475547/274100000000000000000000000000000 : ℝ)*base78 + (14894913690951624453/274100000000000000000000000000000 : ℝ)*base79 + (7717246527187/1370500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1072007/125000000000000000000 : ℝ)*base90 + (1072007/125000000000000000000 : ℝ)*base92 + (1072007/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-4149/5000 : ℝ) ≤ (-568602176965237964041626943260309/685250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (212857619/100000000000000 : ℝ)*(lower1) + (88084219/100000000000000 : ℝ)*(upper3) + (361523501/100000000000000 : ℝ)*(lower4) + (3587081/10000000000000 : ℝ)*(upper5) + (4432812425955587/100000000000000 : ℝ)*(major0) + (4432812425955587/100000000000000 : ℝ)*(major1) + (4432812425955587/100000000000000 : ℝ)*(major2) + (1645836849/20000000000000 : ℝ)*(sp4) + (754242524491/100000000000000 : ℝ)*(sp6) + (3351742577/1000000000000 : ℝ)*(sp7) + (5902709688471003/100000000000000 : ℝ)*(sp12) + (5902717917655249/100000000000000 : ℝ)*(sp13) + (2950981837565379/50000000000000 : ℝ)*(sp14) + (1495115435561921/50000000000000 : ℝ)*(sp15) + (1495283022690771/50000000000000 : ℝ)*(f.failure) + (5902717917655249/100000000000000 : ℝ)*(f.sum) + (43373029688781/13705000000000000000000000000 : ℝ)*base65 + (16025431821053720103/1370500000000000000000000000000000 : ℝ)*base68 + (57994418049989279897/1370500000000000000000000000000000 : ℝ)*base69 + (5687495964476720103/1370500000000000000000000000000000 : ℝ)*base72 + (7806744345547/6852500000000000000000000000 : ℝ)*base74 + (3284802076622779897/1370500000000000000000000000000000 : ℝ)*base75 + (6173247255762220103/1370500000000000000000000000000000 : ℝ)*base78 + (22836496200801720103/1370500000000000000000000000000000 : ℝ)*base80 + (1094821121394349/13705000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2361697/1000000000000000000000 : ℝ)*base89 + (2361697/1000000000000000000000 : ℝ)*base91 + (2361697/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1078_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(237/400 : ℝ) else (7961/10000 : ℝ) ≤ X j i ∧ X j i ≤ (4149/5000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1078_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1078_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(237/400 : ℝ) else (7961/10000 : ℝ) ≤ X j i ∧ X j i ≤ (4149/5000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1078_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1078_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(237/400 : ℝ) else (7961/10000 : ℝ) ≤ X j i ∧ X j i ≤ (4149/5000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1078_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

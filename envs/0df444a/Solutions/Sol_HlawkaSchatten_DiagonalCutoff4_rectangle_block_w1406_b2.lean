-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1406_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:47:56.799+00:00
-- url     : https://prove2.me/submissions/25cf884f-5f01-4741-ae0d-514d86249cd2

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
theorem support_rectangle_w1406_s6_0 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1989941921/10000000000 : ℝ)*x 0 + (5409412089/10000000000 : ℝ)*x 1 + (1311591127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989941921/10000000000 : ℝ)^2183 ≤ (758372834117/6250000000000 : ℝ)^1671 := by
    have hnat : (1989941921 : ℕ)^2183*6250000000000^1671 ≤ 758372834117^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989941921 10000000000 758372834117 6250000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409412089/10000000000 : ℝ)^2183 ≤ (8962235450147/20000000000000 : ℝ)^1671 := by
    have hnat : (5409412089 : ℕ)^2183*20000000000000^1671 ≤ 8962235450147^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409412089 10000000000 8962235450147 20000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311591127/2500000000 : ℝ)^2183 ≤ (43054857385217/100000000000000 : ℝ)^1671 := by
    have hnat : (1311591127 : ℕ)^2183*100000000000000^1671 ≤ 43054857385217^1671*2500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311591127 2500000000 43054857385217 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1989941921/10000000000 : ℝ), (5409412089/10000000000 : ℝ), (1311591127/2500000000 : ℝ)] ![(758372834117/6250000000000 : ℝ), (8962235450147/20000000000000 : ℝ), (43054857385217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1989941921/10000000000 : ℝ)|^2183 ≤ (758372834117/6250000000000 : ℝ)^1671
        have hw : |(-1989941921/10000000000 : ℝ)|=(1989941921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409412089/10000000000 : ℝ)|^2183 ≤ (8962235450147/20000000000000 : ℝ)^1671
        have hw : |(5409412089/10000000000 : ℝ)|=(5409412089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311591127/2500000000 : ℝ)|^2183 ≤ (43054857385217/100000000000000 : ℝ)^1671
        have hw : |(1311591127/2500000000 : ℝ)|=(1311591127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s6_1 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267390157/500000000 : ℝ)*x 0 + (-129560521/625000000 : ℝ)*x 1 + (5246364503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267390157/500000000 : ℝ)^2183 ≤ (8829120473513/20000000000000 : ℝ)^1671 := by
    have hnat : (267390157 : ℕ)^2183*20000000000000^1671 ≤ 8829120473513^1671*500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267390157 500000000 8829120473513 20000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129560521/625000000 : ℝ)^2183 ≤ (79997126809/625000000000 : ℝ)^1671 := by
    have hnat : (129560521 : ℕ)^2183*625000000000^1671 ≤ 79997126809^1671*625000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129560521 625000000 79997126809 625000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246364503/10000000000 : ℝ)^2183 ≤ (43054857331611/100000000000000 : ℝ)^1671 := by
    have hnat : (5246364503 : ℕ)^2183*100000000000000^1671 ≤ 43054857331611^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246364503 10000000000 43054857331611 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267390157/500000000 : ℝ), (-129560521/625000000 : ℝ), (5246364503/10000000000 : ℝ)] ![(8829120473513/20000000000000 : ℝ), (79997126809/625000000000 : ℝ), (43054857331611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267390157/500000000 : ℝ)|^2183 ≤ (8829120473513/20000000000000 : ℝ)^1671
        have hw : |(267390157/500000000 : ℝ)|=(267390157/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129560521/625000000 : ℝ)|^2183 ≤ (79997126809/625000000000 : ℝ)^1671
        have hw : |(-129560521/625000000 : ℝ)|=(129560521/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246364503/10000000000 : ℝ)|^2183 ≤ (43054857331611/100000000000000 : ℝ)^1671
        have hw : |(5246364503/10000000000 : ℝ)|=(5246364503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s6_2 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336950797/2500000000 : ℝ)*x 0 + (5246364449/10000000000 : ℝ)*x 1 + (-2072968343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336950797/2500000000 : ℝ)^2183 ≤ (5518200360651/12500000000000 : ℝ)^1671 := by
    have hnat : (1336950797 : ℕ)^2183*12500000000000^1671 ≤ 5518200360651^1671*2500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336950797 2500000000 5518200360651 12500000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246364449/10000000000 : ℝ)^2183 ≤ (43054856752669/100000000000000 : ℝ)^1671 := by
    have hnat : (5246364449 : ℕ)^2183*100000000000000^1671 ≤ 43054856752669^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246364449 10000000000 43054856752669 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072968343/10000000000 : ℝ)^2183 ≤ (799971271619/6250000000000 : ℝ)^1671 := by
    have hnat : (2072968343 : ℕ)^2183*6250000000000^1671 ≤ 799971271619^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072968343 10000000000 799971271619 6250000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336950797/2500000000 : ℝ), (5246364449/10000000000 : ℝ), (-2072968343/10000000000 : ℝ)] ![(5518200360651/12500000000000 : ℝ), (43054856752669/100000000000000 : ℝ), (799971271619/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336950797/2500000000 : ℝ)|^2183 ≤ (5518200360651/12500000000000 : ℝ)^1671
        have hw : |(1336950797/2500000000 : ℝ)|=(1336950797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246364449/10000000000 : ℝ)|^2183 ≤ (43054856752669/100000000000000 : ℝ)^1671
        have hw : |(5246364449/10000000000 : ℝ)|=(5246364449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2072968343/10000000000 : ℝ)|^2183 ≤ (799971271619/6250000000000 : ℝ)^1671
        have hw : |(-2072968343/10000000000 : ℝ)|=(2072968343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s6_3 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (862031579/2000000000 : ℝ)*x 0 + (4138502883/10000000000 : ℝ)*x 1 + (2244129621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862031579/2000000000 : ℝ)^2183 ≤ (6660865453293/20000000000000 : ℝ)^1671 := by
    have hnat : (862031579 : ℕ)^2183*20000000000000^1671 ≤ 6660865453293^1671*2000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862031579 2000000000 6660865453293 20000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4138502883/10000000000 : ℝ)^2183 ≤ (31582227201221/100000000000000 : ℝ)^1671 := by
    have hnat : (4138502883 : ℕ)^2183*100000000000000^1671 ≤ 31582227201221^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4138502883 10000000000 31582227201221 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244129621/5000000000 : ℝ)^2183 ≤ (1755672275643/5000000000000 : ℝ)^1671 := by
    have hnat : (2244129621 : ℕ)^2183*5000000000000^1671 ≤ 1755672275643^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244129621 5000000000 1755672275643 5000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862031579/2000000000 : ℝ), (4138502883/10000000000 : ℝ), (2244129621/5000000000 : ℝ)] ![(6660865453293/20000000000000 : ℝ), (31582227201221/100000000000000 : ℝ), (1755672275643/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862031579/2000000000 : ℝ)|^2183 ≤ (6660865453293/20000000000000 : ℝ)^1671
        have hw : |(862031579/2000000000 : ℝ)|=(862031579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4138502883/10000000000 : ℝ)|^2183 ≤ (31582227201221/100000000000000 : ℝ)^1671
        have hw : |(4138502883/10000000000 : ℝ)|=(4138502883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2244129621/5000000000 : ℝ)|^2183 ≤ (1755672275643/5000000000000 : ℝ)^1671
        have hw : |(2244129621/5000000000 : ℝ)|=(2244129621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s6_4 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1989953483/10000000000 : ℝ)*x 0 + (5246951373/10000000000 : ℝ)*x 1 + (1352205543/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989953483/10000000000 : ℝ)^2183 ≤ (47398661909/390625000000 : ℝ)^1671 := by
    have hnat : (1989953483 : ℕ)^2183*390625000000^1671 ≤ 47398661909^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989953483 10000000000 47398661909 390625000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246951373/10000000000 : ℝ)^2183 ≤ (10765287338761/25000000000000 : ℝ)^1671 := by
    have hnat : (5246951373 : ℕ)^2183*25000000000000^1671 ≤ 10765287338761^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246951373 10000000000 10765287338761 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352205543/2500000000 : ℝ)^2183 ≤ (112011982967/250000000000 : ℝ)^1671 := by
    have hnat : (1352205543 : ℕ)^2183*250000000000^1671 ≤ 112011982967^1671*2500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352205543 2500000000 112011982967 250000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1989953483/10000000000 : ℝ), (5246951373/10000000000 : ℝ), (1352205543/2500000000 : ℝ)] ![(47398661909/390625000000 : ℝ), (10765287338761/25000000000000 : ℝ), (112011982967/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1989953483/10000000000 : ℝ)|^2183 ≤ (47398661909/390625000000 : ℝ)^1671
        have hw : |(-1989953483/10000000000 : ℝ)|=(1989953483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246951373/10000000000 : ℝ)|^2183 ≤ (10765287338761/25000000000000 : ℝ)^1671
        have hw : |(5246951373/10000000000 : ℝ)|=(5246951373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352205543/2500000000 : ℝ)|^2183 ≤ (112011982967/250000000000 : ℝ)^1671
        have hw : |(1352205543/2500000000 : ℝ)|=(1352205543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s6_5 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061102507/2000000000 : ℝ)*x 0 + (-1910510663/10000000000 : ℝ)*x 1 + (5408822173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061102507/2000000000 : ℝ)^2183 ≤ (21845042061779/50000000000000 : ℝ)^1671 := by
    have hnat : (1061102507 : ℕ)^2183*50000000000000^1671 ≤ 21845042061779^1671*2000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061102507 2000000000 21845042061779 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1910510663/10000000000 : ℝ)^2183 ≤ (2876280665169/25000000000000 : ℝ)^1671 := by
    have hnat : (1910510663 : ℕ)^2183*25000000000000^1671 ≤ 2876280665169^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1910510663 10000000000 2876280665169 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408822173/10000000000 : ℝ)^2183 ≤ (22402396598811/50000000000000 : ℝ)^1671 := by
    have hnat : (5408822173 : ℕ)^2183*50000000000000^1671 ≤ 22402396598811^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408822173 10000000000 22402396598811 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061102507/2000000000 : ℝ), (-1910510663/10000000000 : ℝ), (5408822173/10000000000 : ℝ)] ![(21845042061779/50000000000000 : ℝ), (2876280665169/25000000000000 : ℝ), (22402396598811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061102507/2000000000 : ℝ)|^2183 ≤ (21845042061779/50000000000000 : ℝ)^1671
        have hw : |(1061102507/2000000000 : ℝ)|=(1061102507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1910510663/10000000000 : ℝ)|^2183 ≤ (2876280665169/25000000000000 : ℝ)^1671
        have hw : |(-1910510663/10000000000 : ℝ)|=(1910510663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408822173/10000000000 : ℝ)|^2183 ≤ (22402396598811/50000000000000 : ℝ)^1671
        have hw : |(5408822173/10000000000 : ℝ)|=(5408822173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s6_6 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (663189069/1250000000 : ℝ)*x 0 + (5408822159/10000000000 : ℝ)*x 1 + (-1910510659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663189069/1250000000 : ℝ)^2183 ≤ (8738016861289/20000000000000 : ℝ)^1671 := by
    have hnat : (663189069 : ℕ)^2183*20000000000000^1671 ≤ 8738016861289^1671*1250000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663189069 1250000000 8738016861289 20000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408822159/10000000000 : ℝ)^2183 ≤ (44804793046117/100000000000000 : ℝ)^1671 := by
    have hnat : (5408822159 : ℕ)^2183*100000000000000^1671 ≤ 44804793046117^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408822159 10000000000 44804793046117 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1910510659/10000000000 : ℝ)^2183 ≤ (1438140328651/12500000000000 : ℝ)^1671 := by
    have hnat : (1910510659 : ℕ)^2183*12500000000000^1671 ≤ 1438140328651^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1910510659 10000000000 1438140328651 12500000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663189069/1250000000 : ℝ), (5408822159/10000000000 : ℝ), (-1910510659/10000000000 : ℝ)] ![(8738016861289/20000000000000 : ℝ), (44804793046117/100000000000000 : ℝ), (1438140328651/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663189069/1250000000 : ℝ)|^2183 ≤ (8738016861289/20000000000000 : ℝ)^1671
        have hw : |(663189069/1250000000 : ℝ)|=(663189069/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408822159/10000000000 : ℝ)|^2183 ≤ (44804793046117/100000000000000 : ℝ)^1671
        have hw : |(5408822159/10000000000 : ℝ)|=(5408822159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1910510659/10000000000 : ℝ)|^2183 ≤ (1438140328651/12500000000000 : ℝ)^1671
        have hw : |(-1910510659/10000000000 : ℝ)|=(1910510659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s6_7 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (862036521/2000000000 : ℝ)*x 0 + (1121750073/2500000000 : ℝ)*x 1 + (4139768387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862036521/2000000000 : ℝ)^2183 ≤ (6660915340351/20000000000000 : ℝ)^1671 := by
    have hnat : (862036521 : ℕ)^2183*20000000000000^1671 ≤ 6660915340351^1671*2000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862036521 2000000000 6660915340351 20000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121750073/2500000000 : ℝ)^2183 ≤ (8775144736979/25000000000000 : ℝ)^1671 := by
    have hnat : (1121750073 : ℕ)^2183*25000000000000^1671 ≤ 8775144736979^1671*2500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121750073 2500000000 8775144736979 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4139768387/10000000000 : ℝ)^2183 ≤ (7898711083279/25000000000000 : ℝ)^1671 := by
    have hnat : (4139768387 : ℕ)^2183*25000000000000^1671 ≤ 7898711083279^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139768387 10000000000 7898711083279 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862036521/2000000000 : ℝ), (1121750073/2500000000 : ℝ), (4139768387/10000000000 : ℝ)] ![(6660915340351/20000000000000 : ℝ), (8775144736979/25000000000000 : ℝ), (7898711083279/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862036521/2000000000 : ℝ)|^2183 ≤ (6660915340351/20000000000000 : ℝ)^1671
        have hw : |(862036521/2000000000 : ℝ)|=(862036521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121750073/2500000000 : ℝ)|^2183 ≤ (8775144736979/25000000000000 : ℝ)^1671
        have hw : |(1121750073/2500000000 : ℝ)|=(1121750073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4139768387/10000000000 : ℝ)|^2183 ≤ (7898711083279/25000000000000 : ℝ)^1671
        have hw : |(4139768387/10000000000 : ℝ)|=(4139768387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1406_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157255887/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2823/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2949/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1411/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1411/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1411/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1411/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1411/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1411/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1411/12500 : ℝ) ^ (4365/1024 : ℝ) ≤ (4576831610437999/50000000000000000000 : ℝ) := by
    have hpowers : (1411/12500 : ℝ)^4365 ≤ (4576831610437999/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1411 : ℕ)^4365*50000000000000000000^1024 ≤ 4576831610437999^1024*12500^4365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1411 12500 4576831610437999 50000000000000000000 4365 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1411/12500 : ℝ)) (X := (4576831610437999/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (59/400 : ℝ) ^ (4365/1024 : ℝ) ≤ (14314745976469479/50000000000000000000 : ℝ) := by
    have hpowers : (59/400 : ℝ)^4365 ≤ (14314745976469479/50000000000000000000 : ℝ)^1024 := by
      have hnat : (59 : ℕ)^4365*50000000000000000000^1024 ≤ 14314745976469479^1024*400^4365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59 400 14314745976469479 50000000000000000000 4365 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59/400 : ℝ)) (X := (14314745976469479/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004576831610437999/25000000000000000000 : ℝ) ≤ (5000214723814117/5000000000000000 : ℝ) ^ (4365/1024 : ℝ) := by
    have hpowers : (25004576831610437999/25000000000000000000 : ℝ)^1024 ≤ (5000214723814117/5000000000000000 : ℝ)^4365 := by
      have hnat : (25004576831610437999 : ℕ)^1024*5000000000000000^4365 ≤ 5000214723814117^4365*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004576831610437999 25000000000000000000 5000214723814117 5000000000000000 1024 4365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000214723814117/5000000000000000 : ℝ)) (X := (25004576831610437999/25000000000000000000 : ℝ)) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009445788793453739/25000000000000000000 : ℝ) ≤ (5000443119790099/5000000000000000 : ℝ) ^ (4365/1024 : ℝ) := by
    have hpowers : (25009445788793453739/25000000000000000000 : ℝ)^1024 ≤ (5000443119790099/5000000000000000 : ℝ)^4365 := by
      have hnat : (25009445788793453739 : ℕ)^1024*5000000000000000^4365 ≤ 5000443119790099^4365*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009445788793453739 25000000000000000000 5000443119790099 5000000000000000 1024 4365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000443119790099/5000000000000000 : ℝ)) (X := (25009445788793453739/25000000000000000000 : ℝ)) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014314745976469479/25000000000000000000 : ℝ) ≤ (5000671515766081/5000000000000000 : ℝ) ^ (4365/1024 : ℝ) := by
    have hpowers : (25014314745976469479/25000000000000000000 : ℝ)^1024 ≤ (5000671515766081/5000000000000000 : ℝ)^4365 := by
      have hnat : (25014314745976469479 : ℕ)^1024*5000000000000000^4365 ≤ 5000671515766081^4365*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014314745976469479 25000000000000000000 5000671515766081 5000000000000000 1024 4365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000671515766081/5000000000000000 : ℝ)) (X := (25014314745976469479/25000000000000000000 : ℝ)) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4576831610437999/50000000000000000000 : ℝ) ≤ ((2884264517715117237/2885000000000000000 : ℝ)+2*(38065995997/28850000000000 : ℝ)*(1411/12500 : ℝ))^(4365/1024 : ℝ) := by
    rw [show (2884264517715117237/2885000000000000000 : ℝ)+2*(38065995997/28850000000000 : ℝ)*(1411/12500 : ℝ)=(5000214723814117/5000000000000000 : ℝ) by norm_num, show 1+2*(4576831610437999/50000000000000000000 : ℝ)=(25004576831610437999/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14314745976469479/50000000000000000000 : ℝ)+(4576831610437999/50000000000000000000 : ℝ) ≤ ((2884264517715117237/2885000000000000000 : ℝ)+(38065995997/28850000000000 : ℝ)*((59/400 : ℝ)+(1411/12500 : ℝ)))^(4365/1024 : ℝ) := by
    rw [show (2884264517715117237/2885000000000000000 : ℝ)+(38065995997/28850000000000 : ℝ)*((59/400 : ℝ)+(1411/12500 : ℝ))=(5000443119790099/5000000000000000 : ℝ) by norm_num, show 1+(14314745976469479/50000000000000000000 : ℝ)+(4576831610437999/50000000000000000000 : ℝ)=(25009445788793453739/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14314745976469479/50000000000000000000 : ℝ) ≤ ((2884264517715117237/2885000000000000000 : ℝ)+2*(38065995997/28850000000000 : ℝ)*(59/400 : ℝ))^(4365/1024 : ℝ) := by
    rw [show (2884264517715117237/2885000000000000000 : ℝ)+2*(38065995997/28850000000000 : ℝ)*(59/400 : ℝ)=(5000671515766081/5000000000000000 : ℝ) by norm_num, show 1+2*(14314745976469479/50000000000000000000 : ℝ)=(25014314745976469479/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2884264517715117237/2885000000000000000 : ℝ)*(X 1 0+X 2 0)+(38065995997/28850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4365/1024 : ℝ)) (lo := (1411/12500 : ℝ)) (hi := (59/400 : ℝ)) (c := (2884264517715117237/2885000000000000000 : ℝ)) (alpha := (38065995997/28850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2884264517715117237/2885000000000000000 : ℝ)*(X 0 1+X 2 1)+(38065995997/28850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4365/1024 : ℝ)) (lo := (1411/12500 : ℝ)) (hi := (59/400 : ℝ)) (c := (2884264517715117237/2885000000000000000 : ℝ)) (alpha := (38065995997/28850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2884264517715117237/2885000000000000000 : ℝ)*(X 0 2+X 1 2)+(38065995997/28850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4365/1024 : ℝ)) (lo := (1411/12500 : ℝ)) (hi := (59/400 : ℝ)) (c := (2884264517715117237/2885000000000000000 : ℝ)) (alpha := (38065995997/28850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1989941921/10000000000 : ℝ)*X 0 0+(5409412089/10000000000 : ℝ)*X 0 1+(1311591127/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267390157/500000000 : ℝ)*X 1 0+(-129560521/625000000 : ℝ)*X 1 1+(5246364503/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336950797/2500000000 : ℝ)*X 2 0+(5246364449/10000000000 : ℝ)*X 2 1+(-2072968343/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((862031579/2000000000 : ℝ)*X 0 0+(4138502883/10000000000 : ℝ)*X 0 1+(2244129621/5000000000 : ℝ)*X 0 2+(862031579/2000000000 : ℝ)*X 1 0+(4138502883/10000000000 : ℝ)*X 1 1+(2244129621/5000000000 : ℝ)*X 1 2+(862031579/2000000000 : ℝ)*X 2 0+(4138502883/10000000000 : ℝ)*X 2 1+(2244129621/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1989953483/10000000000 : ℝ)*X 0 0+(5246951373/10000000000 : ℝ)*X 0 1+(1352205543/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061102507/2000000000 : ℝ)*X 1 0+(-1910510663/10000000000 : ℝ)*X 1 1+(5408822173/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663189069/1250000000 : ℝ)*X 2 0+(5408822159/10000000000 : ℝ)*X 2 1+(-1910510659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((862036521/2000000000 : ℝ)*X 0 0+(1121750073/2500000000 : ℝ)*X 0 1+(4139768387/10000000000 : ℝ)*X 0 2+(862036521/2000000000 : ℝ)*X 1 0+(1121750073/2500000000 : ℝ)*X 1 1+(4139768387/10000000000 : ℝ)*X 1 2+(862036521/2000000000 : ℝ)*X 2 0+(1121750073/2500000000 : ℝ)*X 2 1+(4139768387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (817996462185126704562677991/144250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1039599581/100000000000000 : ℝ)*(base19) + (493043789/50000000000000 : ℝ)*(base23) + (29028311/50000000000000 : ℝ)*(lower2) + (39341507/25000000000000 : ℝ)*(upper3) + (78316487/100000000000000 : ℝ)*(upper5) + (4496187558455481/100000000000000 : ℝ)*(major0) + (4496187558455481/100000000000000 : ℝ)*(major1) + (2248093779227741/50000000000000 : ℝ)*(major2) + (613320065398221/10000000000000 : ℝ)*(sp0) + (766652519813853/12500000000000 : ℝ)*(sp1) + (6133220212022827/100000000000000 : ℝ)*(sp2) + (2859142488580513/100000000000000 : ℝ)*(sp3) + (4108825639/20000000000000 : ℝ)*(sp4) + (2810299293/25000000000000 : ℝ)*(sp7) + (571830745955537/20000000000000 : ℝ)*(f.failure) + (1226644239622081/20000000000000 : ℝ)*(f.sum) + (15002896794111/2885000000000000000000000000 : ℝ)*base65 + (617611727562374003/288500000000000000000000000000000 : ℝ)*base68 + (95996118963021617/144250000000000000000000000000000 : ℝ)*base69 + (2022916566998125997/288500000000000000000000000000000 : ℝ)*base71 + (1111590100363/360625000000000000000000000 : ℝ)*base74 + (1265888073887978383/144250000000000000000000000000000 : ℝ)*base76 + (245091438567574003/288500000000000000000000000000000 : ℝ)*base78 + (431319589235074003/288500000000000000000000000000000 : ℝ)*base80 + (15614900782749/2885000000000000000000000000 : ℝ)*base81 + (13496319/2000000000000000000000 : ℝ)*base89 + (13496319/2000000000000000000000 : ℝ)*base91 + (6503681/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9504055062922564867359/1442500000000000000000000000 : ℝ) := by norm_num
    linear_combination (552343659/50000000000000 : ℝ)*(base19) + (1208790811/100000000000000 : ℝ)*(base23) + (186590517/50000000000000 : ℝ)*(lower1) + (134618347/100000000000000 : ℝ)*(upper3) + (3783753/10000000000000 : ℝ)*(lower4) + (27928031/20000000000000 : ℝ)*(upper5) + (4528825937787017/100000000000000 : ℝ)*(major0) + (4528825937787017/100000000000000 : ℝ)*(major1) + (4528825937787017/100000000000000 : ℝ)*(major2) + (6366429/390625000000 : ℝ)*(sp2) + (6177742977058571/100000000000000 : ℝ)*(sp4) + (1544435468092813/25000000000000 : ℝ)*(sp5) + (386108758653871/6250000000000 : ℝ)*(sp6) + (2879908678895447/100000000000000 : ℝ)*(sp7) + (2879908678895447/100000000000000 : ℝ)*(f.failure) + (6177742977058571/100000000000000 : ℝ)*(f.sum) + (441205973733/180312500000000000000000000 : ℝ)*base65 + (10147845127683087971/288500000000000000000000000000000 : ℝ)*base68 + (703489421402087971/288500000000000000000000000000000 : ℝ)*base70 + (14259080402518912029/288500000000000000000000000000000 : ℝ)*base71 + (4872378999709/1442500000000000000000000000 : ℝ)*base73 + (43224116508813912029/288500000000000000000000000000000 : ℝ)*base75 + (1080679173395087971/288500000000000000000000000000000 : ℝ)*base78 + (3972839612412029/288500000000000000000000000000000 : ℝ)*base79 + (10609628824193/2885000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1753511/10000000000000000000000 : ℝ)*base90 + (1753511/10000000000000000000000 : ℝ)*base92 + (1753511/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1406_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157255887/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1406_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1406_s7_0 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1989947583/10000000000 : ℝ)*x 0 + (5409377277/10000000000 : ℝ)*x 1 + (2623197721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989947583/10000000000 : ℝ)^2183 ≤ (6067005224657/50000000000000 : ℝ)^1671 := by
    have hnat : (1989947583 : ℕ)^2183*50000000000000^1671 ≤ 6067005224657^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989947583 10000000000 6067005224657 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409377277/10000000000 : ℝ)^2183 ≤ (44810800510401/100000000000000 : ℝ)^1671 := by
    have hnat : (5409377277 : ℕ)^2183*100000000000000^1671 ≤ 44810800510401^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409377277 10000000000 44810800510401 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623197721/5000000000 : ℝ)^2183 ≤ (43055189033271/100000000000000 : ℝ)^1671 := by
    have hnat : (2623197721 : ℕ)^2183*100000000000000^1671 ≤ 43055189033271^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623197721 5000000000 43055189033271 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1989947583/10000000000 : ℝ), (5409377277/10000000000 : ℝ), (2623197721/5000000000 : ℝ)] ![(6067005224657/50000000000000 : ℝ), (44810800510401/100000000000000 : ℝ), (43055189033271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1989947583/10000000000 : ℝ)|^2183 ≤ (6067005224657/50000000000000 : ℝ)^1671
        have hw : |(-1989947583/10000000000 : ℝ)|=(1989947583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409377277/10000000000 : ℝ)|^2183 ≤ (44810800510401/100000000000000 : ℝ)^1671
        have hw : |(5409377277/10000000000 : ℝ)|=(5409377277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623197721/5000000000 : ℝ)|^2183 ≤ (43055189033271/100000000000000 : ℝ)^1671
        have hw : |(2623197721/5000000000 : ℝ)|=(2623197721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s7_1 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668474209/1250000000 : ℝ)*x 0 + (-2072939849/10000000000 : ℝ)*x 1 + (262319773/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668474209/1250000000 : ℝ)^2183 ≤ (44145500262461/100000000000000 : ℝ)^1671 := by
    have hnat : (668474209 : ℕ)^2183*100000000000000^1671 ≤ 44145500262461^1671*1250000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668474209 1250000000 44145500262461 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2072939849/10000000000 : ℝ)^2183 ≤ (12799310502791/100000000000000 : ℝ)^1671 := by
    have hnat : (2072939849 : ℕ)^2183*100000000000000^1671 ≤ 12799310502791^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072939849 10000000000 12799310502791 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262319773/500000000 : ℝ)^2183 ≤ (43055189226251/100000000000000 : ℝ)^1671 := by
    have hnat : (262319773 : ℕ)^2183*100000000000000^1671 ≤ 43055189226251^1671*500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262319773 500000000 43055189226251 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668474209/1250000000 : ℝ), (-2072939849/10000000000 : ℝ), (262319773/500000000 : ℝ)] ![(44145500262461/100000000000000 : ℝ), (12799310502791/100000000000000 : ℝ), (43055189226251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668474209/1250000000 : ℝ)|^2183 ≤ (44145500262461/100000000000000 : ℝ)^1671
        have hw : |(668474209/1250000000 : ℝ)|=(668474209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2072939849/10000000000 : ℝ)|^2183 ≤ (12799310502791/100000000000000 : ℝ)^1671
        have hw : |(-2072939849/10000000000 : ℝ)|=(2072939849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262319773/500000000 : ℝ)|^2183 ≤ (43055189226251/100000000000000 : ℝ)^1671
        have hw : |(262319773/500000000 : ℝ)|=(262319773/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s7_2 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336948419/2500000000 : ℝ)*x 0 + (5246395461/10000000000 : ℝ)*x 1 + (-2072939841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336948419/2500000000 : ℝ)^2183 ≤ (22072750152799/50000000000000 : ℝ)^1671 := by
    have hnat : (1336948419 : ℕ)^2183*50000000000000^1671 ≤ 22072750152799^1671*2500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336948419 2500000000 22072750152799 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246395461/10000000000 : ℝ)^2183 ≤ (43055189236973/100000000000000 : ℝ)^1671 := by
    have hnat : (5246395461 : ℕ)^2183*100000000000000^1671 ≤ 43055189236973^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246395461 10000000000 43055189236973 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072939841/10000000000 : ℝ)^2183 ≤ (12799310438261/100000000000000 : ℝ)^1671 := by
    have hnat : (2072939841 : ℕ)^2183*100000000000000^1671 ≤ 12799310438261^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072939841 10000000000 12799310438261 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336948419/2500000000 : ℝ), (5246395461/10000000000 : ℝ), (-2072939841/10000000000 : ℝ)] ![(22072750152799/50000000000000 : ℝ), (43055189236973/100000000000000 : ℝ), (12799310438261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336948419/2500000000 : ℝ)|^2183 ≤ (22072750152799/50000000000000 : ℝ)^1671
        have hw : |(1336948419/2500000000 : ℝ)|=(1336948419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246395461/10000000000 : ℝ)|^2183 ≤ (43055189236973/100000000000000 : ℝ)^1671
        have hw : |(5246395461/10000000000 : ℝ)|=(5246395461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2072939841/10000000000 : ℝ)|^2183 ≤ (12799310438261/100000000000000 : ℝ)^1671
        have hw : |(-2072939841/10000000000 : ℝ)|=(2072939841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s7_3 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (26938501/62500000 : ℝ)*x 0 + (4138573189/10000000000 : ℝ)*x 1 + (179527537/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26938501/62500000 : ℝ)^2183 ≤ (33304350130507/100000000000000 : ℝ)^1671 := by
    have hnat : (26938501 : ℕ)^2183*100000000000000^1671 ≤ 33304350130507^1671*62500000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26938501 62500000 33304350130507 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4138573189/10000000000 : ℝ)^2183 ≤ (31582928124199/100000000000000 : ℝ)^1671 := by
    have hnat : (4138573189 : ℕ)^2183*100000000000000^1671 ≤ 31582928124199^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4138573189 10000000000 31582928124199 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179527537/400000000 : ℝ)^2183 ≤ (2194545108023/6250000000000 : ℝ)^1671 := by
    have hnat : (179527537 : ℕ)^2183*6250000000000^1671 ≤ 2194545108023^1671*400000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179527537 400000000 2194545108023 6250000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26938501/62500000 : ℝ), (4138573189/10000000000 : ℝ), (179527537/400000000 : ℝ)] ![(33304350130507/100000000000000 : ℝ), (31582928124199/100000000000000 : ℝ), (2194545108023/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26938501/62500000 : ℝ)|^2183 ≤ (33304350130507/100000000000000 : ℝ)^1671
        have hw : |(26938501/62500000 : ℝ)|=(26938501/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4138573189/10000000000 : ℝ)|^2183 ≤ (31582928124199/100000000000000 : ℝ)^1671
        have hw : |(4138573189/10000000000 : ℝ)|=(4138573189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(179527537/400000000 : ℝ)|^2183 ≤ (2194545108023/6250000000000 : ℝ)^1671
        have hw : |(179527537/400000000 : ℝ)|=(179527537/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s7_4 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-994979531/5000000000 : ℝ)*x 0 + (2623490983/5000000000 : ℝ)*x 1 + (1352196939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (994979531/5000000000 : ℝ)^2183 ≤ (1516762736381/12500000000000 : ℝ)^1671 := by
    have hnat : (994979531 : ℕ)^2183*12500000000000^1671 ≤ 1516762736381^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994979531 5000000000 1516762736381 12500000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623490983/5000000000 : ℝ)^2183 ≤ (5382684669803/12500000000000 : ℝ)^1671 := by
    have hnat : (2623490983 : ℕ)^2183*12500000000000^1671 ≤ 5382684669803^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623490983 5000000000 5382684669803 12500000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352196939/2500000000 : ℝ)^2183 ≤ (1792176829779/4000000000000 : ℝ)^1671 := by
    have hnat : (1352196939 : ℕ)^2183*4000000000000^1671 ≤ 1792176829779^1671*2500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352196939 2500000000 1792176829779 4000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-994979531/5000000000 : ℝ), (2623490983/5000000000 : ℝ), (1352196939/2500000000 : ℝ)] ![(1516762736381/12500000000000 : ℝ), (5382684669803/12500000000000 : ℝ), (1792176829779/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-994979531/5000000000 : ℝ)|^2183 ≤ (1516762736381/12500000000000 : ℝ)^1671
        have hw : |(-994979531/5000000000 : ℝ)|=(994979531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623490983/5000000000 : ℝ)|^2183 ≤ (5382684669803/12500000000000 : ℝ)^1671
        have hw : |(2623490983/5000000000 : ℝ)|=(2623490983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352196939/2500000000 : ℝ)|^2183 ≤ (1792176829779/4000000000000 : ℝ)^1671
        have hw : |(1352196939/2500000000 : ℝ)|=(1352196939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s7_5 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (530551959/1000000000 : ℝ)*x 0 + (-1910547573/10000000000 : ℝ)*x 1 + (5408788327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530551959/1000000000 : ℝ)^2183 ≤ (2730635001343/6250000000000 : ℝ)^1671 := by
    have hnat : (530551959 : ℕ)^2183*6250000000000^1671 ≤ 2730635001343^1671*1000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530551959 1000000000 2730635001343 6250000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1910547573/10000000000 : ℝ)^2183 ≤ (575270651957/5000000000000 : ℝ)^1671 := by
    have hnat : (1910547573 : ℕ)^2183*5000000000000^1671 ≤ 575270651957^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1910547573 10000000000 575270651957 5000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408788327/10000000000 : ℝ)^2183 ≤ (8960885384741/20000000000000 : ℝ)^1671 := by
    have hnat : (5408788327 : ℕ)^2183*20000000000000^1671 ≤ 8960885384741^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408788327 10000000000 8960885384741 20000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530551959/1000000000 : ℝ), (-1910547573/10000000000 : ℝ), (5408788327/10000000000 : ℝ)] ![(2730635001343/6250000000000 : ℝ), (575270651957/5000000000000 : ℝ), (8960885384741/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530551959/1000000000 : ℝ)|^2183 ≤ (2730635001343/6250000000000 : ℝ)^1671
        have hw : |(530551959/1000000000 : ℝ)|=(530551959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1910547573/10000000000 : ℝ)|^2183 ≤ (575270651957/5000000000000 : ℝ)^1671
        have hw : |(-1910547573/10000000000 : ℝ)|=(1910547573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408788327/10000000000 : ℝ)|^2183 ≤ (8960885384741/20000000000000 : ℝ)^1671
        have hw : |(5408788327/10000000000 : ℝ)|=(5408788327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s7_6 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061104127/2000000000 : ℝ)*x 0 + (1081757507/2000000000 : ℝ)*x 1 + (-955273617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061104127/2000000000 : ℝ)^2183 ≤ (10922542815909/25000000000000 : ℝ)^1671 := by
    have hnat : (1061104127 : ℕ)^2183*25000000000000^1671 ≤ 10922542815909^1671*2000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061104127 2000000000 10922542815909 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081757507/2000000000 : ℝ)^2183 ≤ (8960883670573/20000000000000 : ℝ)^1671 := by
    have hnat : (1081757507 : ℕ)^2183*20000000000000^1671 ≤ 8960883670573^1671*2000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081757507 2000000000 8960883670573 20000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (955273617/5000000000 : ℝ)^2183 ≤ (11505410372151/100000000000000 : ℝ)^1671 := by
    have hnat : (955273617 : ℕ)^2183*100000000000000^1671 ≤ 11505410372151^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955273617 5000000000 11505410372151 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061104127/2000000000 : ℝ), (1081757507/2000000000 : ℝ), (-955273617/5000000000 : ℝ)] ![(10922542815909/25000000000000 : ℝ), (8960883670573/20000000000000 : ℝ), (11505410372151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061104127/2000000000 : ℝ)|^2183 ≤ (10922542815909/25000000000000 : ℝ)^1671
        have hw : |(1061104127/2000000000 : ℝ)|=(1061104127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081757507/2000000000 : ℝ)|^2183 ≤ (8960883670573/20000000000000 : ℝ)^1671
        have hw : |(1081757507/2000000000 : ℝ)|=(1081757507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-955273617/5000000000 : ℝ)|^2183 ≤ (11505410372151/100000000000000 : ℝ)^1671
        have hw : |(-955273617/5000000000 : ℝ)|=(955273617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_s7_7 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1077546207/2500000000 : ℝ)*x 0 + (70108287/156250000 : ℝ)*x 1 + (4139837807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077546207/2500000000 : ℝ)^2183 ≤ (8326149785467/25000000000000 : ℝ)^1671 := by
    have hnat : (1077546207 : ℕ)^2183*25000000000000^1671 ≤ 8326149785467^1671*2500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077546207 2500000000 8326149785467 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70108287/156250000 : ℝ)^2183 ≤ (2193741521983/6250000000000 : ℝ)^1671 := by
    have hnat : (70108287 : ℕ)^2183*6250000000000^1671 ≤ 2193741521983^1671*156250000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70108287 156250000 2193741521983 6250000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4139837807/10000000000 : ℝ)^2183 ≤ (197472103049/625000000000 : ℝ)^1671 := by
    have hnat : (4139837807 : ℕ)^2183*625000000000^1671 ≤ 197472103049^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139837807 10000000000 197472103049 625000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077546207/2500000000 : ℝ), (70108287/156250000 : ℝ), (4139837807/10000000000 : ℝ)] ![(8326149785467/25000000000000 : ℝ), (2193741521983/6250000000000 : ℝ), (197472103049/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077546207/2500000000 : ℝ)|^2183 ≤ (8326149785467/25000000000000 : ℝ)^1671
        have hw : |(1077546207/2500000000 : ℝ)|=(1077546207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(70108287/156250000 : ℝ)|^2183 ≤ (2193741521983/6250000000000 : ℝ)^1671
        have hw : |(70108287/156250000 : ℝ)|=(70108287/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4139837807/10000000000 : ℝ)|^2183 ≤ (197472103049/625000000000 : ℝ)^1671
        have hw : |(4139837807/10000000000 : ℝ)|=(4139837807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1406_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157255887/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11293/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1843/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2949/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2823/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2949/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2823/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2949/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2823/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2949/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2823/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2949/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2823/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2949/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2823/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2823/25000 : ℝ) ^ (4365/1024 : ℝ) ≤ (9167498032951993/100000000000000000000 : ℝ) := by
    have hpowers : (2823/25000 : ℝ)^4365 ≤ (9167498032951993/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2823 : ℕ)^4365*100000000000000000000^1024 ≤ 9167498032951993^1024*25000^4365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2823 25000 9167498032951993 100000000000000000000 4365 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2823/25000 : ℝ)) (X := (9167498032951993/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2949/20000 : ℝ) ^ (4365/1024 : ℝ) ≤ (28588145739027181/100000000000000000000 : ℝ) := by
    have hpowers : (2949/20000 : ℝ)^4365 ≤ (28588145739027181/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2949 : ℕ)^4365*100000000000000000000^1024 ≤ 28588145739027181^1024*20000^4365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2949 20000 28588145739027181 100000000000000000000 4365 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2949/20000 : ℝ)) (X := (28588145739027181/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009167498032951993/50000000000000000000 : ℝ) ≤ (5000215048324111/5000000000000000 : ℝ) ^ (4365/1024 : ℝ) := by
    have hpowers : (50009167498032951993/50000000000000000000 : ℝ)^1024 ≤ (5000215048324111/5000000000000000 : ℝ)^4365 := by
      have hnat : (50009167498032951993 : ℕ)^1024*5000000000000000^4365 ≤ 5000215048324111^4365*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009167498032951993 50000000000000000000 5000215048324111 5000000000000000 1024 4365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000215048324111/5000000000000000 : ℝ)) (X := (50009167498032951993/50000000000000000000 : ℝ)) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018877821885989587/50000000000000000000 : ℝ) ≤ (2000177118873501/2000000000000000 : ℝ) ^ (4365/1024 : ℝ) := by
    have hpowers : (50018877821885989587/50000000000000000000 : ℝ)^1024 ≤ (2000177118873501/2000000000000000 : ℝ)^4365 := by
      have hnat : (50018877821885989587 : ℕ)^1024*2000000000000000^4365 ≤ 2000177118873501^4365*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018877821885989587 50000000000000000000 2000177118873501 2000000000000000 1024 4365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000177118873501/2000000000000000 : ℝ)) (X := (50018877821885989587/50000000000000000000 : ℝ)) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028588145739027181/50000000000000000000 : ℝ) ≤ (2500335273021697/2500000000000000 : ℝ) ^ (4365/1024 : ℝ) := by
    have hpowers : (50028588145739027181/50000000000000000000 : ℝ)^1024 ≤ (2500335273021697/2500000000000000 : ℝ)^4365 := by
      have hnat : (50028588145739027181 : ℕ)^1024*2500000000000000^4365 ≤ 2500335273021697^4365*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028588145739027181 50000000000000000000 2500335273021697 2500000000000000 1024 4365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500335273021697/2500000000000000 : ℝ)) (X := (50028588145739027181/50000000000000000000 : ℝ)) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9167498032951993/100000000000000000000 : ℝ) ≤ ((5753533027205670549/5755000000000000000 : ℝ)+2*(455497719283/345300000000000 : ℝ)*(2823/25000 : ℝ))^(4365/1024 : ℝ) := by
    rw [show (5753533027205670549/5755000000000000000 : ℝ)+2*(455497719283/345300000000000 : ℝ)*(2823/25000 : ℝ)=(5000215048324111/5000000000000000 : ℝ) by norm_num, show 1+2*(9167498032951993/100000000000000000000 : ℝ)=(50009167498032951993/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28588145739027181/100000000000000000000 : ℝ)+(9167498032951993/100000000000000000000 : ℝ) ≤ ((5753533027205670549/5755000000000000000 : ℝ)+(455497719283/345300000000000 : ℝ)*((2949/20000 : ℝ)+(2823/25000 : ℝ)))^(4365/1024 : ℝ) := by
    rw [show (5753533027205670549/5755000000000000000 : ℝ)+(455497719283/345300000000000 : ℝ)*((2949/20000 : ℝ)+(2823/25000 : ℝ))=(2000177118873501/2000000000000000 : ℝ) by norm_num, show 1+(28588145739027181/100000000000000000000 : ℝ)+(9167498032951993/100000000000000000000 : ℝ)=(50018877821885989587/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28588145739027181/100000000000000000000 : ℝ) ≤ ((5753533027205670549/5755000000000000000 : ℝ)+2*(455497719283/345300000000000 : ℝ)*(2949/20000 : ℝ))^(4365/1024 : ℝ) := by
    rw [show (5753533027205670549/5755000000000000000 : ℝ)+2*(455497719283/345300000000000 : ℝ)*(2949/20000 : ℝ)=(2500335273021697/2500000000000000 : ℝ) by norm_num, show 1+2*(28588145739027181/100000000000000000000 : ℝ)=(50028588145739027181/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5753533027205670549/5755000000000000000 : ℝ)*(X 1 0+X 2 0)+(455497719283/345300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4365/1024 : ℝ)) (lo := (2823/25000 : ℝ)) (hi := (2949/20000 : ℝ)) (c := (5753533027205670549/5755000000000000000 : ℝ)) (alpha := (455497719283/345300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5753533027205670549/5755000000000000000 : ℝ)*(X 0 1+X 2 1)+(455497719283/345300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4365/1024 : ℝ)) (lo := (2823/25000 : ℝ)) (hi := (2949/20000 : ℝ)) (c := (5753533027205670549/5755000000000000000 : ℝ)) (alpha := (455497719283/345300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5753533027205670549/5755000000000000000 : ℝ)*(X 0 2+X 1 2)+(455497719283/345300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4365/1024 : ℝ)) (lo := (2823/25000 : ℝ)) (hi := (2949/20000 : ℝ)) (c := (5753533027205670549/5755000000000000000 : ℝ)) (alpha := (455497719283/345300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1989947583/10000000000 : ℝ)*X 0 0+(5409377277/10000000000 : ℝ)*X 0 1+(2623197721/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668474209/1250000000 : ℝ)*X 1 0+(-2072939849/10000000000 : ℝ)*X 1 1+(262319773/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336948419/2500000000 : ℝ)*X 2 0+(5246395461/10000000000 : ℝ)*X 2 1+(-2072939841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((26938501/62500000 : ℝ)*X 0 0+(4138573189/10000000000 : ℝ)*X 0 1+(179527537/400000000 : ℝ)*X 0 2+(26938501/62500000 : ℝ)*X 1 0+(4138573189/10000000000 : ℝ)*X 1 1+(179527537/400000000 : ℝ)*X 1 2+(26938501/62500000 : ℝ)*X 2 0+(4138573189/10000000000 : ℝ)*X 2 1+(179527537/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-994979531/5000000000 : ℝ)*X 0 0+(2623490983/5000000000 : ℝ)*X 0 1+(1352196939/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530551959/1000000000 : ℝ)*X 1 0+(-1910547573/10000000000 : ℝ)*X 1 1+(5408788327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061104127/2000000000 : ℝ)*X 2 0+(1081757507/2000000000 : ℝ)*X 2 1+(-955273617/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1077546207/2500000000 : ℝ)*X 0 0+(70108287/156250000 : ℝ)*X 0 1+(4139837807/10000000000 : ℝ)*X 0 2+(1077546207/2500000000 : ℝ)*X 1 0+(70108287/156250000 : ℝ)*X 1 1+(4139837807/10000000000 : ℝ)*X 1 2+(1077546207/2500000000 : ℝ)*X 2 0+(70108287/156250000 : ℝ)*X 2 1+(4139837807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (332820864057452417218141363/143875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (444050283/100000000000000 : ℝ)*(base19) + (430457437/100000000000000 : ℝ)*(base23) + (58161471/100000000000000 : ℝ)*(upper3) + (9723443/100000000000000 : ℝ)*(upper4) + (44349/80000000000 : ℝ)*(upper5) + (4497984877938829/100000000000000 : ℝ)*(major0) + (4497984877938829/100000000000000 : ℝ)*(major1) + (449798487793883/10000000000000 : ℝ)*(major2) + (6135662925365923/100000000000000 : ℝ)*(sp0) + (6135672578264089/100000000000000 : ℝ)*(sp1) + (1227134518371387/20000000000000 : ℝ)*(sp2) + (357536483036531/12500000000000 : ℝ)*(sp3) + (10096948449/100000000000000 : ℝ)*(sp4) + (4792162229/100000000000000 : ℝ)*(sp7) + (715074164113619/25000000000000 : ℝ)*(f.failure) + (1533918255578593/25000000000000 : ℝ)*(f.sum) + (46162981508549/11510000000000000000000000000 : ℝ)*base65 + (18021845136557458637/1726500000000000000000000000000000 : ℝ)*base68 + (37252158909940301/172650000000000000000000000000000 : ℝ)*base69 + (6848687388858958637/1726500000000000000000000000000000 : ℝ)*base72 + (94306603570831/11510000000000000000000000000 : ℝ)*base74 + (3879645015894559699/172650000000000000000000000000000 : ℝ)*base76 + (294702806901108637/1726500000000000000000000000000000 : ℝ)*base78 + (26719194188716608637/1726500000000000000000000000000000 : ℝ)*base80 + (4716593091413/17265000000000000000000000000 : ℝ)*base82 + (374947/2500000000000000000000 : ℝ)*base90 + (374947/2500000000000000000000 : ℝ)*base92 + (25374947/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1164710477491302422962202621/287750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1160769383/100000000000000 : ℝ)*(base23) + (66364077/25000000000000 : ℝ)*(lower1) + (13957249/25000000000000 : ℝ)*(lower2) + (87435583/100000000000000 : ℝ)*(upper3) + (41497709/100000000000000 : ℝ)*(upper4) + (51999161/100000000000000 : ℝ)*(upper5) + (4530658802956481/100000000000000 : ℝ)*(major0) + (4530658802956481/100000000000000 : ℝ)*(major1) + (4530658802956481/100000000000000 : ℝ)*(major2) + (7964872399/50000000000000 : ℝ)*(sp2) + (6180243261695497/100000000000000 : ℝ)*(sp4) + (6180243261695497/100000000000000 : ℝ)*(sp5) + (1545056542795329/25000000000000 : ℝ)*(sp6) + (1440537104647943/50000000000000 : ℝ)*(sp7) + (1440537104647943/50000000000000 : ℝ)*(f.failure) + (6180243261695497/100000000000000 : ℝ)*(f.sum) + (103663376469713/17265000000000000000000000000 : ℝ)*base65 + (7684801779507715793/1726500000000000000000000000000000 : ℝ)*base68 + (20786042447283715793/1726500000000000000000000000000000 : ℝ)*base70 + (4333545612339715793/1726500000000000000000000000000000 : ℝ)*base72 + (602651477669/134882812500000000000000000 : ℝ)*base74 + (7713206798039215793/1726500000000000000000000000000000 : ℝ)*base76 + (3391682677206715793/1726500000000000000000000000000000 : ℝ)*base78 + (24913287747861715793/1726500000000000000000000000000000 : ℝ)*base80 + (25640922534023/17265000000000000000000000000 : ℝ)*base81 + (49190441/5000000000000000000000 : ℝ)*base89 + (49190441/5000000000000000000000 : ℝ)*base91 + (49190441/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1406_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157255887/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1843/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1406_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1406_box_0 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1827607739/10000000000 : ℝ)*x 0 + (5387238123/10000000000 : ℝ)*x 1 + (1346809373/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1827607739/10000000000 : ℝ)^2183 ≤ (2714322652203/25000000000000 : ℝ)^1671 := by
    have hnat : (1827607739 : ℕ)^2183*25000000000000^1671 ≤ 2714322652203^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1827607739 10000000000 2714322652203 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387238123/10000000000 : ℝ)^2183 ≤ (22285679047573/50000000000000 : ℝ)^1671 := by
    have hnat : (5387238123 : ℕ)^2183*50000000000000^1671 ≤ 22285679047573^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387238123 10000000000 22285679047573 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346809373/2500000000 : ℝ)^2183 ≤ (44571351274959/100000000000000 : ℝ)^1671 := by
    have hnat : (1346809373 : ℕ)^2183*100000000000000^1671 ≤ 44571351274959^1671*2500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346809373 2500000000 44571351274959 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1827607739/10000000000 : ℝ), (5387238123/10000000000 : ℝ), (1346809373/2500000000 : ℝ)] ![(2714322652203/25000000000000 : ℝ), (22285679047573/50000000000000 : ℝ), (44571351274959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1827607739/10000000000 : ℝ)|^2183 ≤ (2714322652203/25000000000000 : ℝ)^1671
        have hw : |(-1827607739/10000000000 : ℝ)|=(1827607739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387238123/10000000000 : ℝ)|^2183 ≤ (22285679047573/50000000000000 : ℝ)^1671
        have hw : |(5387238123/10000000000 : ℝ)|=(5387238123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346809373/2500000000 : ℝ)|^2183 ≤ (44571351274959/100000000000000 : ℝ)^1671
        have hw : |(1346809373/2500000000 : ℝ)|=(1346809373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_box_1 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5285883023/10000000000 : ℝ)*x 0 + (-983379653/5000000000 : ℝ)*x 1 + (1346809287/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285883023/10000000000 : ℝ)^2183 ≤ (43479029011023/100000000000000 : ℝ)^1671 := by
    have hnat : (5285883023 : ℕ)^2183*100000000000000^1671 ≤ 43479029011023^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285883023 10000000000 43479029011023 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (983379653/5000000000 : ℝ)^2183 ≤ (477984936437/4000000000000 : ℝ)^1671 := by
    have hnat : (983379653 : ℕ)^2183*4000000000000^1671 ≤ 477984936437^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983379653 5000000000 477984936437 4000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346809287/2500000000 : ℝ)^2183 ≤ (44571347556821/100000000000000 : ℝ)^1671 := by
    have hnat : (1346809287 : ℕ)^2183*100000000000000^1671 ≤ 44571347556821^1671*2500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346809287 2500000000 44571347556821 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285883023/10000000000 : ℝ), (-983379653/5000000000 : ℝ), (1346809287/2500000000 : ℝ)] ![(43479029011023/100000000000000 : ℝ), (477984936437/4000000000000 : ℝ), (44571347556821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285883023/10000000000 : ℝ)|^2183 ≤ (43479029011023/100000000000000 : ℝ)^1671
        have hw : |(5285883023/10000000000 : ℝ)|=(5285883023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-983379653/5000000000 : ℝ)|^2183 ≤ (477984936437/4000000000000 : ℝ)^1671
        have hw : |(-983379653/5000000000 : ℝ)|=(983379653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346809287/2500000000 : ℝ)|^2183 ≤ (44571347556821/100000000000000 : ℝ)^1671
        have hw : |(1346809287/2500000000 : ℝ)|=(1346809287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_box_2 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2642941763/5000000000 : ℝ)*x 0 + (2693618713/5000000000 : ℝ)*x 1 + (-983379123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642941763/5000000000 : ℝ)^2183 ≤ (4347903441617/10000000000000 : ℝ)^1671 := by
    have hnat : (2642941763 : ℕ)^2183*10000000000000^1671 ≤ 4347903441617^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642941763 5000000000 4347903441617 10000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693618713/5000000000 : ℝ)^2183 ≤ (8914270112319/20000000000000 : ℝ)^1671 := by
    have hnat : (2693618713 : ℕ)^2183*20000000000000^1671 ≤ 8914270112319^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693618713 5000000000 8914270112319 20000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (983379123/5000000000 : ℝ)^2183 ≤ (11949614997243/100000000000000 : ℝ)^1671 := by
    have hnat : (983379123 : ℕ)^2183*100000000000000^1671 ≤ 11949614997243^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983379123 5000000000 11949614997243 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642941763/5000000000 : ℝ), (2693618713/5000000000 : ℝ), (-983379123/5000000000 : ℝ)] ![(4347903441617/10000000000000 : ℝ), (8914270112319/20000000000000 : ℝ), (11949614997243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642941763/5000000000 : ℝ)|^2183 ≤ (4347903441617/10000000000000 : ℝ)^1671
        have hw : |(2642941763/5000000000 : ℝ)|=(2642941763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693618713/5000000000 : ℝ)|^2183 ≤ (8914270112319/20000000000000 : ℝ)^1671
        have hw : |(2693618713/5000000000 : ℝ)|=(2693618713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-983379123/5000000000 : ℝ)|^2183 ≤ (11949614997243/100000000000000 : ℝ)^1671
        have hw : |(-983379123/5000000000 : ℝ)|=(983379123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_box_3 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2228462219/5000000000 : ℝ)*x 0 + (16564577/39062500 : ℝ)*x 1 + (4240532277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2228462219/5000000000 : ℝ)^2183 ≤ (17396765380029/50000000000000 : ℝ)^1671 := by
    have hnat : (2228462219 : ℕ)^2183*50000000000000^1671 ≤ 17396765380029^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228462219 5000000000 17396765380029 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16564577/39062500 : ℝ)^2183 ≤ (8150807943267/25000000000000 : ℝ)^1671 := by
    have hnat : (16564577 : ℕ)^2183*25000000000000^1671 ≤ 8150807943267^1671*39062500^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16564577 39062500 8150807943267 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4240532277/10000000000 : ℝ)^2183 ≤ (32603237448071/100000000000000 : ℝ)^1671 := by
    have hnat : (4240532277 : ℕ)^2183*100000000000000^1671 ≤ 32603237448071^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240532277 10000000000 32603237448071 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2228462219/5000000000 : ℝ), (16564577/39062500 : ℝ), (4240532277/10000000000 : ℝ)] ![(17396765380029/50000000000000 : ℝ), (8150807943267/25000000000000 : ℝ), (32603237448071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2228462219/5000000000 : ℝ)|^2183 ≤ (17396765380029/50000000000000 : ℝ)^1671
        have hw : |(2228462219/5000000000 : ℝ)|=(2228462219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16564577/39062500 : ℝ)|^2183 ≤ (8150807943267/25000000000000 : ℝ)^1671
        have hw : |(16564577/39062500 : ℝ)|=(16564577/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4240532277/10000000000 : ℝ)|^2183 ≤ (32603237448071/100000000000000 : ℝ)^1671
        have hw : |(4240532277/10000000000 : ℝ)|=(4240532277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_box_4 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2155026479/10000000000 : ℝ)*x 0 + (1316541661/2500000000 : ℝ)*x 1 + (5266167203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155026479/10000000000 : ℝ)^2183 ≤ (13465430940029/100000000000000 : ℝ)^1671 := by
    have hnat : (2155026479 : ℕ)^2183*100000000000000^1671 ≤ 13465430940029^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155026479 10000000000 13465430940029 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316541661/2500000000 : ℝ)^2183 ≤ (43267281520377/100000000000000 : ℝ)^1671 := by
    have hnat : (1316541661 : ℕ)^2183*100000000000000^1671 ≤ 43267281520377^1671*2500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316541661 2500000000 43267281520377 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266167203/10000000000 : ℝ)^2183 ≤ (43267287520417/100000000000000 : ℝ)^1671 := by
    have hnat : (5266167203 : ℕ)^2183*100000000000000^1671 ≤ 43267287520417^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266167203 10000000000 43267287520417 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2155026479/10000000000 : ℝ), (1316541661/2500000000 : ℝ), (5266167203/10000000000 : ℝ)] ![(13465430940029/100000000000000 : ℝ), (43267281520377/100000000000000 : ℝ), (43267287520417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2155026479/10000000000 : ℝ)|^2183 ≤ (13465430940029/100000000000000 : ℝ)^1671
        have hw : |(-2155026479/10000000000 : ℝ)|=(2155026479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316541661/2500000000 : ℝ)|^2183 ≤ (43267281520377/100000000000000 : ℝ)^1671
        have hw : |(1316541661/2500000000 : ℝ)|=(1316541661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266167203/10000000000 : ℝ)|^2183 ≤ (43267287520417/100000000000000 : ℝ)^1671
        have hw : |(5266167203/10000000000 : ℝ)|=(5266167203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_box_5 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5370694327/10000000000 : ℝ)*x 0 + (-2015766503/10000000000 : ℝ)*x 1 + (5266166551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370694327/10000000000 : ℝ)^2183 ≤ (11098157005741/25000000000000 : ℝ)^1671 := by
    have hnat : (5370694327 : ℕ)^2183*25000000000000^1671 ≤ 11098157005741^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370694327 10000000000 11098157005741 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015766503/10000000000 : ℝ)^2183 ≤ (6170045717641/50000000000000 : ℝ)^1671 := by
    have hnat : (2015766503 : ℕ)^2183*50000000000000^1671 ≤ 6170045717641^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015766503 10000000000 6170045717641 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266166551/10000000000 : ℝ)^2183 ≤ (43267280522159/100000000000000 : ℝ)^1671 := by
    have hnat : (5266166551 : ℕ)^2183*100000000000000^1671 ≤ 43267280522159^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266166551 10000000000 43267280522159 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370694327/10000000000 : ℝ), (-2015766503/10000000000 : ℝ), (5266166551/10000000000 : ℝ)] ![(11098157005741/25000000000000 : ℝ), (6170045717641/50000000000000 : ℝ), (43267280522159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370694327/10000000000 : ℝ)|^2183 ≤ (11098157005741/25000000000000 : ℝ)^1671
        have hw : |(5370694327/10000000000 : ℝ)|=(5370694327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2015766503/10000000000 : ℝ)|^2183 ≤ (6170045717641/50000000000000 : ℝ)^1671
        have hw : |(-2015766503/10000000000 : ℝ)|=(2015766503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266166551/10000000000 : ℝ)|^2183 ≤ (43267280522159/100000000000000 : ℝ)^1671
        have hw : |(5266166551/10000000000 : ℝ)|=(5266166551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_box_6 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5370694299/10000000000 : ℝ)*x 0 + (2633083441/5000000000 : ℝ)*x 1 + (-2015766097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370694299/10000000000 : ℝ)^2183 ≤ (4439262772061/10000000000000 : ℝ)^1671 := by
    have hnat : (5370694299 : ℕ)^2183*10000000000000^1671 ≤ 4439262772061^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370694299 10000000000 4439262772061 10000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633083441/5000000000 : ℝ)^2183 ≤ (8653456814991/20000000000000 : ℝ)^1671 := by
    have hnat : (2633083441 : ℕ)^2183*20000000000000^1671 ≤ 8653456814991^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633083441 5000000000 8653456814991 20000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015766097/10000000000 : ℝ)^2183 ≤ (96406938971/781250000000 : ℝ)^1671 := by
    have hnat : (2015766097 : ℕ)^2183*781250000000^1671 ≤ 96406938971^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015766097 10000000000 96406938971 781250000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370694299/10000000000 : ℝ), (2633083441/5000000000 : ℝ), (-2015766097/10000000000 : ℝ)] ![(4439262772061/10000000000000 : ℝ), (8653456814991/20000000000000 : ℝ), (96406938971/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370694299/10000000000 : ℝ)|^2183 ≤ (4439262772061/10000000000000 : ℝ)^1671
        have hw : |(5370694299/10000000000 : ℝ)|=(5370694299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633083441/5000000000 : ℝ)|^2183 ≤ (8653456814991/20000000000000 : ℝ)^1671
        have hw : |(2633083441/5000000000 : ℝ)|=(2633083441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2015766097/10000000000 : ℝ)|^2183 ≤ (96406938971/781250000000 : ℝ)^1671
        have hw : |(-2015766097/10000000000 : ℝ)|=(2015766097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_box_7 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (41623791/100000000 : ℝ)*x 0 + (4387753379/10000000000 : ℝ)*x 1 + (548469103/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41623791/100000000 : ℝ)^2183 ≤ (31820473121371/100000000000000 : ℝ)^1671 := by
    have hnat : (41623791 : ℕ)^2183*100000000000000^1671 ≤ 31820473121371^1671*100000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41623791 100000000 31820473121371 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4387753379/10000000000 : ℝ)^2183 ≤ (136359065003/400000000000 : ℝ)^1671 := by
    have hnat : (4387753379 : ℕ)^2183*400000000000^1671 ≤ 136359065003^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4387753379 10000000000 136359065003 400000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548469103/1250000000 : ℝ)^2183 ≤ (3408976061759/10000000000000 : ℝ)^1671 := by
    have hnat : (548469103 : ℕ)^2183*10000000000000^1671 ≤ 3408976061759^1671*1250000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548469103 1250000000 3408976061759 10000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41623791/100000000 : ℝ), (4387753379/10000000000 : ℝ), (548469103/1250000000 : ℝ)] ![(31820473121371/100000000000000 : ℝ), (136359065003/400000000000 : ℝ), (3408976061759/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41623791/100000000 : ℝ)|^2183 ≤ (31820473121371/100000000000000 : ℝ)^1671
        have hw : |(41623791/100000000 : ℝ)|=(41623791/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4387753379/10000000000 : ℝ)|^2183 ≤ (136359065003/400000000000 : ℝ)^1671
        have hw : |(4387753379/10000000000 : ℝ)|=(4387753379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(548469103/1250000000 : ℝ)|^2183 ≤ (3408976061759/10000000000000 : ℝ)^1671
        have hw : |(548469103/1250000000 : ℝ)|=(548469103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_box_8 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2086113701/10000000000 : ℝ)*x 0 + (1295631833/2500000000 : ℝ)*x 1 + (675153077/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086113701/10000000000 : ℝ)^2183 ≤ (12905678737993/100000000000000 : ℝ)^1671 := by
    have hnat : (2086113701 : ℕ)^2183*100000000000000^1671 ≤ 12905678737993^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086113701 10000000000 12905678737993 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295631833/2500000000 : ℝ)^2183 ≤ (42371729504119/100000000000000 : ℝ)^1671 := by
    have hnat : (1295631833 : ℕ)^2183*100000000000000^1671 ≤ 42371729504119^1671*2500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295631833 2500000000 42371729504119 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675153077/1250000000 : ℝ)^2183 ≤ (11180647934573/25000000000000 : ℝ)^1671 := by
    have hnat : (675153077 : ℕ)^2183*25000000000000^1671 ≤ 11180647934573^1671*1250000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675153077 1250000000 11180647934573 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2086113701/10000000000 : ℝ), (1295631833/2500000000 : ℝ), (675153077/1250000000 : ℝ)] ![(12905678737993/100000000000000 : ℝ), (42371729504119/100000000000000 : ℝ), (11180647934573/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2086113701/10000000000 : ℝ)|^2183 ≤ (12905678737993/100000000000000 : ℝ)^1671
        have hw : |(-2086113701/10000000000 : ℝ)|=(2086113701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295631833/2500000000 : ℝ)|^2183 ≤ (42371729504119/100000000000000 : ℝ)^1671
        have hw : |(1295631833/2500000000 : ℝ)|=(1295631833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675153077/1250000000 : ℝ)|^2183 ≤ (11180647934573/25000000000000 : ℝ)^1671
        have hw : |(675153077/1250000000 : ℝ)|=(675153077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_box_9 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5276079977/10000000000 : ℝ)*x 0 + (-1960969491/10000000000 : ℝ)*x 1 + (337576557/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276079977/10000000000 : ℝ)^2183 ≤ (43373717183/100000000000 : ℝ)^1671 := by
    have hnat : (5276079977 : ℕ)^2183*100000000000^1671 ≤ 43373717183^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276079977 10000000000 43373717183 100000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1960969491/10000000000 : ℝ)^2183 ≤ (5951843929799/50000000000000 : ℝ)^1671 := by
    have hnat : (1960969491 : ℕ)^2183*50000000000000^1671 ≤ 5951843929799^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960969491 10000000000 5951843929799 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337576557/625000000 : ℝ)^2183 ≤ (22361297470081/50000000000000 : ℝ)^1671 := by
    have hnat : (337576557 : ℕ)^2183*50000000000000^1671 ≤ 22361297470081^1671*625000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337576557 625000000 22361297470081 50000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276079977/10000000000 : ℝ), (-1960969491/10000000000 : ℝ), (337576557/625000000 : ℝ)] ![(43373717183/100000000000 : ℝ), (5951843929799/50000000000000 : ℝ), (22361297470081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276079977/10000000000 : ℝ)|^2183 ≤ (43373717183/100000000000 : ℝ)^1671
        have hw : |(5276079977/10000000000 : ℝ)|=(5276079977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1960969491/10000000000 : ℝ)|^2183 ≤ (5951843929799/50000000000000 : ℝ)^1671
        have hw : |(-1960969491/10000000000 : ℝ)|=(1960969491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337576557/625000000 : ℝ)|^2183 ≤ (22361297470081/50000000000000 : ℝ)^1671
        have hw : |(337576557/625000000 : ℝ)|=(337576557/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_box_10 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2638040263/5000000000 : ℝ)*x 0 + (2700612589/5000000000 : ℝ)*x 1 + (-392193677/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638040263/5000000000 : ℝ)^2183 ≤ (43373723079101/100000000000000 : ℝ)^1671 := by
    have hnat : (2638040263 : ℕ)^2183*100000000000000^1671 ≤ 43373723079101^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638040263 5000000000 43373723079101 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700612589/5000000000 : ℝ)^2183 ≤ (44722597817519/100000000000000 : ℝ)^1671 := by
    have hnat : (2700612589 : ℕ)^2183*100000000000000^1671 ≤ 44722597817519^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700612589 5000000000 44722597817519 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (392193677/2000000000 : ℝ)^2183 ≤ (148795988609/1250000000000 : ℝ)^1671 := by
    have hnat : (392193677 : ℕ)^2183*1250000000000^1671 ≤ 148795988609^1671*2000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392193677 2000000000 148795988609 1250000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638040263/5000000000 : ℝ), (2700612589/5000000000 : ℝ), (-392193677/2000000000 : ℝ)] ![(43373723079101/100000000000000 : ℝ), (44722597817519/100000000000000 : ℝ), (148795988609/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638040263/5000000000 : ℝ)|^2183 ≤ (43373723079101/100000000000000 : ℝ)^1671
        have hw : |(2638040263/5000000000 : ℝ)|=(2638040263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700612589/5000000000 : ℝ)|^2183 ≤ (44722597817519/100000000000000 : ℝ)^1671
        have hw : |(2700612589/5000000000 : ℝ)|=(2700612589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-392193677/2000000000 : ℝ)|^2183 ≤ (148795988609/1250000000000 : ℝ)^1671
        have hw : |(-392193677/2000000000 : ℝ)|=(392193677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_box_11 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2245198477/5000000000 : ℝ)*x 0 + (211175467/500000000 : ℝ)*x 1 + (2111753889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2245198477/5000000000 : ℝ)^2183 ≤ (8783823906361/25000000000000 : ℝ)^1671 := by
    have hnat : (2245198477 : ℕ)^2183*25000000000000^1671 ≤ 8783823906361^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245198477 5000000000 8783823906361 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211175467/500000000 : ℝ)^2183 ≤ (1013511250509/3125000000000 : ℝ)^1671 := by
    have hnat : (211175467 : ℕ)^2183*3125000000000^1671 ≤ 1013511250509^1671*500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211175467 500000000 1013511250509 3125000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111753889/5000000000 : ℝ)^2183 ≤ (3243234434649/10000000000000 : ℝ)^1671 := by
    have hnat : (2111753889 : ℕ)^2183*10000000000000^1671 ≤ 3243234434649^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111753889 5000000000 3243234434649 10000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2245198477/5000000000 : ℝ), (211175467/500000000 : ℝ), (2111753889/5000000000 : ℝ)] ![(8783823906361/25000000000000 : ℝ), (1013511250509/3125000000000 : ℝ), (3243234434649/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2245198477/5000000000 : ℝ)|^2183 ≤ (8783823906361/25000000000000 : ℝ)^1671
        have hw : |(2245198477/5000000000 : ℝ)|=(2245198477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211175467/500000000 : ℝ)|^2183 ≤ (1013511250509/3125000000000 : ℝ)^1671
        have hw : |(211175467/500000000 : ℝ)|=(211175467/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2111753889/5000000000 : ℝ)|^2183 ≤ (3243234434649/10000000000000 : ℝ)^1671
        have hw : |(2111753889/5000000000 : ℝ)|=(2111753889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_box_12 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1896740137/10000000000 : ℝ)*x 0 + (5468808563/10000000000 : ℝ)*x 1 + (2627526861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1896740137/10000000000 : ℝ)^2183 ≤ (11396907285709/100000000000000 : ℝ)^1671 := by
    have hnat : (1896740137 : ℕ)^2183*100000000000000^1671 ≤ 11396907285709^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896740137 10000000000 11396907285709 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468808563/10000000000 : ℝ)^2183 ≤ (909101068177/2000000000000 : ℝ)^1671 := by
    have hnat : (5468808563 : ℕ)^2183*2000000000000^1671 ≤ 909101068177^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468808563 10000000000 909101068177 2000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627526861/5000000000 : ℝ)^2183 ≤ (43148039296397/100000000000000 : ℝ)^1671 := by
    have hnat : (2627526861 : ℕ)^2183*100000000000000^1671 ≤ 43148039296397^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627526861 5000000000 43148039296397 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1896740137/10000000000 : ℝ), (5468808563/10000000000 : ℝ), (2627526861/5000000000 : ℝ)] ![(11396907285709/100000000000000 : ℝ), (909101068177/2000000000000 : ℝ), (43148039296397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1896740137/10000000000 : ℝ)|^2183 ≤ (11396907285709/100000000000000 : ℝ)^1671
        have hw : |(-1896740137/10000000000 : ℝ)|=(1896740137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468808563/10000000000 : ℝ)|^2183 ≤ (909101068177/2000000000000 : ℝ)^1671
        have hw : |(5468808563/10000000000 : ℝ)|=(5468808563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627526861/5000000000 : ℝ)|^2183 ≤ (43148039296397/100000000000000 : ℝ)^1671
        have hw : |(2627526861/5000000000 : ℝ)|=(2627526861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_box_13 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5378477771/10000000000 : ℝ)*x 0 + (-2020164237/10000000000 : ℝ)*x 1 + (1313763231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378477771/10000000000 : ℝ)^2183 ≤ (347474180387/781250000000 : ℝ)^1671 := by
    have hnat : (5378477771 : ℕ)^2183*781250000000^1671 ≤ 347474180387^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378477771 10000000000 347474180387 781250000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2020164237/10000000000 : ℝ)^2183 ≤ (12375274158829/100000000000000 : ℝ)^1671 := by
    have hnat : (2020164237 : ℕ)^2183*100000000000000^1671 ≤ 12375274158829^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020164237 10000000000 12375274158829 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313763231/2500000000 : ℝ)^2183 ≤ (10787007684147/25000000000000 : ℝ)^1671 := by
    have hnat : (1313763231 : ℕ)^2183*25000000000000^1671 ≤ 10787007684147^1671*2500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313763231 2500000000 10787007684147 25000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378477771/10000000000 : ℝ), (-2020164237/10000000000 : ℝ), (1313763231/2500000000 : ℝ)] ![(347474180387/781250000000 : ℝ), (12375274158829/100000000000000 : ℝ), (10787007684147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378477771/10000000000 : ℝ)|^2183 ≤ (347474180387/781250000000 : ℝ)^1671
        have hw : |(5378477771/10000000000 : ℝ)|=(5378477771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2020164237/10000000000 : ℝ)|^2183 ≤ (12375274158829/100000000000000 : ℝ)^1671
        have hw : |(-2020164237/10000000000 : ℝ)|=(2020164237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313763231/2500000000 : ℝ)|^2183 ≤ (10787007684147/25000000000000 : ℝ)^1671
        have hw : |(1313763231/2500000000 : ℝ)|=(1313763231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_box_14 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (21009677/39062500 : ℝ)*x 0 + (2627526649/5000000000 : ℝ)*x 1 + (-505041089/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21009677/39062500 : ℝ)^2183 ≤ (4447669013089/10000000000000 : ℝ)^1671 := by
    have hnat : (21009677 : ℕ)^2183*10000000000000^1671 ≤ 4447669013089^1671*39062500^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21009677 39062500 4447669013089 10000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627526649/5000000000 : ℝ)^2183 ≤ (5393504343541/12500000000000 : ℝ)^1671 := by
    have hnat : (2627526649 : ℕ)^2183*12500000000000^1671 ≤ 5393504343541^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627526649 5000000000 5393504343541 12500000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (505041089/2500000000 : ℝ)^2183 ≤ (1237527511117/10000000000000 : ℝ)^1671 := by
    have hnat : (505041089 : ℕ)^2183*10000000000000^1671 ≤ 1237527511117^1671*2500000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505041089 2500000000 1237527511117 10000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21009677/39062500 : ℝ), (2627526649/5000000000 : ℝ), (-505041089/2500000000 : ℝ)] ![(4447669013089/10000000000000 : ℝ), (5393504343541/12500000000000 : ℝ), (1237527511117/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21009677/39062500 : ℝ)|^2183 ≤ (4447669013089/10000000000000 : ℝ)^1671
        have hw : |(21009677/39062500 : ℝ)|=(21009677/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627526649/5000000000 : ℝ)|^2183 ≤ (5393504343541/12500000000000 : ℝ)^1671
        have hw : |(2627526649/5000000000 : ℝ)|=(2627526649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-505041089/2500000000 : ℝ)|^2183 ≤ (1237527511117/10000000000000 : ℝ)^1671
        have hw : |(-505041089/2500000000 : ℝ)|=(505041089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1406_box_15 (p : ℝ) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4134892117/10000000000 : ℝ)*x 0 + (2200628359/5000000000 : ℝ)*x 1 + (4401255807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4134892117/10000000000 : ℝ)^2183 ≤ (31546234200443/100000000000000 : ℝ)^1671 := by
    have hnat : (4134892117 : ℕ)^2183*100000000000000^1671 ≤ 31546234200443^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134892117 10000000000 31546234200443 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2200628359/5000000000 : ℝ)^2183 ≤ (34226887524111/100000000000000 : ℝ)^1671 := by
    have hnat : (2200628359 : ℕ)^2183*100000000000000^1671 ≤ 34226887524111^1671*5000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200628359 5000000000 34226887524111 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4401255807/10000000000 : ℝ)^2183 ≤ (34226878268899/100000000000000 : ℝ)^1671 := by
    have hnat : (4401255807 : ℕ)^2183*100000000000000^1671 ≤ 34226878268899^1671*10000000000^2183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4401255807 10000000000 34226878268899 100000000000000 2183 1671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2183/512 : ℝ)) 2183 1671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4134892117/10000000000 : ℝ), (2200628359/5000000000 : ℝ), (4401255807/10000000000 : ℝ)] ![(31546234200443/100000000000000 : ℝ), (34226887524111/100000000000000 : ℝ), (34226878268899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4134892117/10000000000 : ℝ)|^2183 ≤ (31546234200443/100000000000000 : ℝ)^1671
        have hw : |(4134892117/10000000000 : ℝ)|=(4134892117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2200628359/5000000000 : ℝ)|^2183 ≤ (34226887524111/100000000000000 : ℝ)^1671
        have hw : |(2200628359/5000000000 : ℝ)|=(2200628359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4401255807/10000000000 : ℝ)|^2183 ≤ (34226878268899/100000000000000 : ℝ)^1671
        have hw : |(4401255807/10000000000 : ℝ)|=(4401255807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1406_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157255887/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1843/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31443/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59067/100000 : ℝ) ∧ (80321/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42299/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1843/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11293/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1843/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11293/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1843/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11293/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1843/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11293/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1843/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11293/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1843/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11293/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11293/100000 : ℝ) ^ (4365/1024 : ℝ) ≤ (1834191847059371/20000000000000000000 : ℝ) := by
    have hpowers : (11293/100000 : ℝ)^4365 ≤ (1834191847059371/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11293 : ℕ)^4365*20000000000000000000^1024 ≤ 1834191847059371^1024*100000^4365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11293 100000 1834191847059371 20000000000000000000 4365 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11293/100000 : ℝ)) (X := (1834191847059371/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1843/12500 : ℝ) ^ (4365/1024 : ℝ) ≤ (1428994099182709/5000000000000000000 : ℝ) := by
    have hpowers : (1843/12500 : ℝ)^4365 ≤ (1428994099182709/5000000000000000000 : ℝ)^1024 := by
      have hnat : (1843 : ℕ)^4365*5000000000000000000^1024 ≤ 1428994099182709^1024*12500^4365 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1843 12500 1428994099182709 5000000000000000000 4365 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1843/12500 : ℝ)) (X := (1428994099182709/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001834191847059371/10000000000000000000 : ℝ) ≤ (10000430259020447/10000000000000000 : ℝ) ^ (4365/1024 : ℝ) := by
    have hpowers : (10001834191847059371/10000000000000000000 : ℝ)^1024 ≤ (10000430259020447/10000000000000000 : ℝ)^4365 := by
      have hnat : (10001834191847059371 : ℕ)^1024*10000000000000000^4365 ≤ 10000430259020447^4365*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001834191847059371 10000000000000000000 10000430259020447 10000000000000000 1024 4365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000430259020447/10000000000000000 : ℝ)) (X := (10001834191847059371/10000000000000000000 : ℝ)) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007550168243790207/20000000000000000000 : ℝ) ≤ (10000885481735347/10000000000000000 : ℝ) ^ (4365/1024 : ℝ) := by
    have hpowers : (20007550168243790207/20000000000000000000 : ℝ)^1024 ≤ (10000885481735347/10000000000000000 : ℝ)^4365 := by
      have hnat : (20007550168243790207 : ℕ)^1024*10000000000000000^4365 ≤ 10000885481735347^4365*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007550168243790207 20000000000000000000 10000885481735347 10000000000000000 1024 4365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000885481735347/10000000000000000 : ℝ)) (X := (20007550168243790207/20000000000000000000 : ℝ)) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501428994099182709/2500000000000000000 : ℝ) ≤ (10001340704450247/10000000000000000 : ℝ) ^ (4365/1024 : ℝ) := by
    have hpowers : (2501428994099182709/2500000000000000000 : ℝ)^1024 ≤ (10001340704450247/10000000000000000 : ℝ)^4365 := by
      have hnat : (2501428994099182709 : ℕ)^1024*10000000000000000^4365 ≤ 10001340704450247^4365*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501428994099182709 2500000000000000000 10001340704450247 10000000000000000 1024 4365 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001340704450247/10000000000000000 : ℝ)) (X := (2501428994099182709/2500000000000000000 : ℝ)) (by norm_num) 4365 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1834191847059371/20000000000000000000 : ℝ) ≤ ((34501203163640831197/34510000000000000000 : ℝ)+2*(4552227149/3451000000000 : ℝ)*(11293/100000 : ℝ))^(4365/1024 : ℝ) := by
    rw [show (34501203163640831197/34510000000000000000 : ℝ)+2*(4552227149/3451000000000 : ℝ)*(11293/100000 : ℝ)=(10000430259020447/10000000000000000 : ℝ) by norm_num, show 1+2*(1834191847059371/20000000000000000000 : ℝ)=(10001834191847059371/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1428994099182709/5000000000000000000 : ℝ)+(1834191847059371/20000000000000000000 : ℝ) ≤ ((34501203163640831197/34510000000000000000 : ℝ)+(4552227149/3451000000000 : ℝ)*((1843/12500 : ℝ)+(11293/100000 : ℝ)))^(4365/1024 : ℝ) := by
    rw [show (34501203163640831197/34510000000000000000 : ℝ)+(4552227149/3451000000000 : ℝ)*((1843/12500 : ℝ)+(11293/100000 : ℝ))=(10000885481735347/10000000000000000 : ℝ) by norm_num, show 1+(1428994099182709/5000000000000000000 : ℝ)+(1834191847059371/20000000000000000000 : ℝ)=(20007550168243790207/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1428994099182709/5000000000000000000 : ℝ) ≤ ((34501203163640831197/34510000000000000000 : ℝ)+2*(4552227149/3451000000000 : ℝ)*(1843/12500 : ℝ))^(4365/1024 : ℝ) := by
    rw [show (34501203163640831197/34510000000000000000 : ℝ)+2*(4552227149/3451000000000 : ℝ)*(1843/12500 : ℝ)=(10001340704450247/10000000000000000 : ℝ) by norm_num, show 1+2*(1428994099182709/5000000000000000000 : ℝ)=(2501428994099182709/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34501203163640831197/34510000000000000000 : ℝ)*(X 1 0+X 2 0)+(4552227149/3451000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4365/1024 : ℝ)) (lo := (11293/100000 : ℝ)) (hi := (1843/12500 : ℝ)) (c := (34501203163640831197/34510000000000000000 : ℝ)) (alpha := (4552227149/3451000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34501203163640831197/34510000000000000000 : ℝ)*(X 0 1+X 2 1)+(4552227149/3451000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4365/1024 : ℝ)) (lo := (11293/100000 : ℝ)) (hi := (1843/12500 : ℝ)) (c := (34501203163640831197/34510000000000000000 : ℝ)) (alpha := (4552227149/3451000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34501203163640831197/34510000000000000000 : ℝ)*(X 0 2+X 1 2)+(4552227149/3451000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4365/1024 : ℝ)) (lo := (11293/100000 : ℝ)) (hi := (1843/12500 : ℝ)) (c := (34501203163640831197/34510000000000000000 : ℝ)) (alpha := (4552227149/3451000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1827607739/10000000000 : ℝ)*X 0 0+(5387238123/10000000000 : ℝ)*X 0 1+(1346809373/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285883023/10000000000 : ℝ)*X 1 0+(-983379653/5000000000 : ℝ)*X 1 1+(1346809287/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642941763/5000000000 : ℝ)*X 2 0+(2693618713/5000000000 : ℝ)*X 2 1+(-983379123/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2228462219/5000000000 : ℝ)*X 0 0+(16564577/39062500 : ℝ)*X 0 1+(4240532277/10000000000 : ℝ)*X 0 2+(2228462219/5000000000 : ℝ)*X 1 0+(16564577/39062500 : ℝ)*X 1 1+(4240532277/10000000000 : ℝ)*X 1 2+(2228462219/5000000000 : ℝ)*X 2 0+(16564577/39062500 : ℝ)*X 2 1+(4240532277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2155026479/10000000000 : ℝ)*X 0 0+(1316541661/2500000000 : ℝ)*X 0 1+(5266167203/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5370694327/10000000000 : ℝ)*X 1 0+(-2015766503/10000000000 : ℝ)*X 1 1+(5266166551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5370694299/10000000000 : ℝ)*X 2 0+(2633083441/5000000000 : ℝ)*X 2 1+(-2015766097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((41623791/100000000 : ℝ)*X 0 0+(4387753379/10000000000 : ℝ)*X 0 1+(548469103/1250000000 : ℝ)*X 0 2+(41623791/100000000 : ℝ)*X 1 0+(4387753379/10000000000 : ℝ)*X 1 1+(548469103/1250000000 : ℝ)*X 1 2+(41623791/100000000 : ℝ)*X 2 0+(4387753379/10000000000 : ℝ)*X 2 1+(548469103/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2086113701/10000000000 : ℝ)*X 0 0+(1295631833/2500000000 : ℝ)*X 0 1+(675153077/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276079977/10000000000 : ℝ)*X 1 0+(-1960969491/10000000000 : ℝ)*X 1 1+(337576557/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2638040263/5000000000 : ℝ)*X 2 0+(2700612589/5000000000 : ℝ)*X 2 1+(-392193677/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2245198477/5000000000 : ℝ)*X 0 0+(211175467/500000000 : ℝ)*X 0 1+(2111753889/5000000000 : ℝ)*X 0 2+(2245198477/5000000000 : ℝ)*X 1 0+(211175467/500000000 : ℝ)*X 1 1+(2111753889/5000000000 : ℝ)*X 1 2+(2245198477/5000000000 : ℝ)*X 2 0+(211175467/500000000 : ℝ)*X 2 1+(2111753889/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1896740137/10000000000 : ℝ)*X 0 0+(5468808563/10000000000 : ℝ)*X 0 1+(2627526861/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5378477771/10000000000 : ℝ)*X 1 0+(-2020164237/10000000000 : ℝ)*X 1 1+(1313763231/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((21009677/39062500 : ℝ)*X 2 0+(2627526649/5000000000 : ℝ)*X 2 1+(-505041089/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4134892117/10000000000 : ℝ)*X 0 0+(2200628359/5000000000 : ℝ)*X 0 1+(4401255807/10000000000 : ℝ)*X 0 2+(4134892117/10000000000 : ℝ)*X 1 0+(2200628359/5000000000 : ℝ)*X 1 1+(4401255807/10000000000 : ℝ)*X 1 2+(4134892117/10000000000 : ℝ)*X 2 0+(2200628359/5000000000 : ℝ)*X 2 1+(4401255807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1406_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31443/50000 : ℝ) ≤ (-1139760750733282545650559534603/1812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (95718361/100000000000000 : ℝ)*(lower0) + (105946209/100000000000000 : ℝ)*(lower2) + (88813347/100000000000000 : ℝ)*(lower3) + (747927434651173/25000000000000 : ℝ)*(major0) + (747927434651173/25000000000000 : ℝ)*(major1) + (747927434651173/25000000000000 : ℝ)*(major2) + (14699015833/100000000000000 : ℝ)*(sp1) + (3411193/400000000000 : ℝ)*(sp2) + (4101933096340229/100000000000000 : ℝ)*(sp4) + (512739875122147/12500000000000 : ℝ)*(sp5) + (4101932847194759/100000000000000 : ℝ)*(sp6) + (380481828393107/20000000000000 : ℝ)*(sp7) + (30182639/5000000000000 : ℝ)*(sp12) + (37752505699/100000000000000 : ℝ)*(sp15) + (951223447235617/50000000000000 : ℝ)*(f.failure) + (4101933699993009/100000000000000 : ℝ)*(f.sum) + (22016992853/7250000000000000000000000 : ℝ)*base65 + (75379196289178201/7250000000000000000000000000000 : ℝ)*base68 + (31384139587428201/7250000000000000000000000000000 : ℝ)*base70 + (63876141338928201/7250000000000000000000000000000 : ℝ)*base72 + (23080059231/29000000000000000000000000 : ℝ)*base73 + (56900134781678201/7250000000000000000000000000000 : ℝ)*base76 + (23718179368571799/7250000000000000000000000000000 : ℝ)*base77 + (81898391373678201/7250000000000000000000000000000 : ℝ)*base80 + (7449797/580000000000000000000000 : ℝ)*base82 + (49327279/5000000000000000000000 : ℝ)*base89 + (49327279/5000000000000000000000 : ℝ)*base91 + (49327279/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59067/100000 : ℝ) ≤ (509623455908583185511012025492101/862750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (366390251/100000000000000 : ℝ)*(lower1) + (24341719/25000000000000 : ℝ)*(lower2) + (211981003/50000000000000 : ℝ)*(upper4) + (3062544421477223/100000000000000 : ℝ)*(major0) + (3062544421477223/100000000000000 : ℝ)*(major1) + (382818052684653/12500000000000 : ℝ)*(major2) + (2078948759950507/50000000000000 : ℝ)*(sp0) + (2078766664506133/50000000000000 : ℝ)*(sp1) + (2078925893514761/50000000000000 : ℝ)*(sp2) + (486872364258321/25000000000000 : ℝ)*(sp3) + (1654366077/100000000000000 : ℝ)*(sp7) + (1032636831/10000000000000 : ℝ)*(sp8) + (187258628529/50000000000000 : ℝ)*(sp9) + (28029619901/50000000000000 : ℝ)*(sp10) + (1947491111399361/100000000000000 : ℝ)*(f.failure) + (1039476961567331/25000000000000 : ℝ)*(f.sum) + (9854945094697/1725500000000000000000000000 : ℝ)*base65 + (13023602531799674069/3451000000000000000000000000000000 : ℝ)*base68 + (28818146728435039/3625000000000000000000000000000 : ℝ)*base69 + (19863970580992674069/3451000000000000000000000000000000 : ℝ)*base72 + (3538714420863/3451000000000000000000000000 : ℝ)*base73 + (19696376470435039/3625000000000000000000000000000 : ℝ)*base75 + (11723246823122674069/3451000000000000000000000000000000 : ℝ)*base78 + (12056668649475674069/3451000000000000000000000000000000 : ℝ)*base80 + (7988846469347/1725500000000000000000000000 : ℝ)*base82 + (25288207/10000000000000000000000 : ℝ)*base89 + (25288207/10000000000000000000000 : ℝ)*base91 + (74711793/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80321/100000 : ℝ) ≤ (27719557819738921649544930684603/34510000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75948929/50000000000000 : ℝ)*(lower3) + (19748773/3125000000000 : ℝ)*(upper4) + (206002801/100000000000000 : ℝ)*(lower5) + (67434244207133/2000000000000 : ℝ)*(major0) + (67434244207133/2000000000000 : ℝ)*(major1) + (67434244207133/2000000000000 : ℝ)*(major2) + (9850189969/100000000000000 : ℝ)*(sp0) + (53801152951/25000000000000 : ℝ)*(sp1) + (603788044281/100000000000000 : ℝ)*(sp2) + (147935212081/50000000000000 : ℝ)*(sp3) + (914509462369609/20000000000000 : ℝ)*(sp8) + (457234195742621/10000000000000 : ℝ)*(sp9) + (4571953373993733/100000000000000 : ℝ)*(sp10) + (535949241871111/25000000000000 : ℝ)*(sp11) + (1072046418954303/50000000000000 : ℝ)*(f.failure) + (2286278581019007/50000000000000 : ℝ)*(f.sum) + (428452995497/107843750000000000000000000 : ℝ)*base65 + (695265646941291799/69020000000000000000000000000000 : ℝ)*base68 + (26491032604848201/69020000000000000000000000000000 : ℝ)*base69 + (432102287036448201/69020000000000000000000000000000 : ℝ)*base71 + (2048272054467/345100000000000000000000000 : ℝ)*base74 + (446796020332031799/69020000000000000000000000000000 : ℝ)*base76 + (335314369555591799/69020000000000000000000000000000 : ℝ)*base78 + (185208954919351799/69020000000000000000000000000000 : ℝ)*base80 + (51272870269/138040000000000000000000000 : ℝ)*base82 + (30731761/5000000000000000000000 : ℝ)*base89 + (30731761/5000000000000000000000 : ℝ)*base91 + (30731761/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-42299/50000 : ℝ) ≤ (-364923992182024203528960471968649/431375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (118136779/100000000000000 : ℝ)*(lower0) + (40893827/25000000000000 : ℝ)*(upper1) + (6566591/4000000000000 : ℝ)*(lower4) + (1704447093340723/50000000000000 : ℝ)*(major0) + (1704447093340723/50000000000000 : ℝ)*(major1) + (426111773335181/12500000000000 : ℝ)*(major2) + (1547687229/100000000000000 : ℝ)*(sp4) + (95139527403/50000000000000 : ℝ)*(sp5) + (15664843777/12500000000000 : ℝ)*(sp6) + (32954502451/100000000000000 : ℝ)*(sp7) + (1169562062217089/25000000000000 : ℝ)*(sp12) + (4678059517500779/100000000000000 : ℝ)*(sp13) + (4678124477805369/100000000000000 : ℝ)*(sp14) + (270963016776147/12500000000000 : ℝ)*(sp15) + (541934272177907/25000000000000 : ℝ)*(f.failure) + (935649959311117/20000000000000 : ℝ)*(f.sum) + (4232318103781/3451000000000000000000000000 : ℝ)*base65 + (3893596881816564569/1725500000000000000000000000000000 : ℝ)*base68 + (741193840721330951/61625000000000000000000000000000 : ℝ)*base69 + (22652733629097564569/1725500000000000000000000000000000 : ℝ)*base72 + (41709328984151/862750000000000000000000000 : ℝ)*base73 + (1310507135868955951/61625000000000000000000000000000 : ℝ)*base75 + (20561288927583064569/1725500000000000000000000000000000 : ℝ)*base78 + (76820756352341564569/1725500000000000000000000000000000 : ℝ)*base80 + (1367237403687/172550000000000000000000000 : ℝ)*base81 + (37088509/2500000000000000000000 : ℝ)*base89 + (37088509/2500000000000000000000 : ℝ)*base91 + (12911491/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1406_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157255887/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1843/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31443/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59067/100000 : ℝ) else (80321/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42299/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1406_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1406_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157255887/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31443/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59067/100000 : ℝ) else (80321/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42299/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1406_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1406_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1406_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4365/1024 : ℝ) ≤ p) (hpb : p ≤ (2183/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157255887/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31443/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59067/100000 : ℝ) else (80321/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42299/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1406_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

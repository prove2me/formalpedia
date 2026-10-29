-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1481_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:13:21.997696+00:00
-- url     : https://prove2.me/submissions/1a1cdc86-783d-453d-8bea-49b2f210f8da

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
theorem support_rectangle_w1481_s6_0 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-382961131/2000000000 : ℝ)*x 0 + (217491791/400000000 : ℝ)*x 1 + (162997233/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (382961131/2000000000 : ℝ)^4459 ≤ (11698240259907/100000000000000 : ℝ)^3435 := by
    have hnat : (382961131 : ℕ)^4459*100000000000000^3435 ≤ 11698240259907^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382961131 2000000000 11698240259907 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217491791/400000000 : ℝ)^4459 ≤ (22670885169331/50000000000000 : ℝ)^3435 := by
    have hnat : (217491791 : ℕ)^4459*50000000000000^3435 ≤ 22670885169331^3435*400000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217491791 400000000 22670885169331 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (162997233/312500000 : ℝ)^4459 ≤ (42959989376317/100000000000000 : ℝ)^3435 := by
    have hnat : (162997233 : ℕ)^4459*100000000000000^3435 ≤ 42959989376317^3435*312500000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162997233 312500000 42959989376317 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-382961131/2000000000 : ℝ), (217491791/400000000 : ℝ), (162997233/312500000 : ℝ)] ![(11698240259907/100000000000000 : ℝ), (22670885169331/50000000000000 : ℝ), (42959989376317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-382961131/2000000000 : ℝ)|^4459 ≤ (11698240259907/100000000000000 : ℝ)^3435
        have hw : |(-382961131/2000000000 : ℝ)|=(382961131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217491791/400000000 : ℝ)|^4459 ≤ (22670885169331/50000000000000 : ℝ)^3435
        have hw : |(217491791/400000000 : ℝ)|=(217491791/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(162997233/312500000 : ℝ)|^4459 ≤ (42959989376317/100000000000000 : ℝ)^3435
        have hw : |(162997233/312500000 : ℝ)|=(162997233/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s6_1 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669157023/1250000000 : ℝ)*x 0 + (-1584579/7812500 : ℝ)*x 1 + (40749309/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669157023/1250000000 : ℝ)^4459 ≤ (11108539825321/25000000000000 : ℝ)^3435 := by
    have hnat : (669157023 : ℕ)^4459*25000000000000^3435 ≤ 11108539825321^3435*1250000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669157023 1250000000 11108539825321 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1584579/7812500 : ℝ)^4459 ≤ (1260585028069/10000000000000 : ℝ)^3435 := by
    have hnat : (1584579 : ℕ)^4459*10000000000000^3435 ≤ 1260585028069^3435*7812500^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584579 7812500 1260585028069 10000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40749309/78125000 : ℝ)^4459 ≤ (10739997600679/25000000000000 : ℝ)^3435 := by
    have hnat : (40749309 : ℕ)^4459*25000000000000^3435 ≤ 10739997600679^3435*78125000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40749309 78125000 10739997600679 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669157023/1250000000 : ℝ), (-1584579/7812500 : ℝ), (40749309/78125000 : ℝ)] ![(11108539825321/25000000000000 : ℝ), (1260585028069/10000000000000 : ℝ), (10739997600679/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669157023/1250000000 : ℝ)|^4459 ≤ (11108539825321/25000000000000 : ℝ)^3435
        have hw : |(669157023/1250000000 : ℝ)|=(669157023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1584579/7812500 : ℝ)|^4459 ≤ (1260585028069/10000000000000 : ℝ)^3435
        have hw : |(-1584579/7812500 : ℝ)|=(1584579/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40749309/78125000 : ℝ)|^4459 ≤ (10739997600679/25000000000000 : ℝ)^3435
        have hw : |(40749309/78125000 : ℝ)|=(40749309/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s6_2 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070651417/2000000000 : ℝ)*x 0 + (162997219/312500000 : ℝ)*x 1 + (-2028260637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070651417/2000000000 : ℝ)^4459 ≤ (44434169009389/100000000000000 : ℝ)^3435 := by
    have hnat : (1070651417 : ℕ)^4459*100000000000000^3435 ≤ 44434169009389^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070651417 2000000000 44434169009389 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162997219/312500000 : ℝ)^4459 ≤ (42959984586459/100000000000000 : ℝ)^3435 := by
    have hnat : (162997219 : ℕ)^4459*100000000000000^3435 ≤ 42959984586459^3435*312500000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162997219 312500000 42959984586459 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2028260637/10000000000 : ℝ)^4459 ≤ (3151461595977/25000000000000 : ℝ)^3435 := by
    have hnat : (2028260637 : ℕ)^4459*25000000000000^3435 ≤ 3151461595977^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028260637 10000000000 3151461595977 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070651417/2000000000 : ℝ), (162997219/312500000 : ℝ), (-2028260637/10000000000 : ℝ)] ![(44434169009389/100000000000000 : ℝ), (42959984586459/100000000000000 : ℝ), (3151461595977/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070651417/2000000000 : ℝ)|^4459 ≤ (44434169009389/100000000000000 : ℝ)^3435
        have hw : |(1070651417/2000000000 : ℝ)|=(1070651417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162997219/312500000 : ℝ)|^4459 ≤ (42959984586459/100000000000000 : ℝ)^3435
        have hw : |(162997219/312500000 : ℝ)|=(162997219/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2028260637/10000000000 : ℝ)|^4459 ≤ (3151461595977/25000000000000 : ℝ)^3435
        have hw : |(-2028260637/10000000000 : ℝ)|=(2028260637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s6_3 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071107669/2500000000 : ℝ)*x 0 + (2022515689/5000000000 : ℝ)*x 1 + (17719103/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071107669/2500000000 : ℝ)^4459 ≤ (16639015402457/50000000000000 : ℝ)^3435 := by
    have hnat : (1071107669 : ℕ)^4459*50000000000000^3435 ≤ 16639015402457^3435*2500000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071107669 2500000000 16639015402457 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2022515689/5000000000 : ℝ)^4459 ≤ (30884621210803/100000000000000 : ℝ)^3435 := by
    have hnat : (2022515689 : ℕ)^4459*100000000000000^3435 ≤ 30884621210803^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022515689 5000000000 30884621210803 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17719103/39062500 : ℝ)^4459 ≤ (7167469593559/20000000000000 : ℝ)^3435 := by
    have hnat : (17719103 : ℕ)^4459*20000000000000^3435 ≤ 7167469593559^3435*39062500^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17719103 39062500 7167469593559 20000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071107669/2500000000 : ℝ), (2022515689/5000000000 : ℝ), (17719103/39062500 : ℝ)] ![(16639015402457/50000000000000 : ℝ), (30884621210803/100000000000000 : ℝ), (7167469593559/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071107669/2500000000 : ℝ)|^4459 ≤ (16639015402457/50000000000000 : ℝ)^3435
        have hw : |(1071107669/2500000000 : ℝ)|=(1071107669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2022515689/5000000000 : ℝ)|^4459 ≤ (30884621210803/100000000000000 : ℝ)^3435
        have hw : |(2022515689/5000000000 : ℝ)|=(2022515689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17719103/39062500 : ℝ)|^4459 ≤ (7167469593559/20000000000000 : ℝ)^3435
        have hw : |(17719103/39062500 : ℝ)|=(17719103/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s6_4 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1914835703/10000000000 : ℝ)*x 0 + (5217044257/10000000000 : ℝ)*x 1 + (5436153839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1914835703/10000000000 : ℝ)^4459 ≤ (11698478559419/100000000000000 : ℝ)^3435 := by
    have hnat : (1914835703 : ℕ)^4459*100000000000000^3435 ≤ 11698478559419^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914835703 10000000000 11698478559419 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217044257/10000000000 : ℝ)^4459 ≤ (42972101278859/100000000000000 : ℝ)^3435 := by
    have hnat : (5217044257 : ℕ)^4459*100000000000000^3435 ≤ 42972101278859^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217044257 10000000000 42972101278859 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436153839/10000000000 : ℝ)^4459 ≤ (22664710068843/50000000000000 : ℝ)^3435 := by
    have hnat : (5436153839 : ℕ)^4459*50000000000000^3435 ≤ 22664710068843^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436153839 10000000000 22664710068843 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1914835703/10000000000 : ℝ), (5217044257/10000000000 : ℝ), (5436153839/10000000000 : ℝ)] ![(11698478559419/100000000000000 : ℝ), (42972101278859/100000000000000 : ℝ), (22664710068843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1914835703/10000000000 : ℝ)|^4459 ≤ (11698478559419/100000000000000 : ℝ)^3435
        have hw : |(-1914835703/10000000000 : ℝ)|=(1914835703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217044257/10000000000 : ℝ)|^4459 ≤ (42972101278859/100000000000000 : ℝ)^3435
        have hw : |(5217044257/10000000000 : ℝ)|=(5217044257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436153839/10000000000 : ℝ)|^4459 ≤ (22664710068843/50000000000000 : ℝ)^3435
        have hw : |(5436153839/10000000000 : ℝ)|=(5436153839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s6_5 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059085883/2000000000 : ℝ)*x 0 + (-904009271/5000000000 : ℝ)*x 1 + (5436153839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059085883/2000000000 : ℝ)^4459 ≤ (10953023134737/25000000000000 : ℝ)^3435 := by
    have hnat : (1059085883 : ℕ)^4459*25000000000000^3435 ≤ 10953023134737^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059085883 2000000000 10953023134737 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904009271/5000000000 : ℝ)^4459 ≤ (10858487309523/100000000000000 : ℝ)^3435 := by
    have hnat : (904009271 : ℕ)^4459*100000000000000^3435 ≤ 10858487309523^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904009271 5000000000 10858487309523 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436153839/10000000000 : ℝ)^4459 ≤ (22664710068843/50000000000000 : ℝ)^3435 := by
    have hnat : (5436153839 : ℕ)^4459*50000000000000^3435 ≤ 22664710068843^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436153839 10000000000 22664710068843 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059085883/2000000000 : ℝ), (-904009271/5000000000 : ℝ), (5436153839/10000000000 : ℝ)] ![(10953023134737/25000000000000 : ℝ), (10858487309523/100000000000000 : ℝ), (22664710068843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059085883/2000000000 : ℝ)|^4459 ≤ (10953023134737/25000000000000 : ℝ)^3435
        have hw : |(1059085883/2000000000 : ℝ)|=(1059085883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-904009271/5000000000 : ℝ)|^4459 ≤ (10858487309523/100000000000000 : ℝ)^3435
        have hw : |(-904009271/5000000000 : ℝ)|=(904009271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436153839/10000000000 : ℝ)|^4459 ≤ (22664710068843/50000000000000 : ℝ)^3435
        have hw : |(5436153839/10000000000 : ℝ)|=(5436153839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s6_6 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059085883/2000000000 : ℝ)*x 0 + (5436153839/10000000000 : ℝ)*x 1 + (-904009271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059085883/2000000000 : ℝ)^4459 ≤ (10953023134737/25000000000000 : ℝ)^3435 := by
    have hnat : (1059085883 : ℕ)^4459*25000000000000^3435 ≤ 10953023134737^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059085883 2000000000 10953023134737 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436153839/10000000000 : ℝ)^4459 ≤ (22664710068843/50000000000000 : ℝ)^3435 := by
    have hnat : (5436153839 : ℕ)^4459*50000000000000^3435 ≤ 22664710068843^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436153839 10000000000 22664710068843 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (904009271/5000000000 : ℝ)^4459 ≤ (10858487309523/100000000000000 : ℝ)^3435 := by
    have hnat : (904009271 : ℕ)^4459*100000000000000^3435 ≤ 10858487309523^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904009271 5000000000 10858487309523 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059085883/2000000000 : ℝ), (5436153839/10000000000 : ℝ), (-904009271/5000000000 : ℝ)] ![(10953023134737/25000000000000 : ℝ), (22664710068843/50000000000000 : ℝ), (10858487309523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059085883/2000000000 : ℝ)|^4459 ≤ (10953023134737/25000000000000 : ℝ)^3435
        have hw : |(1059085883/2000000000 : ℝ)|=(1059085883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436153839/10000000000 : ℝ)|^4459 ≤ (22664710068843/50000000000000 : ℝ)^3435
        have hw : |(5436153839/10000000000 : ℝ)|=(5436153839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-904009271/5000000000 : ℝ)|^4459 ≤ (10858487309523/100000000000000 : ℝ)^3435
        have hw : |(-904009271/5000000000 : ℝ)|=(904009271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s6_7 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (856899547/2000000000 : ℝ)*x 0 + (906715631/2000000000 : ℝ)*x 1 + (4047562211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (856899547/2000000000 : ℝ)^4459 ≤ (8319676734939/25000000000000 : ℝ)^3435 := by
    have hnat : (856899547 : ℕ)^4459*25000000000000^3435 ≤ 8319676734939^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856899547 2000000000 8319676734939 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906715631/2000000000 : ℝ)^4459 ≤ (35811585616501/100000000000000 : ℝ)^3435 := by
    have hnat : (906715631 : ℕ)^4459*100000000000000^3435 ≤ 35811585616501^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906715631 2000000000 35811585616501 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4047562211/10000000000 : ℝ)^4459 ≤ (15454853711673/50000000000000 : ℝ)^3435 := by
    have hnat : (4047562211 : ℕ)^4459*50000000000000^3435 ≤ 15454853711673^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4047562211 10000000000 15454853711673 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(856899547/2000000000 : ℝ), (906715631/2000000000 : ℝ), (4047562211/10000000000 : ℝ)] ![(8319676734939/25000000000000 : ℝ), (35811585616501/100000000000000 : ℝ), (15454853711673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(856899547/2000000000 : ℝ)|^4459 ≤ (8319676734939/25000000000000 : ℝ)^3435
        have hw : |(856899547/2000000000 : ℝ)|=(856899547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(906715631/2000000000 : ℝ)|^4459 ≤ (35811585616501/100000000000000 : ℝ)^3435
        have hw : |(906715631/2000000000 : ℝ)|=(906715631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4047562211/10000000000 : ℝ)|^4459 ≤ (15454853711673/50000000000000 : ℝ)^3435
        have hw : |(4047562211/10000000000 : ℝ)|=(4047562211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1481_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10789/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1079/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3869/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15477/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10789/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15477/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10789/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15477/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10789/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15477/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10789/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15477/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10789/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15477/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10789/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10789/100000 : ℝ) ^ (4457/1024 : ℝ) ≤ (6180347131444931/100000000000000000000 : ℝ) := by
    have hpowers : (10789/100000 : ℝ)^4457 ≤ (6180347131444931/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10789 : ℕ)^4457*100000000000000000000^1024 ≤ 6180347131444931^1024*100000^4457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10789 100000 6180347131444931 100000000000000000000 4457 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10789/100000 : ℝ)) (X := (6180347131444931/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15477/100000 : ℝ) ^ (4457/1024 : ℝ) ≤ (116102107469533/390625000000000000 : ℝ) := by
    have hpowers : (15477/100000 : ℝ)^4457 ≤ (116102107469533/390625000000000000 : ℝ)^1024 := by
      have hnat : (15477 : ℕ)^4457*390625000000000000^1024 ≤ 116102107469533^1024*100000^4457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15477 100000 116102107469533 390625000000000000 4457 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15477/100000 : ℝ)) (X := (116102107469533/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006180347131444931/50000000000000000000 : ℝ) ≤ (10000283974611349/10000000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (50006180347131444931/50000000000000000000 : ℝ)^1024 ≤ (10000283974611349/10000000000000000 : ℝ)^4457 := by
      have hnat : (50006180347131444931 : ℕ)^1024*10000000000000000^4457 ≤ 10000283974611349^4457*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006180347131444931 50000000000000000000 10000283974611349 10000000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283974611349/10000000000000000 : ℝ)) (X := (50006180347131444931/50000000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035902486643645379/100000000000000000000 : ℝ) ≤ (5000412374512539/5000000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (100035902486643645379/100000000000000000000 : ℝ)^1024 ≤ (5000412374512539/5000000000000000 : ℝ)^4457 := by
      have hnat : (100035902486643645379 : ℕ)^1024*5000000000000000^4457 ≤ 5000412374512539^4457*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035902486643645379 100000000000000000000 5000412374512539 5000000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000412374512539/5000000000000000 : ℝ)) (X := (100035902486643645379/100000000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (195428602107469533/195312500000000000 : ℝ) ≤ (10001365523438807/10000000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (195428602107469533/195312500000000000 : ℝ)^1024 ≤ (10001365523438807/10000000000000000 : ℝ)^4457 := by
      have hnat : (195428602107469533 : ℕ)^1024*10000000000000000^4457 ≤ 10001365523438807^4457*195312500000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195428602107469533 195312500000000000 10001365523438807 10000000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001365523438807/10000000000000000 : ℝ)) (X := (195428602107469533/195312500000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6180347131444931/100000000000000000000 : ℝ) ≤ ((187478649770714239/187520000000000000 : ℝ)+2*(540774413729/468800000000000 : ℝ)*(10789/100000 : ℝ))^(4457/1024 : ℝ) := by
    rw [show (187478649770714239/187520000000000000 : ℝ)+2*(540774413729/468800000000000 : ℝ)*(10789/100000 : ℝ)=(10000283974611349/10000000000000000 : ℝ) by norm_num, show 1+2*(6180347131444931/100000000000000000000 : ℝ)=(50006180347131444931/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(116102107469533/390625000000000000 : ℝ)+(6180347131444931/100000000000000000000 : ℝ) ≤ ((187478649770714239/187520000000000000 : ℝ)+(540774413729/468800000000000 : ℝ)*((15477/100000 : ℝ)+(10789/100000 : ℝ)))^(4457/1024 : ℝ) := by
    rw [show (187478649770714239/187520000000000000 : ℝ)+(540774413729/468800000000000 : ℝ)*((15477/100000 : ℝ)+(10789/100000 : ℝ))=(5000412374512539/5000000000000000 : ℝ) by norm_num, show 1+(116102107469533/390625000000000000 : ℝ)+(6180347131444931/100000000000000000000 : ℝ)=(100035902486643645379/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(116102107469533/390625000000000000 : ℝ) ≤ ((187478649770714239/187520000000000000 : ℝ)+2*(540774413729/468800000000000 : ℝ)*(15477/100000 : ℝ))^(4457/1024 : ℝ) := by
    rw [show (187478649770714239/187520000000000000 : ℝ)+2*(540774413729/468800000000000 : ℝ)*(15477/100000 : ℝ)=(10001365523438807/10000000000000000 : ℝ) by norm_num, show 1+2*(116102107469533/390625000000000000 : ℝ)=(195428602107469533/195312500000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (187478649770714239/187520000000000000 : ℝ)*(X 1 0+X 2 0)+(540774413729/468800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (10789/100000 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (187478649770714239/187520000000000000 : ℝ)) (alpha := (540774413729/468800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (187478649770714239/187520000000000000 : ℝ)*(X 0 1+X 2 1)+(540774413729/468800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (10789/100000 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (187478649770714239/187520000000000000 : ℝ)) (alpha := (540774413729/468800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (187478649770714239/187520000000000000 : ℝ)*(X 0 2+X 1 2)+(540774413729/468800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (10789/100000 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (187478649770714239/187520000000000000 : ℝ)) (alpha := (540774413729/468800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-382961131/2000000000 : ℝ)*X 0 0+(217491791/400000000 : ℝ)*X 0 1+(162997233/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669157023/1250000000 : ℝ)*X 1 0+(-1584579/7812500 : ℝ)*X 1 1+(40749309/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070651417/2000000000 : ℝ)*X 2 0+(162997219/312500000 : ℝ)*X 2 1+(-2028260637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1071107669/2500000000 : ℝ)*X 0 0+(2022515689/5000000000 : ℝ)*X 0 1+(17719103/39062500 : ℝ)*X 0 2+(1071107669/2500000000 : ℝ)*X 1 0+(2022515689/5000000000 : ℝ)*X 1 1+(17719103/39062500 : ℝ)*X 1 2+(1071107669/2500000000 : ℝ)*X 2 0+(2022515689/5000000000 : ℝ)*X 2 1+(17719103/39062500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1914835703/10000000000 : ℝ)*X 0 0+(5217044257/10000000000 : ℝ)*X 0 1+(5436153839/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1059085883/2000000000 : ℝ)*X 1 0+(-904009271/5000000000 : ℝ)*X 1 1+(5436153839/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1059085883/2000000000 : ℝ)*X 2 0+(5436153839/10000000000 : ℝ)*X 2 1+(-904009271/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((856899547/2000000000 : ℝ)*X 0 0+(906715631/2000000000 : ℝ)*X 0 1+(4047562211/10000000000 : ℝ)*X 0 2+(856899547/2000000000 : ℝ)*X 1 0+(906715631/2000000000 : ℝ)*X 1 1+(4047562211/10000000000 : ℝ)*X 1 2+(856899547/2000000000 : ℝ)*X 2 0+(906715631/2000000000 : ℝ)*X 2 1+(4047562211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47836717150993194257481/5860000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35106779/2000000000000 : ℝ)*(base19) + (123542263/5000000000000 : ℝ)*(base23) + (30788453/100000000000000 : ℝ)*(upper4) + (122051739/25000000000000 : ℝ)*(upper5) + (819194727128563/25000000000000 : ℝ)*(major0) + (819194727128563/25000000000000 : ℝ)*(major1) + (819194727128563/25000000000000 : ℝ)*(major2) + (2258537076693447/50000000000000 : ℝ)*(sp0) + (282319531020221/6250000000000 : ℝ)*(sp1) + (180684518445647/4000000000000 : ℝ)*(sp2) + (2036430140317777/100000000000000 : ℝ)*(sp3) + (41278599541/100000000000000 : ℝ)*(sp4) + (295080987/25000000000000 : ℝ)*(sp5) + (11972615543/100000000000000 : ℝ)*(sp7) + (50911052823333/2500000000000 : ℝ)*(f.failure) + (903423086397287/20000000000000 : ℝ)*(f.sum) + (8620182117613/5860000000000000000000000000 : ℝ)*base66 + (40435706761224643/4688000000000000000000000000000 : ℝ)*base68 + (105046902743357/4688000000000000000000000000000 : ℝ)*base69 + (38138889807608643/4688000000000000000000000000000 : ℝ)*base72 + (3101124365673/5860000000000000000000000000 : ℝ)*base74 + (69627718046215357/4688000000000000000000000000000 : ℝ)*base75 + (14366500439336643/4688000000000000000000000000000 : ℝ)*base78 + (593718401831357/4688000000000000000000000000000 : ℝ)*base79 + (1115829502187/5860000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1374317/250000000000000000000 : ℝ)*base89 + (1374317/250000000000000000000 : ℝ)*base91 + (1374317/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23497563411669022273403469/2344000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1663492721/100000000000000 : ℝ)*(base19) + (72230299/4000000000000 : ℝ)*(base23) + (551971757/100000000000000 : ℝ)*(lower1) + (2590259/1250000000000 : ℝ)*(upper3) + (64287367/100000000000000 : ℝ)*(lower4) + (206698777/100000000000000 : ℝ)*(upper5) + (827679304289457/25000000000000 : ℝ)*(major0) + (827679304289457/25000000000000 : ℝ)*(major1) + (827679304289457/25000000000000 : ℝ)*(major2) + (1910494063/100000000000000 : ℝ)*(sp2) + (4563900115336333/100000000000000 : ℝ)*(sp4) + (1140974612960903/25000000000000 : ℝ)*(sp5) + (912779279816959/20000000000000 : ℝ)*(sp6) + (205753398482737/10000000000000 : ℝ)*(sp7) + (205753398482737/10000000000000 : ℝ)*(f.failure) + (4563900115336333/100000000000000 : ℝ)*(f.sum) + (5605963028293/5860000000000000000000000000 : ℝ)*base65 + (72158547817011423/4688000000000000000000000000000 : ℝ)*base67 + (27427958888876577/4688000000000000000000000000000 : ℝ)*base70 + (577113519565699423/4688000000000000000000000000000 : ℝ)*base71 + (13526697689593/5860000000000000000000000000 : ℝ)*base73 + (489605193540604577/4688000000000000000000000000000 : ℝ)*base76 + (19025613232700577/4688000000000000000000000000000 : ℝ)*base78 + (43377371237452577/4688000000000000000000000000000 : ℝ)*base80 + (181723188013/5860000000000000000000000000 : ℝ)*base81 + (8113113/1000000000000000000000 : ℝ)*base89 + (8113113/1000000000000000000000 : ℝ)*base91 + (8113113/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1481_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10789/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1079/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1481_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1481_box_0 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-8477281/50000000 : ℝ)*x 0 + (216247773/400000000 : ℝ)*x 1 + (5406194423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8477281/50000000 : ℝ)^4459 ≤ (624325357133/6250000000000 : ℝ)^3435 := by
    have hnat : (8477281 : ℕ)^4459*6250000000000^3435 ≤ 624325357133^3435*50000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8477281 50000000 624325357133 6250000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216247773/400000000 : ℝ)^4459 ≤ (22502698301031/50000000000000 : ℝ)^3435 := by
    have hnat : (216247773 : ℕ)^4459*50000000000000^3435 ≤ 22502698301031^3435*400000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216247773 400000000 22502698301031 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406194423/10000000000 : ℝ)^4459 ≤ (5625674707637/12500000000000 : ℝ)^3435 := by
    have hnat : (5406194423 : ℕ)^4459*12500000000000^3435 ≤ 5625674707637^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406194423 10000000000 5625674707637 12500000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8477281/50000000 : ℝ), (216247773/400000000 : ℝ), (5406194423/10000000000 : ℝ)] ![(624325357133/6250000000000 : ℝ), (22502698301031/50000000000000 : ℝ), (5625674707637/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8477281/50000000 : ℝ)|^4459 ≤ (624325357133/6250000000000 : ℝ)^3435
        have hw : |(-8477281/50000000 : ℝ)|=(8477281/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216247773/400000000 : ℝ)|^4459 ≤ (22502698301031/50000000000000 : ℝ)^3435
        have hw : |(216247773/400000000 : ℝ)|=(216247773/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406194423/10000000000 : ℝ)|^4459 ≤ (5625674707637/12500000000000 : ℝ)^3435
        have hw : |(5406194423/10000000000 : ℝ)|=(5406194423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_box_1 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270252497/10000000000 : ℝ)*x 0 + (-941885777/5000000000 : ℝ)*x 1 + (2703097203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270252497/10000000000 : ℝ)^4459 ≤ (43541884736833/100000000000000 : ℝ)^3435 := by
    have hnat : (5270252497 : ℕ)^4459*100000000000000^3435 ≤ 43541884736833^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270252497 10000000000 43541884736833 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (941885777/5000000000 : ℝ)^4459 ≤ (2290543552873/20000000000000 : ℝ)^3435 := by
    have hnat : (941885777 : ℕ)^4459*20000000000000^3435 ≤ 2290543552873^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941885777 5000000000 2290543552873 20000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703097203/5000000000 : ℝ)^4459 ≤ (22502698738693/50000000000000 : ℝ)^3435 := by
    have hnat : (2703097203 : ℕ)^4459*50000000000000^3435 ≤ 22502698738693^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703097203 5000000000 22502698738693 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270252497/10000000000 : ℝ), (-941885777/5000000000 : ℝ), (2703097203/5000000000 : ℝ)] ![(43541884736833/100000000000000 : ℝ), (2290543552873/20000000000000 : ℝ), (22502698738693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270252497/10000000000 : ℝ)|^4459 ≤ (43541884736833/100000000000000 : ℝ)^3435
        have hw : |(5270252497/10000000000 : ℝ)|=(5270252497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-941885777/5000000000 : ℝ)|^4459 ≤ (2290543552873/20000000000000 : ℝ)^3435
        have hw : |(-941885777/5000000000 : ℝ)|=(941885777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703097203/5000000000 : ℝ)|^4459 ≤ (22502698738693/50000000000000 : ℝ)^3435
        have hw : |(2703097203/5000000000 : ℝ)|=(2703097203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_box_2 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270252939/10000000000 : ℝ)*x 0 + (5406194177/10000000000 : ℝ)*x 1 + (-470942817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270252939/10000000000 : ℝ)^4459 ≤ (8708377895433/20000000000000 : ℝ)^3435 := by
    have hnat : (5270252939 : ℕ)^4459*20000000000000^3435 ≤ 8708377895433^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270252939 10000000000 8708377895433 20000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406194177/10000000000 : ℝ)^4459 ≤ (9001079000541/20000000000000 : ℝ)^3435 := by
    have hnat : (5406194177 : ℕ)^4459*20000000000000^3435 ≤ 9001079000541^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406194177 10000000000 9001079000541 20000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (470942817/2500000000 : ℝ)^4459 ≤ (11452715507233/100000000000000 : ℝ)^3435 := by
    have hnat : (470942817 : ℕ)^4459*100000000000000^3435 ≤ 11452715507233^3435*2500000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470942817 2500000000 11452715507233 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270252939/10000000000 : ℝ), (5406194177/10000000000 : ℝ), (-470942817/2500000000 : ℝ)] ![(8708377895433/20000000000000 : ℝ), (9001079000541/20000000000000 : ℝ), (11452715507233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270252939/10000000000 : ℝ)|^4459 ≤ (8708377895433/20000000000000 : ℝ)^3435
        have hw : |(5270252939/10000000000 : ℝ)|=(5270252939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406194177/10000000000 : ℝ)|^4459 ≤ (9001079000541/20000000000000 : ℝ)^3435
        have hw : |(5406194177/10000000000 : ℝ)|=(5406194177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-470942817/2500000000 : ℝ)|^4459 ≤ (11452715507233/100000000000000 : ℝ)^3435
        have hw : |(-470942817/2500000000 : ℝ)|=(470942817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_box_3 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4488987203/10000000000 : ℝ)*x 0 + (4189343369/10000000000 : ℝ)*x 1 + (261834001/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4488987203/10000000000 : ℝ)^4459 ≤ (4419377752483/12500000000000 : ℝ)^3435 := by
    have hnat : (4488987203 : ℕ)^4459*12500000000000^3435 ≤ 4419377752483^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488987203 10000000000 4419377752483 12500000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4189343369/10000000000 : ℝ)^4459 ≤ (8080621436911/25000000000000 : ℝ)^3435 := by
    have hnat : (4189343369 : ℕ)^4459*25000000000000^3435 ≤ 8080621436911^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4189343369 10000000000 8080621436911 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261834001/625000000 : ℝ)^4459 ≤ (16161246113813/50000000000000 : ℝ)^3435 := by
    have hnat : (261834001 : ℕ)^4459*50000000000000^3435 ≤ 16161246113813^3435*625000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261834001 625000000 16161246113813 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4488987203/10000000000 : ℝ), (4189343369/10000000000 : ℝ), (261834001/625000000 : ℝ)] ![(4419377752483/12500000000000 : ℝ), (8080621436911/25000000000000 : ℝ), (16161246113813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4488987203/10000000000 : ℝ)|^4459 ≤ (4419377752483/12500000000000 : ℝ)^3435
        have hw : |(4488987203/10000000000 : ℝ)|=(4488987203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4189343369/10000000000 : ℝ)|^4459 ≤ (8080621436911/25000000000000 : ℝ)^3435
        have hw : |(4189343369/10000000000 : ℝ)|=(4189343369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261834001/625000000 : ℝ)|^4459 ≤ (16161246113813/50000000000000 : ℝ)^3435
        have hw : |(261834001/625000000 : ℝ)|=(261834001/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_box_4 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139620009/10000000000 : ℝ)*x 0 + (5242476329/10000000000 : ℝ)*x 1 + (1310619229/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139620009/10000000000 : ℝ)^4459 ≤ (3377884911653/25000000000000 : ℝ)^3435 := by
    have hnat : (2139620009 : ℕ)^4459*25000000000000^3435 ≤ 3377884911653^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139620009 10000000000 3377884911653 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242476329/10000000000 : ℝ)^4459 ≤ (21622113512747/50000000000000 : ℝ)^3435 := by
    have hnat : (5242476329 : ℕ)^4459*50000000000000^3435 ≤ 21622113512747^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242476329 10000000000 21622113512747 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310619229/2500000000 : ℝ)^4459 ≤ (10811058327751/25000000000000 : ℝ)^3435 := by
    have hnat : (1310619229 : ℕ)^4459*25000000000000^3435 ≤ 10811058327751^3435*2500000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310619229 2500000000 10811058327751 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139620009/10000000000 : ℝ), (5242476329/10000000000 : ℝ), (1310619229/2500000000 : ℝ)] ![(3377884911653/25000000000000 : ℝ), (21622113512747/50000000000000 : ℝ), (10811058327751/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139620009/10000000000 : ℝ)|^4459 ≤ (3377884911653/25000000000000 : ℝ)^3435
        have hw : |(-2139620009/10000000000 : ℝ)|=(2139620009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242476329/10000000000 : ℝ)|^4459 ≤ (21622113512747/50000000000000 : ℝ)^3435
        have hw : |(5242476329/10000000000 : ℝ)|=(5242476329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310619229/2500000000 : ℝ)|^4459 ≤ (10811058327751/25000000000000 : ℝ)^3435
        have hw : |(1310619229/2500000000 : ℝ)|=(1310619229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_box_5 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692256461/5000000000 : ℝ)*x 0 + (-1950804383/10000000000 : ℝ)*x 1 + (5242476969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692256461/5000000000 : ℝ)^4459 ≤ (44771237458573/100000000000000 : ℝ)^3435 := by
    have hnat : (2692256461 : ℕ)^4459*100000000000000^3435 ≤ 44771237458573^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692256461 5000000000 44771237458573 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1950804383/10000000000 : ℝ)^4459 ≤ (2996132160163/25000000000000 : ℝ)^3435 := by
    have hnat : (1950804383 : ℕ)^4459*25000000000000^3435 ≤ 2996132160163^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950804383 10000000000 2996132160163 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242476969/10000000000 : ℝ)^4459 ≤ (1081105846963/2500000000000 : ℝ)^3435 := by
    have hnat : (5242476969 : ℕ)^4459*2500000000000^3435 ≤ 1081105846963^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242476969 10000000000 1081105846963 2500000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692256461/5000000000 : ℝ), (-1950804383/10000000000 : ℝ), (5242476969/10000000000 : ℝ)] ![(44771237458573/100000000000000 : ℝ), (2996132160163/25000000000000 : ℝ), (1081105846963/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692256461/5000000000 : ℝ)|^4459 ≤ (44771237458573/100000000000000 : ℝ)^3435
        have hw : |(2692256461/5000000000 : ℝ)|=(2692256461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1950804383/10000000000 : ℝ)|^4459 ≤ (2996132160163/25000000000000 : ℝ)^3435
        have hw : |(-1950804383/10000000000 : ℝ)|=(1950804383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242476969/10000000000 : ℝ)|^4459 ≤ (1081105846963/2500000000000 : ℝ)^3435
        have hw : |(5242476969/10000000000 : ℝ)|=(5242476969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_box_6 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1346128279/2500000000 : ℝ)*x 0 + (5242476641/10000000000 : ℝ)*x 1 + (-975402281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346128279/2500000000 : ℝ)^4459 ≤ (44771239552517/100000000000000 : ℝ)^3435 := by
    have hnat : (1346128279 : ℕ)^4459*100000000000000^3435 ≤ 44771239552517^3435*2500000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346128279 2500000000 44771239552517 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242476641/10000000000 : ℝ)^4459 ≤ (5405528795793/12500000000000 : ℝ)^3435 := by
    have hnat : (5242476641 : ℕ)^4459*12500000000000^3435 ≤ 5405528795793^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242476641 10000000000 5405528795793 12500000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (975402281/5000000000 : ℝ)^4459 ≤ (1498066258517/12500000000000 : ℝ)^3435 := by
    have hnat : (975402281 : ℕ)^4459*12500000000000^3435 ≤ 1498066258517^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975402281 5000000000 1498066258517 12500000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1346128279/2500000000 : ℝ), (5242476641/10000000000 : ℝ), (-975402281/5000000000 : ℝ)] ![(44771239552517/100000000000000 : ℝ), (5405528795793/12500000000000 : ℝ), (1498066258517/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1346128279/2500000000 : ℝ)|^4459 ≤ (44771239552517/100000000000000 : ℝ)^3435
        have hw : |(1346128279/2500000000 : ℝ)|=(1346128279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242476641/10000000000 : ℝ)|^4459 ≤ (5405528795793/12500000000000 : ℝ)^3435
        have hw : |(5242476641/10000000000 : ℝ)|=(5242476641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-975402281/5000000000 : ℝ)|^4459 ≤ (1498066258517/12500000000000 : ℝ)^3435
        have hw : |(-975402281/5000000000 : ℝ)|=(975402281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_box_7 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1019402371/2500000000 : ℝ)*x 0 + (1098723491/2500000000 : ℝ)*x 1 + (2197447039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1019402371/2500000000 : ℝ)^4459 ≤ (31207899850003/100000000000000 : ℝ)^3435 := by
    have hnat : (1019402371 : ℕ)^4459*100000000000000^3435 ≤ 31207899850003^3435*2500000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019402371 2500000000 31207899850003 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098723491/2500000000 : ℝ)^4459 ≤ (275168395917/800000000000 : ℝ)^3435 := by
    have hnat : (1098723491 : ℕ)^4459*800000000000^3435 ≤ 275168395917^3435*2500000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098723491 2500000000 275168395917 800000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2197447039/5000000000 : ℝ)^4459 ≤ (8599012661951/25000000000000 : ℝ)^3435 := by
    have hnat : (2197447039 : ℕ)^4459*25000000000000^3435 ≤ 8599012661951^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197447039 5000000000 8599012661951 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1019402371/2500000000 : ℝ), (1098723491/2500000000 : ℝ), (2197447039/5000000000 : ℝ)] ![(31207899850003/100000000000000 : ℝ), (275168395917/800000000000 : ℝ), (8599012661951/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1019402371/2500000000 : ℝ)|^4459 ≤ (31207899850003/100000000000000 : ℝ)^3435
        have hw : |(1019402371/2500000000 : ℝ)|=(1019402371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1098723491/2500000000 : ℝ)|^4459 ≤ (275168395917/800000000000 : ℝ)^3435
        have hw : |(1098723491/2500000000 : ℝ)|=(1098723491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2197447039/5000000000 : ℝ)|^4459 ≤ (8599012661951/25000000000000 : ℝ)^3435
        have hw : |(2197447039/5000000000 : ℝ)|=(2197447039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_box_8 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-63935483/312500000 : ℝ)*x 0 + (2564066163/5000000000 : ℝ)*x 1 + (2713368749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63935483/312500000 : ℝ)^4459 ≤ (3187157349643/25000000000000 : ℝ)^3435 := by
    have hnat : (63935483 : ℕ)^4459*25000000000000^3435 ≤ 3187157349643^3435*312500000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63935483 312500000 3187157349643 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564066163/5000000000 : ℝ)^4459 ≤ (42023849262937/100000000000000 : ℝ)^3435 := by
    have hnat : (2564066163 : ℕ)^4459*100000000000000^3435 ≤ 42023849262937^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564066163 5000000000 42023849262937 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713368749/5000000000 : ℝ)^4459 ≤ (45227521320099/100000000000000 : ℝ)^3435 := by
    have hnat : (2713368749 : ℕ)^4459*100000000000000^3435 ≤ 45227521320099^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713368749 5000000000 45227521320099 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-63935483/312500000 : ℝ), (2564066163/5000000000 : ℝ), (2713368749/5000000000 : ℝ)] ![(3187157349643/25000000000000 : ℝ), (42023849262937/100000000000000 : ℝ), (45227521320099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-63935483/312500000 : ℝ)|^4459 ≤ (3187157349643/25000000000000 : ℝ)^3435
        have hw : |(-63935483/312500000 : ℝ)|=(63935483/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564066163/5000000000 : ℝ)|^4459 ≤ (42023849262937/100000000000000 : ℝ)^3435
        have hw : |(2564066163/5000000000 : ℝ)|=(2564066163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713368749/5000000000 : ℝ)|^4459 ≤ (45227521320099/100000000000000 : ℝ)^3435
        have hw : |(2713368749/5000000000 : ℝ)|=(2713368749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_box_9 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164247119/312500000 : ℝ)*x 0 + (-187510581/1000000000 : ℝ)*x 1 + (42396387/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164247119/312500000 : ℝ)^4459 ≤ (43388104215641/100000000000000 : ℝ)^3435 := by
    have hnat : (164247119 : ℕ)^4459*100000000000000^3435 ≤ 43388104215641^3435*312500000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164247119 312500000 43388104215641 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (187510581/1000000000 : ℝ)^4459 ≤ (5692187015441/50000000000000 : ℝ)^3435 := by
    have hnat : (187510581 : ℕ)^4459*50000000000000^3435 ≤ 5692187015441^3435*1000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187510581 1000000000 5692187015441 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42396387/78125000 : ℝ)^4459 ≤ (45227521731209/100000000000000 : ℝ)^3435 := by
    have hnat : (42396387 : ℕ)^4459*100000000000000^3435 ≤ 45227521731209^3435*78125000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42396387 78125000 45227521731209 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164247119/312500000 : ℝ), (-187510581/1000000000 : ℝ), (42396387/78125000 : ℝ)] ![(43388104215641/100000000000000 : ℝ), (5692187015441/50000000000000 : ℝ), (45227521731209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164247119/312500000 : ℝ)|^4459 ≤ (43388104215641/100000000000000 : ℝ)^3435
        have hw : |(164247119/312500000 : ℝ)|=(164247119/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-187510581/1000000000 : ℝ)|^4459 ≤ (5692187015441/50000000000000 : ℝ)^3435
        have hw : |(-187510581/1000000000 : ℝ)|=(187510581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42396387/78125000 : ℝ)|^4459 ≤ (45227521731209/100000000000000 : ℝ)^3435
        have hw : |(42396387/78125000 : ℝ)|=(42396387/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_box_10 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627953929/5000000000 : ℝ)*x 0 + (2713368759/5000000000 : ℝ)*x 1 + (-234388221/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627953929/5000000000 : ℝ)^4459 ≤ (21694052375721/50000000000000 : ℝ)^3435 := by
    have hnat : (2627953929 : ℕ)^4459*50000000000000^3435 ≤ 21694052375721^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627953929 5000000000 21694052375721 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713368759/5000000000 : ℝ)^4459 ≤ (45227521536473/100000000000000 : ℝ)^3435 := by
    have hnat : (2713368759 : ℕ)^4459*100000000000000^3435 ≤ 45227521536473^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713368759 5000000000 45227521536473 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (234388221/1250000000 : ℝ)^4459 ≤ (1138437369987/10000000000000 : ℝ)^3435 := by
    have hnat : (234388221 : ℕ)^4459*10000000000000^3435 ≤ 1138437369987^3435*1250000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234388221 1250000000 1138437369987 10000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627953929/5000000000 : ℝ), (2713368759/5000000000 : ℝ), (-234388221/1250000000 : ℝ)] ![(21694052375721/50000000000000 : ℝ), (45227521536473/100000000000000 : ℝ), (1138437369987/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627953929/5000000000 : ℝ)|^4459 ≤ (21694052375721/50000000000000 : ℝ)^3435
        have hw : |(2627953929/5000000000 : ℝ)|=(2627953929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713368759/5000000000 : ℝ)|^4459 ≤ (45227521536473/100000000000000 : ℝ)^3435
        have hw : |(2713368759/5000000000 : ℝ)|=(2713368759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-234388221/1250000000 : ℝ)|^4459 ≤ (1138437369987/10000000000000 : ℝ)^3435
        have hw : |(-234388221/1250000000 : ℝ)|=(234388221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_box_11 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (907890269/2000000000 : ℝ)*x 0 + (4163519809/10000000000 : ℝ)*x 1 + (166540791/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (907890269/2000000000 : ℝ)^4459 ≤ (8967955228261/25000000000000 : ℝ)^3435 := by
    have hnat : (907890269 : ℕ)^4459*25000000000000^3435 ≤ 8967955228261^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907890269 2000000000 8967955228261 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4163519809/10000000000 : ℝ)^4459 ≤ (32064089706563/100000000000000 : ℝ)^3435 := by
    have hnat : (4163519809 : ℕ)^4459*100000000000000^3435 ≤ 32064089706563^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163519809 10000000000 32064089706563 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166540791/400000000 : ℝ)^4459 ≤ (16032044683333/50000000000000 : ℝ)^3435 := by
    have hnat : (166540791 : ℕ)^4459*50000000000000^3435 ≤ 16032044683333^3435*400000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166540791 400000000 16032044683333 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(907890269/2000000000 : ℝ), (4163519809/10000000000 : ℝ), (166540791/400000000 : ℝ)] ![(8967955228261/25000000000000 : ℝ), (32064089706563/100000000000000 : ℝ), (16032044683333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(907890269/2000000000 : ℝ)|^4459 ≤ (8967955228261/25000000000000 : ℝ)^3435
        have hw : |(907890269/2000000000 : ℝ)|=(907890269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4163519809/10000000000 : ℝ)|^4459 ≤ (32064089706563/100000000000000 : ℝ)^3435
        have hw : |(4163519809/10000000000 : ℝ)|=(4163519809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(166540791/400000000 : ℝ)|^4459 ≤ (16032044683333/50000000000000 : ℝ)^3435
        have hw : |(166540791/400000000 : ℝ)|=(166540791/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_box_12 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-894632961/5000000000 : ℝ)*x 0 + (1379187513/2500000000 : ℝ)*x 1 + (2613741339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (894632961/5000000000 : ℝ)^4459 ≤ (1339064581447/12500000000000 : ℝ)^3435 := by
    have hnat : (894632961 : ℕ)^4459*12500000000000^3435 ≤ 1339064581447^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894632961 5000000000 1339064581447 12500000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1379187513/2500000000 : ℝ)^4459 ≤ (46203737625627/100000000000000 : ℝ)^3435 := by
    have hnat : (1379187513 : ℕ)^4459*100000000000000^3435 ≤ 46203737625627^3435*2500000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379187513 2500000000 46203737625627 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613741339/5000000000 : ℝ)^4459 ≤ (10770936426511/25000000000000 : ℝ)^3435 := by
    have hnat : (2613741339 : ℕ)^4459*25000000000000^3435 ≤ 10770936426511^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613741339 5000000000 10770936426511 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-894632961/5000000000 : ℝ), (1379187513/2500000000 : ℝ), (2613741339/5000000000 : ℝ)] ![(1339064581447/12500000000000 : ℝ), (46203737625627/100000000000000 : ℝ), (10770936426511/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-894632961/5000000000 : ℝ)|^4459 ≤ (1339064581447/12500000000000 : ℝ)^3435
        have hw : |(-894632961/5000000000 : ℝ)|=(894632961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1379187513/2500000000 : ℝ)|^4459 ≤ (46203737625627/100000000000000 : ℝ)^3435
        have hw : |(1379187513/2500000000 : ℝ)|=(1379187513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613741339/5000000000 : ℝ)|^4459 ≤ (10770936426511/25000000000000 : ℝ)^3435
        have hw : |(2613741339/5000000000 : ℝ)|=(2613741339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_box_13 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394976911/10000000000 : ℝ)*x 0 + (-1956759723/10000000000 : ℝ)*x 1 + (5227482499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394976911/10000000000 : ℝ)^4459 ≤ (22442106756597/50000000000000 : ℝ)^3435 := by
    have hnat : (5394976911 : ℕ)^4459*50000000000000^3435 ≤ 22442106756597^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394976911 10000000000 22442106756597 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1956759723/10000000000 : ℝ)^4459 ≤ (752002667523/6250000000000 : ℝ)^3435 := by
    have hnat : (1956759723 : ℕ)^4459*6250000000000^3435 ≤ 752002667523^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956759723 10000000000 752002667523 6250000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227482499/10000000000 : ℝ)^4459 ≤ (21541871895487/50000000000000 : ℝ)^3435 := by
    have hnat : (5227482499 : ℕ)^4459*50000000000000^3435 ≤ 21541871895487^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227482499 10000000000 21541871895487 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394976911/10000000000 : ℝ), (-1956759723/10000000000 : ℝ), (5227482499/10000000000 : ℝ)] ![(22442106756597/50000000000000 : ℝ), (752002667523/6250000000000 : ℝ), (21541871895487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394976911/10000000000 : ℝ)|^4459 ≤ (22442106756597/50000000000000 : ℝ)^3435
        have hw : |(5394976911/10000000000 : ℝ)|=(5394976911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1956759723/10000000000 : ℝ)|^4459 ≤ (752002667523/6250000000000 : ℝ)^3435
        have hw : |(-1956759723/10000000000 : ℝ)|=(1956759723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227482499/10000000000 : ℝ)|^4459 ≤ (21541871895487/50000000000000 : ℝ)^3435
        have hw : |(5227482499/10000000000 : ℝ)|=(5227482499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_box_14 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394976441/10000000000 : ℝ)*x 0 + (2613741347/5000000000 : ℝ)*x 1 + (-1956760097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394976441/10000000000 : ℝ)^4459 ≤ (44884208437299/100000000000000 : ℝ)^3435 := by
    have hnat : (5394976441 : ℕ)^4459*100000000000000^3435 ≤ 44884208437299^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394976441 10000000000 44884208437299 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613741347/5000000000 : ℝ)^4459 ≤ (43083745877223/100000000000000 : ℝ)^3435 := by
    have hnat : (2613741347 : ℕ)^4459*100000000000000^3435 ≤ 43083745877223^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613741347 5000000000 43083745877223 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1956760097/10000000000 : ℝ)^4459 ≤ (6016022832821/50000000000000 : ℝ)^3435 := by
    have hnat : (1956760097 : ℕ)^4459*50000000000000^3435 ≤ 6016022832821^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956760097 10000000000 6016022832821 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394976441/10000000000 : ℝ), (2613741347/5000000000 : ℝ), (-1956760097/10000000000 : ℝ)] ![(44884208437299/100000000000000 : ℝ), (43083745877223/100000000000000 : ℝ), (6016022832821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394976441/10000000000 : ℝ)|^4459 ≤ (44884208437299/100000000000000 : ℝ)^3435
        have hw : |(5394976441/10000000000 : ℝ)|=(5394976441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613741347/5000000000 : ℝ)|^4459 ≤ (43083745877223/100000000000000 : ℝ)^3435
        have hw : |(2613741347/5000000000 : ℝ)|=(2613741347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1956760097/10000000000 : ℝ)|^4459 ≤ (6016022832821/50000000000000 : ℝ)^3435
        have hw : |(-1956760097/10000000000 : ℝ)|=(1956760097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_box_15 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4039072771/10000000000 : ℝ)*x 0 + (1103424323/2500000000 : ℝ)*x 1 + (4413699009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4039072771/10000000000 : ℝ)^4459 ≤ (30825576573671/100000000000000 : ℝ)^3435 := by
    have hnat : (4039072771 : ℕ)^4459*100000000000000^3435 ≤ 30825576573671^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4039072771 10000000000 30825576573671 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103424323/2500000000 : ℝ)^4459 ≤ (4323400371253/12500000000000 : ℝ)^3435 := by
    have hnat : (1103424323 : ℕ)^4459*12500000000000^3435 ≤ 4323400371253^3435*2500000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103424323 2500000000 4323400371253 12500000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4413699009/10000000000 : ℝ)^4459 ≤ (8646805109011/25000000000000 : ℝ)^3435 := by
    have hnat : (4413699009 : ℕ)^4459*25000000000000^3435 ≤ 8646805109011^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4413699009 10000000000 8646805109011 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4039072771/10000000000 : ℝ), (1103424323/2500000000 : ℝ), (4413699009/10000000000 : ℝ)] ![(30825576573671/100000000000000 : ℝ), (4323400371253/12500000000000 : ℝ), (8646805109011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4039072771/10000000000 : ℝ)|^4459 ≤ (30825576573671/100000000000000 : ℝ)^3435
        have hw : |(4039072771/10000000000 : ℝ)|=(4039072771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1103424323/2500000000 : ℝ)|^4459 ≤ (4323400371253/12500000000000 : ℝ)^3435
        have hw : |(1103424323/2500000000 : ℝ)|=(1103424323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4413699009/10000000000 : ℝ)|^4459 ≤ (8646805109011/25000000000000 : ℝ)^3435
        have hw : |(4413699009/10000000000 : ℝ)|=(4413699009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1481_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1079/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63703/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29241/50000 : ℝ) ∧ (79979/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (429/500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3869/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1079/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3869/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1079/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3869/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1079/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3869/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1079/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3869/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1079/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3869/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1079/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1079/10000 : ℝ) ^ (4457/1024 : ℝ) ≤ (3091420408898583/50000000000000000000 : ℝ) := by
    have hpowers : (1079/10000 : ℝ)^4457 ≤ (3091420408898583/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1079 : ℕ)^4457*50000000000000000000^1024 ≤ 3091420408898583^1024*10000^4457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1079 10000 3091420408898583 50000000000000000000 4457 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1079/10000 : ℝ)) (X := (3091420408898583/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3869/25000 : ℝ) ^ (4457/1024 : ℝ) ≤ (29713781770867293/100000000000000000000 : ℝ) := by
    have hpowers : (3869/25000 : ℝ)^4457 ≤ (29713781770867293/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3869 : ℕ)^4457*100000000000000000000^1024 ≤ 29713781770867293^1024*25000^4457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3869 25000 29713781770867293 100000000000000000000 4457 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3869/25000 : ℝ)) (X := (29713781770867293/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003091420408898583/25000000000000000000 : ℝ) ≤ (5000142044592901/5000000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (25003091420408898583/25000000000000000000 : ℝ)^1024 ≤ (5000142044592901/5000000000000000 : ℝ)^4457 := by
      have hnat : (25003091420408898583 : ℕ)^1024*5000000000000000^4457 ≤ 5000142044592901^4457*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003091420408898583 25000000000000000000 5000142044592901 5000000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000142044592901/5000000000000000 : ℝ)) (X := (25003091420408898583/25000000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035896622588664459/100000000000000000000 : ℝ) ≤ (5000412307167549/5000000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (100035896622588664459/100000000000000000000 : ℝ)^1024 ≤ (5000412307167549/5000000000000000 : ℝ)^4457 := by
      have hnat : (100035896622588664459 : ℕ)^1024*5000000000000000^4457 ≤ 5000412307167549^4457*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035896622588664459 100000000000000000000 5000412307167549 5000000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000412307167549/5000000000000000 : ℝ)) (X := (100035896622588664459/100000000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029713781770867293/50000000000000000000 : ℝ) ≤ (5000682569742197/5000000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (50029713781770867293/50000000000000000000 : ℝ)^1024 ≤ (5000682569742197/5000000000000000 : ℝ)^4457 := by
      have hnat : (50029713781770867293 : ℕ)^1024*5000000000000000^4457 ≤ 5000682569742197^4457*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029713781770867293 50000000000000000000 5000682569742197 5000000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000682569742197/5000000000000000 : ℝ)) (X := (50029713781770867293/50000000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3091420408898583/50000000000000000000 : ℝ) ≤ ((1064765152481883193/1065000000000000000 : ℝ)+2*(3071165621/2662500000000 : ℝ)*(1079/10000 : ℝ))^(4457/1024 : ℝ) := by
    rw [show (1064765152481883193/1065000000000000000 : ℝ)+2*(3071165621/2662500000000 : ℝ)*(1079/10000 : ℝ)=(5000142044592901/5000000000000000 : ℝ) by norm_num, show 1+2*(3091420408898583/50000000000000000000 : ℝ)=(25003091420408898583/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29713781770867293/100000000000000000000 : ℝ)+(3091420408898583/50000000000000000000 : ℝ) ≤ ((1064765152481883193/1065000000000000000 : ℝ)+(3071165621/2662500000000 : ℝ)*((3869/25000 : ℝ)+(1079/10000 : ℝ)))^(4457/1024 : ℝ) := by
    rw [show (1064765152481883193/1065000000000000000 : ℝ)+(3071165621/2662500000000 : ℝ)*((3869/25000 : ℝ)+(1079/10000 : ℝ))=(5000412307167549/5000000000000000 : ℝ) by norm_num, show 1+(29713781770867293/100000000000000000000 : ℝ)+(3091420408898583/50000000000000000000 : ℝ)=(100035896622588664459/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29713781770867293/100000000000000000000 : ℝ) ≤ ((1064765152481883193/1065000000000000000 : ℝ)+2*(3071165621/2662500000000 : ℝ)*(3869/25000 : ℝ))^(4457/1024 : ℝ) := by
    rw [show (1064765152481883193/1065000000000000000 : ℝ)+2*(3071165621/2662500000000 : ℝ)*(3869/25000 : ℝ)=(5000682569742197/5000000000000000 : ℝ) by norm_num, show 1+2*(29713781770867293/100000000000000000000 : ℝ)=(50029713781770867293/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1064765152481883193/1065000000000000000 : ℝ)*(X 1 0+X 2 0)+(3071165621/2662500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (1079/10000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (1064765152481883193/1065000000000000000 : ℝ)) (alpha := (3071165621/2662500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1064765152481883193/1065000000000000000 : ℝ)*(X 0 1+X 2 1)+(3071165621/2662500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (1079/10000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (1064765152481883193/1065000000000000000 : ℝ)) (alpha := (3071165621/2662500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1064765152481883193/1065000000000000000 : ℝ)*(X 0 2+X 1 2)+(3071165621/2662500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (1079/10000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (1064765152481883193/1065000000000000000 : ℝ)) (alpha := (3071165621/2662500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-8477281/50000000 : ℝ)*X 0 0+(216247773/400000000 : ℝ)*X 0 1+(5406194423/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270252497/10000000000 : ℝ)*X 1 0+(-941885777/5000000000 : ℝ)*X 1 1+(2703097203/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270252939/10000000000 : ℝ)*X 2 0+(5406194177/10000000000 : ℝ)*X 2 1+(-470942817/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4488987203/10000000000 : ℝ)*X 0 0+(4189343369/10000000000 : ℝ)*X 0 1+(261834001/625000000 : ℝ)*X 0 2+(4488987203/10000000000 : ℝ)*X 1 0+(4189343369/10000000000 : ℝ)*X 1 1+(261834001/625000000 : ℝ)*X 1 2+(4488987203/10000000000 : ℝ)*X 2 0+(4189343369/10000000000 : ℝ)*X 2 1+(261834001/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2139620009/10000000000 : ℝ)*X 0 0+(5242476329/10000000000 : ℝ)*X 0 1+(1310619229/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2692256461/5000000000 : ℝ)*X 1 0+(-1950804383/10000000000 : ℝ)*X 1 1+(5242476969/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1346128279/2500000000 : ℝ)*X 2 0+(5242476641/10000000000 : ℝ)*X 2 1+(-975402281/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1019402371/2500000000 : ℝ)*X 0 0+(1098723491/2500000000 : ℝ)*X 0 1+(2197447039/5000000000 : ℝ)*X 0 2+(1019402371/2500000000 : ℝ)*X 1 0+(1098723491/2500000000 : ℝ)*X 1 1+(2197447039/5000000000 : ℝ)*X 1 2+(1019402371/2500000000 : ℝ)*X 2 0+(1098723491/2500000000 : ℝ)*X 2 1+(2197447039/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-63935483/312500000 : ℝ)*X 0 0+(2564066163/5000000000 : ℝ)*X 0 1+(2713368749/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((164247119/312500000 : ℝ)*X 1 0+(-187510581/1000000000 : ℝ)*X 1 1+(42396387/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2627953929/5000000000 : ℝ)*X 2 0+(2713368759/5000000000 : ℝ)*X 2 1+(-234388221/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((907890269/2000000000 : ℝ)*X 0 0+(4163519809/10000000000 : ℝ)*X 0 1+(166540791/400000000 : ℝ)*X 0 2+(907890269/2000000000 : ℝ)*X 1 0+(4163519809/10000000000 : ℝ)*X 1 1+(166540791/400000000 : ℝ)*X 1 2+(907890269/2000000000 : ℝ)*X 2 0+(4163519809/10000000000 : ℝ)*X 2 1+(166540791/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-894632961/5000000000 : ℝ)*X 0 0+(1379187513/2500000000 : ℝ)*X 0 1+(2613741339/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5394976911/10000000000 : ℝ)*X 1 0+(-1956759723/10000000000 : ℝ)*X 1 1+(5227482499/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5394976441/10000000000 : ℝ)*X 2 0+(2613741347/5000000000 : ℝ)*X 2 1+(-1956760097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4039072771/10000000000 : ℝ)*X 0 0+(1103424323/2500000000 : ℝ)*X 0 1+(4413699009/10000000000 : ℝ)*X 0 2+(4039072771/10000000000 : ℝ)*X 1 0+(1103424323/2500000000 : ℝ)*X 1 1+(4413699009/10000000000 : ℝ)*X 1 2+(4039072771/10000000000 : ℝ)*X 2 0+(1103424323/2500000000 : ℝ)*X 2 1+(4413699009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63703/100000 : ℝ) ≤ (-11306862660813376900831553177511/17750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2103803/50000000000000 : ℝ)*(lower3) + (5555427/25000000000000 : ℝ)*(lower4) + (167499/4000000000000 : ℝ)*(upper5) + (2177167445784127/100000000000000 : ℝ)*(major0) + (2177167445784127/100000000000000 : ℝ)*(major1) + (2177167445784127/100000000000000 : ℝ)*(major2) + (21013011/400000000000 : ℝ)*(sp2) + (3022502929607423/100000000000000 : ℝ)*(sp4) + (1511244720065151/50000000000000 : ℝ)*(sp5) + (302250409766891/10000000000000 : ℝ)*(sp6) + (676525525822587/50000000000000 : ℝ)*(sp7) + (3210657119/50000000000000 : ℝ)*(sp12) + (9955395679/50000000000000 : ℝ)*(sp13) + (251059511/3125000000000 : ℝ)*(sp15) + (676529542774763/50000000000000 : ℝ)*(f.failure) + (151125467546083/5000000000000 : ℝ)*(f.sum) + (2367603969211/1065000000000000000000000000 : ℝ)*base65 + (111476057185074163/35500000000000000000000000000000 : ℝ)*base68 + (20803740745425837/35500000000000000000000000000000 : ℝ)*base69 + (271315042306425837/35500000000000000000000000000000 : ℝ)*base71 + (204812989159/266250000000000000000000000 : ℝ)*base73 + (1204180658574163/35500000000000000000000000000000 : ℝ)*base76 + (154638675212425837/35500000000000000000000000000000 : ℝ)*base77 + (35808560961425837/35500000000000000000000000000000 : ℝ)*base79 + (296854820267/133125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (36004387/5000000000000000000000 : ℝ)*base89 + (36004387/5000000000000000000000 : ℝ)*base91 + (36004387/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29241/50000 : ℝ) ≤ (1297631807568502606223758918593/2218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2925757/25000000000000 : ℝ)*(upper0) + (89197849/100000000000000 : ℝ)*(lower1) + (33547651/100000000000000 : ℝ)*(lower3) + (28847513/25000000000000 : ℝ)*(upper4) + (889273/1562500000000 : ℝ)*(upper5) + (281412268049051/12500000000000 : ℝ)*(major0) + (281412268049051/12500000000000 : ℝ)*(major1) + (281412268049051/12500000000000 : ℝ)*(major2) + (770992938741369/25000000000000 : ℝ)*(sp0) + (3083942113450417/100000000000000 : ℝ)*(sp1) + (770981882454761/25000000000000 : ℝ)*(sp2) + (279825919173051/20000000000000 : ℝ)*(sp3) + (29641515059/100000000000000 : ℝ)*(sp9) + (691017913/1562500000000 : ℝ)*(sp10) + (279825919173051/20000000000000 : ℝ)*(f.failure) + (770992938741369/25000000000000 : ℝ)*(f.sum) + (5689966741219/1065000000000000000000000000 : ℝ)*base65 + (1847024441320781/4437500000000000000000000000000 : ℝ)*base67 + (4099388117616719/4437500000000000000000000000000 : ℝ)*base70 + (12221119199991719/4437500000000000000000000000000 : ℝ)*base72 + (4787770392289/1065000000000000000000000000 : ℝ)*base73 + (7351218630008281/4437500000000000000000000000000 : ℝ)*base75 + (25094355738804219/4437500000000000000000000000000 : ℝ)*base78 + (16757721767679219/4437500000000000000000000000000 : ℝ)*base80 + (296787404927/33281250000000000000000000 : ℝ)*base81 + (3263501/2000000000000000000000 : ℝ)*base90 + (3263501/2000000000000000000000 : ℝ)*base92 + (3263501/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79979/100000 : ℝ) ≤ (354918351622743209453828508719/443750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15020473/100000000000000 : ℝ)*(lower3) + (9376703/50000000000000 : ℝ)*(upper4) + (1835381/25000000000000 : ℝ)*(lower5) + (61217054240089/2500000000000 : ℝ)*(major0) + (61217054240089/2500000000000 : ℝ)*(major1) + (61217054240089/2500000000000 : ℝ)*(major2) + (243562311/100000000000000 : ℝ)*(sp0) + (13749931153/100000000000000 : ℝ)*(sp1) + (15149953623/100000000000000 : ℝ)*(sp2) + (7640561891/100000000000000 : ℝ)*(sp3) + (837226092850283/25000000000000 : ℝ)*(sp8) + (3348890865032289/100000000000000 : ℝ)*(sp9) + (167444473250491/5000000000000 : ℝ)*(sp10) + (30435831004531/2000000000000 : ℝ)*(sp11) + (1521799190788441/100000000000000 : ℝ)*(f.failure) + (1674452307481721/50000000000000 : ℝ)*(f.sum) + (315218299987/213000000000000000000000000 : ℝ)*base66 + (2057177715058059/887500000000000000000000000000 : ℝ)*base67 + (7018123476445559/887500000000000000000000000000 : ℝ)*base69 + (8424737863308059/887500000000000000000000000000 : ℝ)*base71 + (283894100717/42600000000000000000000000 : ℝ)*base74 + (10925971700908059/887500000000000000000000000000 : ℝ)*base75 + (6906170334758059/887500000000000000000000000000 : ℝ)*base77 + (3405466007508059/887500000000000000000000000000 : ℝ)*base79 + (1606886173/4260000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (24620609/10000000000000000000000 : ℝ)*base89 + (24620609/10000000000000000000000 : ℝ)*base91 + (24620609/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-429/500 : ℝ) ≤ (-3045821589401468962901987325549/3550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (380739/4000000000000 : ℝ)*(lower0) + (8961589/12500000000000 : ℝ)*(lower1) + (6757023/50000000000000 : ℝ)*(lower2) + (133573269/100000000000000 : ℝ)*(lower3) + (56164241/20000000000000 : ℝ)*(lower4) + (497404050433431/20000000000000 : ℝ)*(major0) + (497404050433431/20000000000000 : ℝ)*(major1) + (497404050433431/20000000000000 : ℝ)*(major2) + (5009281681/5000000000000 : ℝ)*(sp6) + (6204378419/10000000000000 : ℝ)*(sp7) + (27656114783427/800000000000 : ℝ)*(sp12) + (27656114783427/800000000000 : ℝ)*(sp13) + (864228540573689/25000000000000 : ℝ)*(sp14) + (1545563376371987/100000000000000 : ℝ)*(sp15) + (1545625420156177/100000000000000 : ℝ)*(f.failure) + (27656114783427/800000000000 : ℝ)*(f.sum) + (276250511459/71000000000000000000000000 : ℝ)*base65 + (66140537240475061/7100000000000000000000000000000 : ℝ)*base67 + (36634626408575061/7100000000000000000000000000000 : ℝ)*base69 + (62468703384675061/7100000000000000000000000000000 : ℝ)*base71 + (112981676767/71000000000000000000000000 : ℝ)*base73 + (24416798196075061/7100000000000000000000000000000 : ℝ)*base75 + (12969962178575061/7100000000000000000000000000000 : ℝ)*base77 + (51388884394075061/7100000000000000000000000000000 : ℝ)*base79 + (114592899073/14200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (60191673/10000000000000000000000 : ℝ)*base89 + (60191673/10000000000000000000000 : ℝ)*base91 + (60191673/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1481_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1079/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63703/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29241/50000 : ℝ) else (79979/100000 : ℝ) ≤ X j i ∧ X j i ≤ (429/500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1481_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1481_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10789/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63703/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29241/50000 : ℝ) else (79979/100000 : ℝ) ≤ X j i ∧ X j i ≤ (429/500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1481_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1481_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10789/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63703/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29241/50000 : ℝ) else (79979/100000 : ℝ) ≤ X j i ∧ X j i ≤ (429/500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1481_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

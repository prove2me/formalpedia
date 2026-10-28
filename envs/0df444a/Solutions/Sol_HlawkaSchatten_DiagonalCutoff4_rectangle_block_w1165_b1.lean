-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1165_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:41:52.064602+00:00
-- url     : https://prove2.me/submissions/9d2b6f01-8d32-4ec4-90ca-5ca73e7e1d23

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
theorem support_rectangle_w1165_s3_0 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2152377907/10000000000 : ℝ)*x 0 + (5426851289/10000000000 : ℝ)*x 1 + (654274873/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152377907/10000000000 : ℝ)^4179 ≤ (13073978646583/100000000000000 : ℝ)^3155 := by
    have hnat : (2152377907 : ℕ)^4179*100000000000000^3155 ≤ 13073978646583^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152377907 10000000000 13073978646583 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426851289/10000000000 : ℝ)^4179 ≤ (44503245437519/100000000000000 : ℝ)^3155 := by
    have hnat : (5426851289 : ℕ)^4179*100000000000000^3155 ≤ 44503245437519^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426851289 10000000000 44503245437519 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654274873/1250000000 : ℝ)^4179 ≤ (42422775897607/100000000000000 : ℝ)^3155 := by
    have hnat : (654274873 : ℕ)^4179*100000000000000^3155 ≤ 42422775897607^3155*1250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654274873 1250000000 42422775897607 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2152377907/10000000000 : ℝ), (5426851289/10000000000 : ℝ), (654274873/1250000000 : ℝ)] ![(13073978646583/100000000000000 : ℝ), (44503245437519/100000000000000 : ℝ), (42422775897607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2152377907/10000000000 : ℝ)|^4179 ≤ (13073978646583/100000000000000 : ℝ)^3155
        have hw : |(-2152377907/10000000000 : ℝ)|=(2152377907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426851289/10000000000 : ℝ)|^4179 ≤ (44503245437519/100000000000000 : ℝ)^3155
        have hw : |(5426851289/10000000000 : ℝ)|=(5426851289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654274873/1250000000 : ℝ)|^4179 ≤ (42422775897607/100000000000000 : ℝ)^3155
        have hw : |(654274873/1250000000 : ℝ)|=(654274873/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s3_1 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353246763/10000000000 : ℝ)*x 0 + (-2250806557/10000000000 : ℝ)*x 1 + (5234198789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353246763/10000000000 : ℝ)^4179 ≤ (43705505386131/100000000000000 : ℝ)^3155 := by
    have hnat : (5353246763 : ℕ)^4179*100000000000000^3155 ≤ 43705505386131^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353246763 10000000000 43705505386131 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250806557/10000000000 : ℝ)^4179 ≤ (6935860398261/50000000000000 : ℝ)^3155 := by
    have hnat : (2250806557 : ℕ)^4179*50000000000000^3155 ≤ 6935860398261^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250806557 10000000000 6935860398261 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234198789/10000000000 : ℝ)^4179 ≤ (21211386902093/50000000000000 : ℝ)^3155 := by
    have hnat : (5234198789 : ℕ)^4179*50000000000000^3155 ≤ 21211386902093^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234198789 10000000000 21211386902093 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353246763/10000000000 : ℝ), (-2250806557/10000000000 : ℝ), (5234198789/10000000000 : ℝ)] ![(43705505386131/100000000000000 : ℝ), (6935860398261/50000000000000 : ℝ), (21211386902093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353246763/10000000000 : ℝ)|^4179 ≤ (43705505386131/100000000000000 : ℝ)^3155
        have hw : |(5353246763/10000000000 : ℝ)|=(5353246763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2250806557/10000000000 : ℝ)|^4179 ≤ (6935860398261/50000000000000 : ℝ)^3155
        have hw : |(-2250806557/10000000000 : ℝ)|=(2250806557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234198789/10000000000 : ℝ)|^4179 ≤ (21211386902093/50000000000000 : ℝ)^3155
        have hw : |(5234198789/10000000000 : ℝ)|=(5234198789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s3_2 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070649369/2000000000 : ℝ)*x 0 + (1308549701/2500000000 : ℝ)*x 1 + (-562701607/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070649369/2000000000 : ℝ)^4179 ≤ (43705506272891/100000000000000 : ℝ)^3155 := by
    have hnat : (1070649369 : ℕ)^4179*100000000000000^3155 ≤ 43705506272891^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070649369 2000000000 43705506272891 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1308549701/2500000000 : ℝ)^4179 ≤ (42422773965219/100000000000000 : ℝ)^3155 := by
    have hnat : (1308549701 : ℕ)^4179*100000000000000^3155 ≤ 42422773965219^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308549701 2500000000 42422773965219 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562701607/2500000000 : ℝ)^4179 ≤ (13871719743457/100000000000000 : ℝ)^3155 := by
    have hnat : (562701607 : ℕ)^4179*100000000000000^3155 ≤ 13871719743457^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562701607 2500000000 13871719743457 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070649369/2000000000 : ℝ), (1308549701/2500000000 : ℝ), (-562701607/2500000000 : ℝ)] ![(43705506272891/100000000000000 : ℝ), (42422773965219/100000000000000 : ℝ), (13871719743457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070649369/2000000000 : ℝ)|^4179 ≤ (43705506272891/100000000000000 : ℝ)^3155
        have hw : |(1070649369/2000000000 : ℝ)|=(1070649369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1308549701/2500000000 : ℝ)|^4179 ≤ (42422773965219/100000000000000 : ℝ)^3155
        have hw : |(1308549701/2500000000 : ℝ)|=(1308549701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-562701607/2500000000 : ℝ)|^4179 ≤ (13871719743457/100000000000000 : ℝ)^3155
        have hw : |(-562701607/2500000000 : ℝ)|=(562701607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s3_3 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2179664053/5000000000 : ℝ)*x 0 + (260689133/625000000 : ℝ)*x 1 + (1139008187/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179664053/5000000000 : ℝ)^4179 ≤ (33295693154263/100000000000000 : ℝ)^3155 := by
    have hnat : (2179664053 : ℕ)^4179*100000000000000^3155 ≤ 33295693154263^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179664053 5000000000 33295693154263 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260689133/625000000 : ℝ)^4179 ≤ (31404172952503/100000000000000 : ℝ)^3155 := by
    have hnat : (260689133 : ℕ)^4179*100000000000000^3155 ≤ 31404172952503^3155*625000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260689133 625000000 31404172952503 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1139008187/2500000000 : ℝ)^4179 ≤ (7060026775467/20000000000000 : ℝ)^3155 := by
    have hnat : (1139008187 : ℕ)^4179*20000000000000^3155 ≤ 7060026775467^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139008187 2500000000 7060026775467 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179664053/5000000000 : ℝ), (260689133/625000000 : ℝ), (1139008187/2500000000 : ℝ)] ![(33295693154263/100000000000000 : ℝ), (31404172952503/100000000000000 : ℝ), (7060026775467/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179664053/5000000000 : ℝ)|^4179 ≤ (33295693154263/100000000000000 : ℝ)^3155
        have hw : |(2179664053/5000000000 : ℝ)|=(2179664053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260689133/625000000 : ℝ)|^4179 ≤ (31404172952503/100000000000000 : ℝ)^3155
        have hw : |(260689133/625000000 : ℝ)|=(260689133/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1139008187/2500000000 : ℝ)|^4179 ≤ (7060026775467/20000000000000 : ℝ)^3155
        have hw : |(1139008187/2500000000 : ℝ)|=(1139008187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s3_4 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-430478969/2000000000 : ℝ)*x 0 + (5234934539/10000000000 : ℝ)*x 1 + (2713055867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430478969/2000000000 : ℝ)^4179 ≤ (13074114924327/100000000000000 : ℝ)^3155 := by
    have hnat : (430478969 : ℕ)^4179*100000000000000^3155 ≤ 13074114924327^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430478969 2000000000 13074114924327 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5234934539/10000000000 : ℝ)^4179 ≤ (21215336310423/50000000000000 : ℝ)^3155 := by
    have hnat : (5234934539 : ℕ)^4179*50000000000000^3155 ≤ 21215336310423^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234934539 10000000000 21215336310423 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713055867/5000000000 : ℝ)^4179 ≤ (5561901554977/12500000000000 : ℝ)^3155 := by
    have hnat : (2713055867 : ℕ)^4179*12500000000000^3155 ≤ 5561901554977^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713055867 5000000000 5561901554977 12500000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430478969/2000000000 : ℝ), (5234934539/10000000000 : ℝ), (2713055867/5000000000 : ℝ)] ![(13074114924327/100000000000000 : ℝ), (21215336310423/50000000000000 : ℝ), (5561901554977/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430478969/2000000000 : ℝ)|^4179 ≤ (13074114924327/100000000000000 : ℝ)^3155
        have hw : |(-430478969/2000000000 : ℝ)|=(430478969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5234934539/10000000000 : ℝ)|^4179 ≤ (21215336310423/50000000000000 : ℝ)^3155
        have hw : |(5234934539/10000000000 : ℝ)|=(5234934539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713055867/5000000000 : ℝ)|^4179 ≤ (5561901554977/12500000000000 : ℝ)^3155
        have hw : |(2713055867/5000000000 : ℝ)|=(2713055867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s3_5 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652178749/5000000000 : ℝ)*x 0 + (-514723589/2500000000 : ℝ)*x 1 + (2713055743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652178749/5000000000 : ℝ)^4179 ≤ (21588797662419/50000000000000 : ℝ)^3155 := by
    have hnat : (2652178749 : ℕ)^4179*50000000000000^3155 ≤ 21588797662419^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652178749 5000000000 21588797662419 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514723589/2500000000 : ℝ)^4179 ≤ (12327194913773/100000000000000 : ℝ)^3155 := by
    have hnat : (514723589 : ℕ)^4179*100000000000000^3155 ≤ 12327194913773^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514723589 2500000000 12327194913773 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713055743/5000000000 : ℝ)^4179 ≤ (11123802436529/25000000000000 : ℝ)^3155 := by
    have hnat : (2713055743 : ℕ)^4179*25000000000000^3155 ≤ 11123802436529^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713055743 5000000000 11123802436529 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652178749/5000000000 : ℝ), (-514723589/2500000000 : ℝ), (2713055743/5000000000 : ℝ)] ![(21588797662419/50000000000000 : ℝ), (12327194913773/100000000000000 : ℝ), (11123802436529/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652178749/5000000000 : ℝ)|^4179 ≤ (21588797662419/50000000000000 : ℝ)^3155
        have hw : |(2652178749/5000000000 : ℝ)|=(2652178749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-514723589/2500000000 : ℝ)|^4179 ≤ (12327194913773/100000000000000 : ℝ)^3155
        have hw : |(-514723589/2500000000 : ℝ)|=(514723589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713055743/5000000000 : ℝ)|^4179 ≤ (11123802436529/25000000000000 : ℝ)^3155
        have hw : |(2713055743/5000000000 : ℝ)|=(2713055743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s3_6 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530435881/1000000000 : ℝ)*x 0 + (339131897/625000000 : ℝ)*x 1 + (-1029447063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530435881/1000000000 : ℝ)^4179 ≤ (21588804735401/50000000000000 : ℝ)^3155 := by
    have hnat : (530435881 : ℕ)^4179*50000000000000^3155 ≤ 21588804735401^3155*1000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530435881 1000000000 21588804735401 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339131897/625000000 : ℝ)^4179 ≤ (8899039485791/20000000000000 : ℝ)^3155 := by
    have hnat : (339131897 : ℕ)^4179*20000000000000^3155 ≤ 8899039485791^3155*625000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339131897 625000000 8899039485791 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029447063/5000000000 : ℝ)^4179 ≤ (12327193089747/100000000000000 : ℝ)^3155 := by
    have hnat : (1029447063 : ℕ)^4179*100000000000000^3155 ≤ 12327193089747^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029447063 5000000000 12327193089747 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530435881/1000000000 : ℝ), (339131897/625000000 : ℝ), (-1029447063/5000000000 : ℝ)] ![(21588804735401/50000000000000 : ℝ), (8899039485791/20000000000000 : ℝ), (12327193089747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530435881/1000000000 : ℝ)|^4179 ≤ (21588804735401/50000000000000 : ℝ)^3155
        have hw : |(530435881/1000000000 : ℝ)|=(530435881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339131897/625000000 : ℝ)|^4179 ≤ (8899039485791/20000000000000 : ℝ)^3155
        have hw : |(339131897/625000000 : ℝ)|=(339131897/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1029447063/5000000000 : ℝ)|^4179 ≤ (12327193089747/100000000000000 : ℝ)^3155
        have hw : |(-1029447063/5000000000 : ℝ)|=(1029447063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s3_7 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4359361649/10000000000 : ℝ)*x 0 + (4554562997/10000000000 : ℝ)*x 1 + (4172504413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359361649/10000000000 : ℝ)^4179 ≤ (33296032501217/100000000000000 : ℝ)^3155 := by
    have hnat : (4359361649 : ℕ)^4179*100000000000000^3155 ≤ 33296032501217^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359361649 10000000000 33296032501217 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4554562997/10000000000 : ℝ)^4179 ≤ (3528505102257/10000000000000 : ℝ)^3155 := by
    have hnat : (4554562997 : ℕ)^4179*10000000000000^3155 ≤ 3528505102257^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4554562997 10000000000 3528505102257 10000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172504413/10000000000 : ℝ)^4179 ≤ (6283783290567/20000000000000 : ℝ)^3155 := by
    have hnat : (4172504413 : ℕ)^4179*20000000000000^3155 ≤ 6283783290567^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172504413 10000000000 6283783290567 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359361649/10000000000 : ℝ), (4554562997/10000000000 : ℝ), (4172504413/10000000000 : ℝ)] ![(33296032501217/100000000000000 : ℝ), (3528505102257/10000000000000 : ℝ), (6283783290567/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359361649/10000000000 : ℝ)|^4179 ≤ (33296032501217/100000000000000 : ℝ)^3155
        have hw : |(4359361649/10000000000 : ℝ)|=(4359361649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4554562997/10000000000 : ℝ)|^4179 ≤ (3528505102257/10000000000000 : ℝ)^3155
        have hw : |(4554562997/10000000000 : ℝ)|=(4554562997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172504413/10000000000 : ℝ)|^4179 ≤ (6283783290567/20000000000000 : ℝ)^3155
        have hw : |(4172504413/10000000000 : ℝ)|=(4172504413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1165_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3287/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5351/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14779/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3287/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9173/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3287/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9173/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3287/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9173/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3287/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9173/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3287/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9173/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3287/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9173/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9173/100000 : ℝ) ^ (8357/2048 : ℝ) ≤ (2920309288632889/50000000000000000000 : ℝ) := by
    have hpowers : (9173/100000 : ℝ)^8357 ≤ (2920309288632889/50000000000000000000 : ℝ)^2048 := by
      have hnat : (9173 : ℕ)^8357*50000000000000000000^2048 ≤ 2920309288632889^2048*100000^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9173 100000 2920309288632889 50000000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9173/100000 : ℝ)) (X := (2920309288632889/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3287/20000 : ℝ) ^ (8357/2048 : ℝ) ≤ (63080658371867787/100000000000000000000 : ℝ) := by
    have hpowers : (3287/20000 : ℝ)^8357 ≤ (63080658371867787/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3287 : ℕ)^8357*100000000000000000000^2048 ≤ 63080658371867787^2048*20000^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3287 20000 63080658371867787 100000000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3287/20000 : ℝ)) (X := (63080658371867787/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002920309288632889/25000000000000000000 : ℝ) ≤ (5000143126235023/5000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (25002920309288632889/25000000000000000000 : ℝ)^2048 ≤ (5000143126235023/5000000000000000 : ℝ)^8357 := by
      have hnat : (25002920309288632889 : ℕ)^2048*5000000000000000^8357 ≤ 5000143126235023^8357*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002920309288632889 25000000000000000000 5000143126235023 5000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000143126235023/5000000000000000 : ℝ)) (X := (25002920309288632889/25000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20013784255389826713/20000000000000000000 : ℝ) ≤ (400067542931101/400000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (20013784255389826713/20000000000000000000 : ℝ)^2048 ≤ (400067542931101/400000000000000 : ℝ)^8357 := by
      have hnat : (20013784255389826713 : ℕ)^2048*400000000000000^8357 ≤ 400067542931101^8357*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20013784255389826713 20000000000000000000 400067542931101 400000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400067542931101/400000000000000 : ℝ)) (X := (20013784255389826713/20000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50063080658371867787/50000000000000000000 : ℝ) ≤ (2500772723521251/2500000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (50063080658371867787/50000000000000000000 : ℝ)^2048 ≤ (2500772723521251/2500000000000000 : ℝ)^8357 := by
      have hnat : (50063080658371867787 : ℕ)^2048*2500000000000000^8357 ≤ 2500772723521251^8357*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50063080658371867787 50000000000000000000 2500772723521251 2500000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500772723521251/2500000000000000 : ℝ)) (X := (50063080658371867787/50000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2920309288632889/50000000000000000000 : ℝ) ≤ ((36298175893951732159/36310000000000000000 : ℝ)+2*(1402320807479/726200000000000 : ℝ)*(9173/100000 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (36298175893951732159/36310000000000000000 : ℝ)+2*(1402320807479/726200000000000 : ℝ)*(9173/100000 : ℝ)=(5000143126235023/5000000000000000 : ℝ) by norm_num, show 1+2*(2920309288632889/50000000000000000000 : ℝ)=(25002920309288632889/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(63080658371867787/100000000000000000000 : ℝ)+(2920309288632889/50000000000000000000 : ℝ) ≤ ((36298175893951732159/36310000000000000000 : ℝ)+(1402320807479/726200000000000 : ℝ)*((3287/20000 : ℝ)+(9173/100000 : ℝ)))^(8357/2048 : ℝ) := by
    rw [show (36298175893951732159/36310000000000000000 : ℝ)+(1402320807479/726200000000000 : ℝ)*((3287/20000 : ℝ)+(9173/100000 : ℝ))=(400067542931101/400000000000000 : ℝ) by norm_num, show 1+(63080658371867787/100000000000000000000 : ℝ)+(2920309288632889/50000000000000000000 : ℝ)=(20013784255389826713/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(63080658371867787/100000000000000000000 : ℝ) ≤ ((36298175893951732159/36310000000000000000 : ℝ)+2*(1402320807479/726200000000000 : ℝ)*(3287/20000 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (36298175893951732159/36310000000000000000 : ℝ)+2*(1402320807479/726200000000000 : ℝ)*(3287/20000 : ℝ)=(2500772723521251/2500000000000000 : ℝ) by norm_num, show 1+2*(63080658371867787/100000000000000000000 : ℝ)=(50063080658371867787/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36298175893951732159/36310000000000000000 : ℝ)*(X 1 0+X 2 0)+(1402320807479/726200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (9173/100000 : ℝ)) (hi := (3287/20000 : ℝ)) (c := (36298175893951732159/36310000000000000000 : ℝ)) (alpha := (1402320807479/726200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36298175893951732159/36310000000000000000 : ℝ)*(X 0 1+X 2 1)+(1402320807479/726200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (9173/100000 : ℝ)) (hi := (3287/20000 : ℝ)) (c := (36298175893951732159/36310000000000000000 : ℝ)) (alpha := (1402320807479/726200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36298175893951732159/36310000000000000000 : ℝ)*(X 0 2+X 1 2)+(1402320807479/726200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (9173/100000 : ℝ)) (hi := (3287/20000 : ℝ)) (c := (36298175893951732159/36310000000000000000 : ℝ)) (alpha := (1402320807479/726200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2152377907/10000000000 : ℝ)*X 0 0+(5426851289/10000000000 : ℝ)*X 0 1+(654274873/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353246763/10000000000 : ℝ)*X 1 0+(-2250806557/10000000000 : ℝ)*X 1 1+(5234198789/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070649369/2000000000 : ℝ)*X 2 0+(1308549701/2500000000 : ℝ)*X 2 1+(-562701607/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179664053/5000000000 : ℝ)*X 0 0+(260689133/625000000 : ℝ)*X 0 1+(1139008187/2500000000 : ℝ)*X 0 2+(2179664053/5000000000 : ℝ)*X 1 0+(260689133/625000000 : ℝ)*X 1 1+(1139008187/2500000000 : ℝ)*X 1 2+(2179664053/5000000000 : ℝ)*X 2 0+(260689133/625000000 : ℝ)*X 2 1+(1139008187/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-430478969/2000000000 : ℝ)*X 0 0+(5234934539/10000000000 : ℝ)*X 0 1+(2713055867/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652178749/5000000000 : ℝ)*X 1 0+(-514723589/2500000000 : ℝ)*X 1 1+(2713055743/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530435881/1000000000 : ℝ)*X 2 0+(339131897/625000000 : ℝ)*X 2 1+(-1029447063/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4359361649/10000000000 : ℝ)*X 0 0+(4554562997/10000000000 : ℝ)*X 0 1+(4172504413/10000000000 : ℝ)*X 0 2+(4359361649/10000000000 : ℝ)*X 1 0+(4554562997/10000000000 : ℝ)*X 1 1+(4172504413/10000000000 : ℝ)*X 1 2+(4359361649/10000000000 : ℝ)*X 2 0+(4554562997/10000000000 : ℝ)*X 2 1+(4172504413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11793864089673228282717422391/1815500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1596582171/100000000000000 : ℝ)*(base19) + (769304729/50000000000000 : ℝ)*(base23) + (14719673/20000000000000 : ℝ)*(lower2) + (61926347/50000000000000 : ℝ)*(upper3) + (172701833/100000000000000 : ℝ)*(upper5) + (3894067320787517/100000000000000 : ℝ)*(major0) + (3894067320787517/100000000000000 : ℝ)*(major1) + (3894067320787517/100000000000000 : ℝ)*(major2) + (5190722482227503/100000000000000 : ℝ)*(sp0) + (2595374402994599/50000000000000 : ℝ)*(sp1) + (5190748863961911/100000000000000 : ℝ)*(sp2) + (1298685431634277/50000000000000 : ℝ)*(sp3) + (27920343867/100000000000000 : ℝ)*(sp4) + (6579597433/50000000000000 : ℝ)*(sp7) + (129869201123171/5000000000000 : ℝ)*(f.failure) + (5190750402571369/100000000000000 : ℝ)*(f.sum) + (152947760338177/36310000000000000000000000000 : ℝ)*base66 + (19241263732097190797/3631000000000000000000000000000000 : ℝ)*base68 + (447085679663190797/3631000000000000000000000000000000 : ℝ)*base70 + (27799928603124809203/3631000000000000000000000000000000 : ℝ)*base71 + (153240059687037/36310000000000000000000000000 : ℝ)*base74 + (7484511053484809203/3631000000000000000000000000000000 : ℝ)*base75 + (45757203511173809203/3631000000000000000000000000000000 : ℝ)*base77 + (21077974763818809203/3631000000000000000000000000000000 : ℝ)*base79 + (223950339376377/36310000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (430943/62500000000000000000 : ℝ)*base89 + (430943/62500000000000000000 : ℝ)*base91 + (430943/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (55737758120564451779872431/9077500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (88289303/12500000000000 : ℝ)*(base19) + (2124693703/100000000000000 : ℝ)*(base23) + (1809319/20000000000000 : ℝ)*(upper2) + (12501249/25000000000000 : ℝ)*(upper3) + (36145589/50000000000000 : ℝ)*(upper5) + (19620408933001/500000000000 : ℝ)*(major0) + (19620408933001/500000000000 : ℝ)*(major1) + (19620408933001/500000000000 : ℝ)*(major2) + (7468631109/100000000000000 : ℝ)*(sp1) + (19135708319/100000000000000 : ℝ)*(sp2) + (5230759380427759/100000000000000 : ℝ)*(sp4) + (2615375602741113/50000000000000 : ℝ)*(sp5) + (5230738120025737/100000000000000 : ℝ)*(sp6) + (1308701994049479/50000000000000 : ℝ)*(sp7) + (1308701994049479/50000000000000 : ℝ)*(f.failure) + (5230759380427759/100000000000000 : ℝ)*(f.sum) + (7281621844617/3631000000000000000000000000 : ℝ)*base66 + (288625441344155841/18155000000000000000000000000000 : ℝ)*base68 + (195778965520770841/18155000000000000000000000000000 : ℝ)*base70 + (171529635154805841/18155000000000000000000000000000 : ℝ)*base72 + (13107196683287/3631000000000000000000000000 : ℝ)*base74 + (301690710042075841/18155000000000000000000000000000 : ℝ)*base76 + (144760374685355841/18155000000000000000000000000000 : ℝ)*base78 + (304262557055000841/18155000000000000000000000000000 : ℝ)*base80 + (12961395891/2836718750000000000000000 : ℝ)*base82 + (4936507/625000000000000000000 : ℝ)*base89 + (4936507/625000000000000000000 : ℝ)*base91 + (4936507/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1165_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3287/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5351/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14779/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1165_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1165_s4_0 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1077600359/5000000000 : ℝ)*x 0 + (540081273/1000000000 : ℝ)*x 1 + (1314597539/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077600359/5000000000 : ℝ)^4179 ≤ (13096694886583/100000000000000 : ℝ)^3155 := by
    have hnat : (1077600359 : ℕ)^4179*100000000000000^3155 ≤ 13096694886583^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077600359 5000000000 13096694886583 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540081273/1000000000 : ℝ)^4179 ≤ (44220630536159/100000000000000 : ℝ)^3155 := by
    have hnat : (540081273 : ℕ)^4179*100000000000000^3155 ≤ 44220630536159^3155*1000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540081273 1000000000 44220630536159 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314597539/2500000000 : ℝ)^4179 ≤ (10670668639889/25000000000000 : ℝ)^3155 := by
    have hnat : (1314597539 : ℕ)^4179*25000000000000^3155 ≤ 10670668639889^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314597539 2500000000 10670668639889 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1077600359/5000000000 : ℝ), (540081273/1000000000 : ℝ), (1314597539/2500000000 : ℝ)] ![(13096694886583/100000000000000 : ℝ), (44220630536159/100000000000000 : ℝ), (10670668639889/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1077600359/5000000000 : ℝ)|^4179 ≤ (13096694886583/100000000000000 : ℝ)^3155
        have hw : |(-1077600359/5000000000 : ℝ)|=(1077600359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540081273/1000000000 : ℝ)|^4179 ≤ (44220630536159/100000000000000 : ℝ)^3155
        have hw : |(540081273/1000000000 : ℝ)|=(540081273/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1314597539/2500000000 : ℝ)|^4179 ≤ (10670668639889/25000000000000 : ℝ)^3155
        have hw : |(1314597539/2500000000 : ℝ)|=(1314597539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s4_1 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673364731/5000000000 : ℝ)*x 0 + (-222756149/1000000000 : ℝ)*x 1 + (2629195159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673364731/5000000000 : ℝ)^4179 ≤ (43635040324731/100000000000000 : ℝ)^3155 := by
    have hnat : (2673364731 : ℕ)^4179*100000000000000^3155 ≤ 43635040324731^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673364731 5000000000 43635040324731 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222756149/1000000000 : ℝ)^4179 ≤ (427571355051/3125000000000 : ℝ)^3155 := by
    have hnat : (222756149 : ℕ)^4179*3125000000000^3155 ≤ 427571355051^3155*1000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222756149 1000000000 427571355051 3125000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629195159/5000000000 : ℝ)^4179 ≤ (4268267630131/10000000000000 : ℝ)^3155 := by
    have hnat : (2629195159 : ℕ)^4179*10000000000000^3155 ≤ 4268267630131^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629195159 5000000000 4268267630131 10000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673364731/5000000000 : ℝ), (-222756149/1000000000 : ℝ), (2629195159/5000000000 : ℝ)] ![(43635040324731/100000000000000 : ℝ), (427571355051/3125000000000 : ℝ), (4268267630131/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673364731/5000000000 : ℝ)|^4179 ≤ (43635040324731/100000000000000 : ℝ)^3155
        have hw : |(2673364731/5000000000 : ℝ)|=(2673364731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-222756149/1000000000 : ℝ)|^4179 ≤ (427571355051/3125000000000 : ℝ)^3155
        have hw : |(-222756149/1000000000 : ℝ)|=(222756149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629195159/5000000000 : ℝ)|^4179 ≤ (4268267630131/10000000000000 : ℝ)^3155
        have hw : |(2629195159/5000000000 : ℝ)|=(2629195159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s4_2 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346729383/10000000000 : ℝ)*x 0 + (5258390261/10000000000 : ℝ)*x 1 + (-222756167/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346729383/10000000000 : ℝ)^4179 ≤ (1363594983461/3125000000000 : ℝ)^3155 := by
    have hnat : (5346729383 : ℕ)^4179*3125000000000^3155 ≤ 1363594983461^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346729383 10000000000 1363594983461 3125000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258390261/10000000000 : ℝ)^4179 ≤ (42682675688471/100000000000000 : ℝ)^3155 := by
    have hnat : (5258390261 : ℕ)^4179*100000000000000^3155 ≤ 42682675688471^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258390261 10000000000 42682675688471 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222756167/1000000000 : ℝ)^4179 ≤ (13682284826081/100000000000000 : ℝ)^3155 := by
    have hnat : (222756167 : ℕ)^4179*100000000000000^3155 ≤ 13682284826081^3155*1000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222756167 1000000000 13682284826081 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346729383/10000000000 : ℝ), (5258390261/10000000000 : ℝ), (-222756167/1000000000 : ℝ)] ![(1363594983461/3125000000000 : ℝ), (42682675688471/100000000000000 : ℝ), (13682284826081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346729383/10000000000 : ℝ)|^4179 ≤ (1363594983461/3125000000000 : ℝ)^3155
        have hw : |(5346729383/10000000000 : ℝ)|=(5346729383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258390261/10000000000 : ℝ)|^4179 ≤ (42682675688471/100000000000000 : ℝ)^3155
        have hw : |(5258390261/10000000000 : ℝ)|=(5258390261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-222756167/1000000000 : ℝ)|^4179 ≤ (13682284826081/100000000000000 : ℝ)^3155
        have hw : |(-222756167/1000000000 : ℝ)|=(222756167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s4_3 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (34888113/80000000 : ℝ)*x 0 + (844199851/2000000000 : ℝ)*x 1 + (2252812137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34888113/80000000 : ℝ)^4179 ≤ (33312751276807/100000000000000 : ℝ)^3155 := by
    have hnat : (34888113 : ℕ)^4179*100000000000000^3155 ≤ 33312751276807^3155*80000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34888113 80000000 33312751276807 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844199851/2000000000 : ℝ)^4179 ≤ (31903511739741/100000000000000 : ℝ)^3155 := by
    have hnat : (844199851 : ℕ)^4179*100000000000000^3155 ≤ 31903511739741^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844199851 2000000000 31903511739741 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252812137/5000000000 : ℝ)^4179 ≤ (3478373696329/10000000000000 : ℝ)^3155 := by
    have hnat : (2252812137 : ℕ)^4179*10000000000000^3155 ≤ 3478373696329^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252812137 5000000000 3478373696329 10000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34888113/80000000 : ℝ), (844199851/2000000000 : ℝ), (2252812137/5000000000 : ℝ)] ![(33312751276807/100000000000000 : ℝ), (31903511739741/100000000000000 : ℝ), (3478373696329/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34888113/80000000 : ℝ)|^4179 ≤ (33312751276807/100000000000000 : ℝ)^3155
        have hw : |(34888113/80000000 : ℝ)|=(34888113/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(844199851/2000000000 : ℝ)|^4179 ≤ (31903511739741/100000000000000 : ℝ)^3155
        have hw : |(844199851/2000000000 : ℝ)|=(844199851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252812137/5000000000 : ℝ)|^4179 ≤ (3478373696329/10000000000000 : ℝ)^3155
        have hw : |(2252812137/5000000000 : ℝ)|=(2252812137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s4_4 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2155207701/10000000000 : ℝ)*x 0 + (525879291/1000000000 : ℝ)*x 1 + (2700204131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155207701/10000000000 : ℝ)^4179 ≤ (2619350218687/20000000000000 : ℝ)^3155 := by
    have hnat : (2155207701 : ℕ)^4179*20000000000000^3155 ≤ 2619350218687^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155207701 10000000000 2619350218687 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525879291/1000000000 : ℝ)^4179 ≤ (42687004850601/100000000000000 : ℝ)^3155 := by
    have hnat : (525879291 : ℕ)^4179*100000000000000^3155 ≤ 42687004850601^3155*1000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525879291 1000000000 42687004850601 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700204131/5000000000 : ℝ)^4179 ≤ (172719703283/390625000000 : ℝ)^3155 := by
    have hnat : (2700204131 : ℕ)^4179*390625000000^3155 ≤ 172719703283^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700204131 5000000000 172719703283 390625000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2155207701/10000000000 : ℝ), (525879291/1000000000 : ℝ), (2700204131/5000000000 : ℝ)] ![(2619350218687/20000000000000 : ℝ), (42687004850601/100000000000000 : ℝ), (172719703283/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2155207701/10000000000 : ℝ)|^4179 ≤ (2619350218687/20000000000000 : ℝ)^3155
        have hw : |(-2155207701/10000000000 : ℝ)|=(2155207701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525879291/1000000000 : ℝ)|^4179 ≤ (42687004850601/100000000000000 : ℝ)^3155
        have hw : |(525879291/1000000000 : ℝ)|=(525879291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700204131/5000000000 : ℝ)|^4179 ≤ (172719703283/390625000000 : ℝ)^3155
        have hw : |(2700204131/5000000000 : ℝ)|=(2700204131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s4_5 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5310587487/10000000000 : ℝ)*x 0 + (-1042771591/5000000000 : ℝ)*x 1 + (1080081631/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310587487/10000000000 : ℝ)^4179 ≤ (5405597470569/12500000000000 : ℝ)^3155 := by
    have hnat : (5310587487 : ℕ)^4179*12500000000000^3155 ≤ 5405597470569^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310587487 10000000000 5405597470569 12500000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042771591/5000000000 : ℝ)^4179 ≤ (12538977336429/100000000000000 : ℝ)^3155 := by
    have hnat : (1042771591 : ℕ)^4179*100000000000000^3155 ≤ 12538977336429^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042771591 5000000000 12538977336429 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080081631/2000000000 : ℝ)^4179 ≤ (44216242880037/100000000000000 : ℝ)^3155 := by
    have hnat : (1080081631 : ℕ)^4179*100000000000000^3155 ≤ 44216242880037^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080081631 2000000000 44216242880037 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310587487/10000000000 : ℝ), (-1042771591/5000000000 : ℝ), (1080081631/2000000000 : ℝ)] ![(5405597470569/12500000000000 : ℝ), (12538977336429/100000000000000 : ℝ), (44216242880037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310587487/10000000000 : ℝ)|^4179 ≤ (5405597470569/12500000000000 : ℝ)^3155
        have hw : |(5310587487/10000000000 : ℝ)|=(5310587487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1042771591/5000000000 : ℝ)|^4179 ≤ (12538977336429/100000000000000 : ℝ)^3155
        have hw : |(-1042771591/5000000000 : ℝ)|=(1042771591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080081631/2000000000 : ℝ)|^4179 ≤ (44216242880037/100000000000000 : ℝ)^3155
        have hw : |(1080081631/2000000000 : ℝ)|=(1080081631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s4_6 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655293617/5000000000 : ℝ)*x 0 + (2700204047/5000000000 : ℝ)*x 1 + (-260692951/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655293617/5000000000 : ℝ)^4179 ≤ (43244777035671/100000000000000 : ℝ)^3155 := by
    have hnat : (2655293617 : ℕ)^4179*100000000000000^3155 ≤ 43244777035671^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655293617 5000000000 43244777035671 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700204047/5000000000 : ℝ)^4179 ≤ (22108121109247/50000000000000 : ℝ)^3155 := by
    have hnat : (2700204047 : ℕ)^4179*50000000000000^3155 ≤ 22108121109247^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700204047 5000000000 22108121109247 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260692951/1250000000 : ℝ)^4179 ≤ (6269490364487/50000000000000 : ℝ)^3155 := by
    have hnat : (260692951 : ℕ)^4179*50000000000000^3155 ≤ 6269490364487^3155*1250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260692951 1250000000 6269490364487 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655293617/5000000000 : ℝ), (2700204047/5000000000 : ℝ), (-260692951/1250000000 : ℝ)] ![(43244777035671/100000000000000 : ℝ), (22108121109247/50000000000000 : ℝ), (6269490364487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655293617/5000000000 : ℝ)|^4179 ≤ (43244777035671/100000000000000 : ℝ)^3155
        have hw : |(2655293617/5000000000 : ℝ)|=(2655293617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700204047/5000000000 : ℝ)|^4179 ≤ (22108121109247/50000000000000 : ℝ)^3155
        have hw : |(2700204047/5000000000 : ℝ)|=(2700204047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-260692951/1250000000 : ℝ)|^4179 ≤ (6269490364487/50000000000000 : ℝ)^3155
        have hw : |(-260692951/1250000000 : ℝ)|=(260692951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s4_7 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (545128477/1250000000 : ℝ)*x 0 + (563102353/1250000000 : ℝ)*x 1 + (4221808061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545128477/1250000000 : ℝ)^4179 ≤ (33312889802843/100000000000000 : ℝ)^3155 := by
    have hnat : (545128477 : ℕ)^4179*100000000000000^3155 ≤ 33312889802843^3155*1250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545128477 1250000000 33312889802843 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563102353/1250000000 : ℝ)^4179 ≤ (3477550088893/10000000000000 : ℝ)^3155 := by
    have hnat : (563102353 : ℕ)^4179*10000000000000^3155 ≤ 3477550088893^3155*1250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563102353 1250000000 3477550088893 10000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4221808061/10000000000 : ℝ)^4179 ≤ (3191160929817/10000000000000 : ℝ)^3155 := by
    have hnat : (4221808061 : ℕ)^4179*10000000000000^3155 ≤ 3191160929817^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221808061 10000000000 3191160929817 10000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545128477/1250000000 : ℝ), (563102353/1250000000 : ℝ), (4221808061/10000000000 : ℝ)] ![(33312889802843/100000000000000 : ℝ), (3477550088893/10000000000000 : ℝ), (3191160929817/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545128477/1250000000 : ℝ)|^4179 ≤ (33312889802843/100000000000000 : ℝ)^3155
        have hw : |(545128477/1250000000 : ℝ)|=(545128477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563102353/1250000000 : ℝ)|^4179 ≤ (3477550088893/10000000000000 : ℝ)^3155
        have hw : |(563102353/1250000000 : ℝ)|=(563102353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4221808061/10000000000 : ℝ)|^4179 ≤ (3191160929817/10000000000000 : ℝ)^3155
        have hw : |(4221808061/10000000000 : ℝ)|=(4221808061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1165_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14779/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5351/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5609/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14779/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5351/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14779/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5351/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14779/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5351/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14779/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5351/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14779/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5351/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14779/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5351/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5351/50000 : ℝ) ^ (8357/2048 : ℝ) ≤ (5478192254000117/50000000000000000000 : ℝ) := by
    have hpowers : (5351/50000 : ℝ)^8357 ≤ (5478192254000117/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5351 : ℕ)^8357*50000000000000000000^2048 ≤ 5478192254000117^2048*50000^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5351 50000 5478192254000117 50000000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5351/50000 : ℝ)) (X := (5478192254000117/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14779/100000 : ℝ) ^ (8357/2048 : ℝ) ≤ (40896061217176961/100000000000000000000 : ℝ) := by
    have hpowers : (14779/100000 : ℝ)^8357 ≤ (40896061217176961/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14779 : ℕ)^8357*100000000000000000000^2048 ≤ 40896061217176961^2048*100000^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14779 100000 40896061217176961 100000000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14779/100000 : ℝ)) (X := (40896061217176961/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005478192254000117/25000000000000000000 : ℝ) ≤ (10000536958710653/10000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (25005478192254000117/25000000000000000000 : ℝ)^2048 ≤ (10000536958710653/10000000000000000 : ℝ)^8357 := by
      have hnat : (25005478192254000117 : ℕ)^2048*10000000000000000^8357 ≤ 10000536958710653^8357*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005478192254000117 25000000000000000000 10000536958710653 10000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000536958710653/10000000000000000 : ℝ)) (X := (25005478192254000117/25000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010370489145035439/20000000000000000000 : ℝ) ≤ (5000635234116413/5000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (20010370489145035439/20000000000000000000 : ℝ)^2048 ≤ (5000635234116413/5000000000000000 : ℝ)^8357 := by
      have hnat : (20010370489145035439 : ℕ)^2048*5000000000000000^8357 ≤ 5000635234116413^8357*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010370489145035439 20000000000000000000 5000635234116413 5000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000635234116413/5000000000000000 : ℝ)) (X := (20010370489145035439/20000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50040896061217176961/50000000000000000000 : ℝ) ≤ (10002003977754999/10000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (50040896061217176961/50000000000000000000 : ℝ)^2048 ≤ (10002003977754999/10000000000000000 : ℝ)^8357 := by
      have hnat : (50040896061217176961 : ℕ)^2048*10000000000000000^8357 ≤ 10002003977754999^8357*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040896061217176961 50000000000000000000 10002003977754999 10000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002003977754999/10000000000000000 : ℝ)) (X := (50040896061217176961/50000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5478192254000117/50000000000000000000 : ℝ) ≤ ((40756489142850741389/40770000000000000000 : ℝ)+2*(733509522173/407700000000000 : ℝ)*(5351/50000 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (40756489142850741389/40770000000000000000 : ℝ)+2*(733509522173/407700000000000 : ℝ)*(5351/50000 : ℝ)=(10000536958710653/10000000000000000 : ℝ) by norm_num, show 1+2*(5478192254000117/50000000000000000000 : ℝ)=(25005478192254000117/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40896061217176961/100000000000000000000 : ℝ)+(5478192254000117/50000000000000000000 : ℝ) ≤ ((40756489142850741389/40770000000000000000 : ℝ)+(733509522173/407700000000000 : ℝ)*((14779/100000 : ℝ)+(5351/50000 : ℝ)))^(8357/2048 : ℝ) := by
    rw [show (40756489142850741389/40770000000000000000 : ℝ)+(733509522173/407700000000000 : ℝ)*((14779/100000 : ℝ)+(5351/50000 : ℝ))=(5000635234116413/5000000000000000 : ℝ) by norm_num, show 1+(40896061217176961/100000000000000000000 : ℝ)+(5478192254000117/50000000000000000000 : ℝ)=(20010370489145035439/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40896061217176961/100000000000000000000 : ℝ) ≤ ((40756489142850741389/40770000000000000000 : ℝ)+2*(733509522173/407700000000000 : ℝ)*(14779/100000 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (40756489142850741389/40770000000000000000 : ℝ)+2*(733509522173/407700000000000 : ℝ)*(14779/100000 : ℝ)=(10002003977754999/10000000000000000 : ℝ) by norm_num, show 1+2*(40896061217176961/100000000000000000000 : ℝ)=(50040896061217176961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (40756489142850741389/40770000000000000000 : ℝ)*(X 1 0+X 2 0)+(733509522173/407700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (5351/50000 : ℝ)) (hi := (14779/100000 : ℝ)) (c := (40756489142850741389/40770000000000000000 : ℝ)) (alpha := (733509522173/407700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (40756489142850741389/40770000000000000000 : ℝ)*(X 0 1+X 2 1)+(733509522173/407700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (5351/50000 : ℝ)) (hi := (14779/100000 : ℝ)) (c := (40756489142850741389/40770000000000000000 : ℝ)) (alpha := (733509522173/407700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (40756489142850741389/40770000000000000000 : ℝ)*(X 0 2+X 1 2)+(733509522173/407700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (5351/50000 : ℝ)) (hi := (14779/100000 : ℝ)) (c := (40756489142850741389/40770000000000000000 : ℝ)) (alpha := (733509522173/407700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1077600359/5000000000 : ℝ)*X 0 0+(540081273/1000000000 : ℝ)*X 0 1+(1314597539/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673364731/5000000000 : ℝ)*X 1 0+(-222756149/1000000000 : ℝ)*X 1 1+(2629195159/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346729383/10000000000 : ℝ)*X 2 0+(5258390261/10000000000 : ℝ)*X 2 1+(-222756167/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((34888113/80000000 : ℝ)*X 0 0+(844199851/2000000000 : ℝ)*X 0 1+(2252812137/5000000000 : ℝ)*X 0 2+(34888113/80000000 : ℝ)*X 1 0+(844199851/2000000000 : ℝ)*X 1 1+(2252812137/5000000000 : ℝ)*X 1 2+(34888113/80000000 : ℝ)*X 2 0+(844199851/2000000000 : ℝ)*X 2 1+(2252812137/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2155207701/10000000000 : ℝ)*X 0 0+(525879291/1000000000 : ℝ)*X 0 1+(2700204131/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310587487/10000000000 : ℝ)*X 1 0+(-1042771591/5000000000 : ℝ)*X 1 1+(1080081631/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655293617/5000000000 : ℝ)*X 2 0+(2700204047/5000000000 : ℝ)*X 2 1+(-260692951/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((545128477/1250000000 : ℝ)*X 0 0+(563102353/1250000000 : ℝ)*X 0 1+(4221808061/10000000000 : ℝ)*X 0 2+(545128477/1250000000 : ℝ)*X 1 0+(563102353/1250000000 : ℝ)*X 1 1+(4221808061/10000000000 : ℝ)*X 1 2+(545128477/1250000000 : ℝ)*X 2 0+(563102353/1250000000 : ℝ)*X 2 1+(4221808061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (362947558769369411904016379/37750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (859320913/50000000000000 : ℝ)*(base19) + (322286019/20000000000000 : ℝ)*(base23) + (351385111/100000000000000 : ℝ)*(upper3) + (370749/20000000000000 : ℝ)*(upper4) + (8595559/12500000000000 : ℝ)*(upper5) + (2633724425899199/50000000000000 : ℝ)*(major0) + (2633724425899199/50000000000000 : ℝ)*(major1) + (2633724425899199/50000000000000 : ℝ)*(major2) + (3510706364601189/50000000000000 : ℝ)*(sp0) + (7021451658568263/100000000000000 : ℝ)*(sp1) + (1404290353155999/20000000000000 : ℝ)*(sp2) + (878354223159287/25000000000000 : ℝ)*(sp3) + (1270250241/3125000000000 : ℝ)*(sp4) + (13556633027/50000000000000 : ℝ)*(sp7) + (1756722002951601/50000000000000 : ℝ)*(f.failure) + (7021453377210089/100000000000000 : ℝ)*(f.sum) + (32390015429813/10192500000000000000000000000 : ℝ)*base66 + (7667691513122052589/2038500000000000000000000000000000 : ℝ)*base68 + (10516584122790947411/2038500000000000000000000000000000 : ℝ)*base69 + (33934006541621052589/2038500000000000000000000000000000 : ℝ)*base72 + (423007013309/1274062500000000000000000000 : ℝ)*base73 + (39117207729093947411/2038500000000000000000000000000000 : ℝ)*base75 + (6740067099912552589/2038500000000000000000000000000000 : ℝ)*base78 + (10597087024269552589/2038500000000000000000000000000000 : ℝ)*base80 + (22354726058303/10192500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1876867/625000000000000000000 : ℝ)*base90 + (1876867/625000000000000000000 : ℝ)*base92 + (1876867/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41226865393844647692525957/75500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1143498561/100000000000000 : ℝ)*(base19) + (487272357/50000000000000 : ℝ)*(base23) + (32152209/20000000000000 : ℝ)*(upper2) + (19696787/20000000000000 : ℝ)*(upper5) + (5297411099170017/100000000000000 : ℝ)*(major0) + (5297411099170017/100000000000000 : ℝ)*(major1) + (5297411099170017/100000000000000 : ℝ)*(major2) + (8064856591/100000000000000 : ℝ)*(sp0) + (39779603513/100000000000000 : ℝ)*(sp1) + (19904489051/100000000000000 : ℝ)*(sp2) + (3530692486997289/50000000000000 : ℝ)*(sp4) + (1412270423149819/20000000000000 : ℝ)*(sp5) + (1765343039954351/25000000000000 : ℝ)*(sp6) + (883357285321787/25000000000000 : ℝ)*(sp7) + (883357285321787/25000000000000 : ℝ)*(f.failure) + (7061393038851169/100000000000000 : ℝ)*(f.sum) + (3109230029077/755000000000000000000000000 : ℝ)*base66 + (336621599228524681/151000000000000000000000000000000 : ℝ)*base68 + (138796846226524681/151000000000000000000000000000000 : ℝ)*base70 + (1069269385544475319/151000000000000000000000000000000 : ℝ)*base71 + (492868900723/755000000000000000000000000 : ℝ)*base73 + (1855566465503524681/151000000000000000000000000000000 : ℝ)*base76 + (1476972915953524681/151000000000000000000000000000000 : ℝ)*base78 + (3797584014344475319/151000000000000000000000000000000 : ℝ)*base79 + (441353790553/755000000000000000000000000 : ℝ)*base81 + (2589929/312500000000000000000 : ℝ)*base90 + (2589929/312500000000000000000 : ℝ)*base92 + (2589929/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1165_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14779/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5351/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1165_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1165_s5_0 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2155790351/10000000000 : ℝ)*x 0 + (1078863171/2000000000 : ℝ)*x 1 + (5264499753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155790351/10000000000 : ℝ)^4179 ≤ (13101441108673/100000000000000 : ℝ)^3155 := by
    have hnat : (2155790351 : ℕ)^4179*100000000000000^3155 ≤ 13101441108673^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155790351 10000000000 13101441108673 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078863171/2000000000 : ℝ)^4179 ≤ (11037546045647/25000000000000 : ℝ)^3155 := by
    have hnat : (1078863171 : ℕ)^4179*25000000000000^3155 ≤ 11037546045647^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078863171 2000000000 11037546045647 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264499753/10000000000 : ℝ)^4179 ≤ (2137418734627/5000000000000 : ℝ)^3155 := by
    have hnat : (5264499753 : ℕ)^4179*5000000000000^3155 ≤ 2137418734627^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264499753 10000000000 2137418734627 5000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2155790351/10000000000 : ℝ), (1078863171/2000000000 : ℝ), (5264499753/10000000000 : ℝ)] ![(13101441108673/100000000000000 : ℝ), (11037546045647/25000000000000 : ℝ), (2137418734627/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2155790351/10000000000 : ℝ)|^4179 ≤ (13101441108673/100000000000000 : ℝ)^3155
        have hw : |(-2155790351/10000000000 : ℝ)|=(2155790351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078863171/2000000000 : ℝ)|^4179 ≤ (11037546045647/25000000000000 : ℝ)^3155
        have hw : |(1078863171/2000000000 : ℝ)|=(1078863171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264499753/10000000000 : ℝ)|^4179 ≤ (2137418734627/5000000000000 : ℝ)^3155
        have hw : |(5264499753/10000000000 : ℝ)|=(5264499753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s5_1 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345095937/10000000000 : ℝ)*x 0 + (-1110827129/5000000000 : ℝ)*x 1 + (5264499609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345095937/10000000000 : ℝ)^4179 ≤ (2180869150963/5000000000000 : ℝ)^3155 := by
    have hnat : (5345095937 : ℕ)^4179*5000000000000^3155 ≤ 2180869150963^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345095937 10000000000 2180869150963 5000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1110827129/5000000000 : ℝ)^4179 ≤ (6817121909583/50000000000000 : ℝ)^3155 := by
    have hnat : (1110827129 : ℕ)^4179*50000000000000^3155 ≤ 6817121909583^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110827129 5000000000 6817121909583 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264499609/10000000000 : ℝ)^4179 ≤ (4274837314373/10000000000000 : ℝ)^3155 := by
    have hnat : (5264499609 : ℕ)^4179*10000000000000^3155 ≤ 4274837314373^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264499609 10000000000 4274837314373 10000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345095937/10000000000 : ℝ), (-1110827129/5000000000 : ℝ), (5264499609/10000000000 : ℝ)] ![(2180869150963/5000000000000 : ℝ), (6817121909583/50000000000000 : ℝ), (4274837314373/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345095937/10000000000 : ℝ)|^4179 ≤ (2180869150963/5000000000000 : ℝ)^3155
        have hw : |(5345095937/10000000000 : ℝ)|=(5345095937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1110827129/5000000000 : ℝ)|^4179 ≤ (6817121909583/50000000000000 : ℝ)^3155
        have hw : |(-1110827129/5000000000 : ℝ)|=(1110827129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264499609/10000000000 : ℝ)|^4179 ≤ (4274837314373/10000000000000 : ℝ)^3155
        have hw : |(5264499609/10000000000 : ℝ)|=(5264499609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s5_2 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345095939/10000000000 : ℝ)*x 0 + (2632249743/5000000000 : ℝ)*x 1 + (-2221654419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345095939/10000000000 : ℝ)^4179 ≤ (21808691520439/50000000000000 : ℝ)^3155 := by
    have hnat : (5345095939 : ℕ)^4179*50000000000000^3155 ≤ 21808691520439^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345095939 10000000000 21808691520439 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632249743/5000000000 : ℝ)^4179 ≤ (42748371820789/100000000000000 : ℝ)^3155 := by
    have hnat : (2632249743 : ℕ)^4179*100000000000000^3155 ≤ 42748371820789^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632249743 5000000000 42748371820789 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2221654419/10000000000 : ℝ)^4179 ≤ (6817122563953/50000000000000 : ℝ)^3155 := by
    have hnat : (2221654419 : ℕ)^4179*50000000000000^3155 ≤ 6817122563953^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221654419 10000000000 6817122563953 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345095939/10000000000 : ℝ), (2632249743/5000000000 : ℝ), (-2221654419/10000000000 : ℝ)] ![(21808691520439/50000000000000 : ℝ), (42748371820789/100000000000000 : ℝ), (6817122563953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345095939/10000000000 : ℝ)|^4179 ≤ (21808691520439/50000000000000 : ℝ)^3155
        have hw : |(5345095939/10000000000 : ℝ)|=(5345095939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632249743/5000000000 : ℝ)|^4179 ≤ (42748371820789/100000000000000 : ℝ)^3155
        have hw : |(2632249743/5000000000 : ℝ)|=(2632249743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2221654419/10000000000 : ℝ)|^4179 ≤ (6817122563953/50000000000000 : ℝ)^3155
        have hw : |(-2221654419/10000000000 : ℝ)|=(2221654419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s5_3 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4361357937/10000000000 : ℝ)*x 0 + (846710297/2000000000 : ℝ)*x 1 + (898596643/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361357937/10000000000 : ℝ)^4179 ≤ (33316230021873/100000000000000 : ℝ)^3155 := by
    have hnat : (4361357937 : ℕ)^4179*100000000000000^3155 ≤ 33316230021873^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361357937 10000000000 33316230021873 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846710297/2000000000 : ℝ)^4179 ≤ (16014619073461/50000000000000 : ℝ)^3155 := by
    have hnat : (846710297 : ℕ)^4179*50000000000000^3155 ≤ 16014619073461^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846710297 2000000000 16014619073461 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898596643/2000000000 : ℝ)^4179 ≤ (8663632953203/25000000000000 : ℝ)^3155 := by
    have hnat : (898596643 : ℕ)^4179*25000000000000^3155 ≤ 8663632953203^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898596643 2000000000 8663632953203 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361357937/10000000000 : ℝ), (846710297/2000000000 : ℝ), (898596643/2000000000 : ℝ)] ![(33316230021873/100000000000000 : ℝ), (16014619073461/50000000000000 : ℝ), (8663632953203/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361357937/10000000000 : ℝ)|^4179 ≤ (33316230021873/100000000000000 : ℝ)^3155
        have hw : |(4361357937/10000000000 : ℝ)|=(4361357937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846710297/2000000000 : ℝ)|^4179 ≤ (16014619073461/50000000000000 : ℝ)^3155
        have hw : |(846710297/2000000000 : ℝ)|=(846710297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898596643/2000000000 : ℝ)|^4179 ≤ (8663632953203/25000000000000 : ℝ)^3155
        have hw : |(898596643/2000000000 : ℝ)|=(898596643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s5_4 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-269474509/1250000000 : ℝ)*x 0 + (526483447/1000000000 : ℝ)*x 1 + (5393979519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269474509/1250000000 : ℝ)^4179 ≤ (818842947603/6250000000000 : ℝ)^3155 := by
    have hnat : (269474509 : ℕ)^4179*6250000000000^3155 ≤ 818842947603^3155*1250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269474509 1250000000 818842947603 6250000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526483447/1000000000 : ℝ)^4179 ≤ (21375987409501/50000000000000 : ℝ)^3155 := by
    have hnat : (526483447 : ℕ)^4179*50000000000000^3155 ≤ 21375987409501^3155*1000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526483447 1000000000 21375987409501 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393979519/10000000000 : ℝ)^4179 ≤ (689789656289/1562500000000 : ℝ)^3155 := by
    have hnat : (5393979519 : ℕ)^4179*1562500000000^3155 ≤ 689789656289^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393979519 10000000000 689789656289 1562500000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-269474509/1250000000 : ℝ), (526483447/1000000000 : ℝ), (5393979519/10000000000 : ℝ)] ![(818842947603/6250000000000 : ℝ), (21375987409501/50000000000000 : ℝ), (689789656289/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-269474509/1250000000 : ℝ)|^4179 ≤ (818842947603/6250000000000 : ℝ)^3155
        have hw : |(-269474509/1250000000 : ℝ)|=(269474509/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526483447/1000000000 : ℝ)|^4179 ≤ (21375987409501/50000000000000 : ℝ)^3155
        have hw : |(526483447/1000000000 : ℝ)|=(526483447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393979519/10000000000 : ℝ)|^4179 ≤ (689789656289/1562500000000 : ℝ)^3155
        have hw : |(5393979519/10000000000 : ℝ)|=(5393979519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s5_5 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531215153/1000000000 : ℝ)*x 0 + (-83686953/400000000 : ℝ)*x 1 + (5393979737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531215153/1000000000 : ℝ)^4179 ≤ (4326165048283/10000000000000 : ℝ)^3155 := by
    have hnat : (531215153 : ℕ)^4179*10000000000000^3155 ≤ 4326165048283^3155*1000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531215153 1000000000 4326165048283 10000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83686953/400000000 : ℝ)^4179 ≤ (12591809140411/100000000000000 : ℝ)^3155 := by
    have hnat : (83686953 : ℕ)^4179*100000000000000^3155 ≤ 12591809140411^3155*400000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83686953 400000000 12591809140411 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393979737/10000000000 : ℝ)^4179 ≤ (8829308073157/20000000000000 : ℝ)^3155 := by
    have hnat : (5393979737 : ℕ)^4179*20000000000000^3155 ≤ 8829308073157^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393979737 10000000000 8829308073157 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531215153/1000000000 : ℝ), (-83686953/400000000 : ℝ), (5393979737/10000000000 : ℝ)] ![(4326165048283/10000000000000 : ℝ), (12591809140411/100000000000000 : ℝ), (8829308073157/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531215153/1000000000 : ℝ)|^4179 ≤ (4326165048283/10000000000000 : ℝ)^3155
        have hw : |(531215153/1000000000 : ℝ)|=(531215153/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-83686953/400000000 : ℝ)|^4179 ≤ (12591809140411/100000000000000 : ℝ)^3155
        have hw : |(-83686953/400000000 : ℝ)|=(83686953/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393979737/10000000000 : ℝ)|^4179 ≤ (8829308073157/20000000000000 : ℝ)^3155
        have hw : |(5393979737/10000000000 : ℝ)|=(5393979737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s5_6 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664018921/1250000000 : ℝ)*x 0 + (2696989887/5000000000 : ℝ)*x 1 + (-2092173993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664018921/1250000000 : ℝ)^4179 ≤ (10815412183829/25000000000000 : ℝ)^3155 := by
    have hnat : (664018921 : ℕ)^4179*25000000000000^3155 ≤ 10815412183829^3155*1250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664018921 1250000000 10815412183829 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696989887/5000000000 : ℝ)^4179 ≤ (22073270383447/50000000000000 : ℝ)^3155 := by
    have hnat : (2696989887 : ℕ)^4179*50000000000000^3155 ≤ 22073270383447^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696989887 5000000000 22073270383447 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2092173993/10000000000 : ℝ)^4179 ≤ (2518362095939/20000000000000 : ℝ)^3155 := by
    have hnat : (2092173993 : ℕ)^4179*20000000000000^3155 ≤ 2518362095939^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092173993 10000000000 2518362095939 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664018921/1250000000 : ℝ), (2696989887/5000000000 : ℝ), (-2092173993/10000000000 : ℝ)] ![(10815412183829/25000000000000 : ℝ), (22073270383447/50000000000000 : ℝ), (2518362095939/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664018921/1250000000 : ℝ)|^4179 ≤ (10815412183829/25000000000000 : ℝ)^3155
        have hw : |(664018921/1250000000 : ℝ)|=(664018921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696989887/5000000000 : ℝ)|^4179 ≤ (22073270383447/50000000000000 : ℝ)^3155
        have hw : |(2696989887/5000000000 : ℝ)|=(2696989887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2092173993/10000000000 : ℝ)|^4179 ≤ (2518362095939/20000000000000 : ℝ)^3155
        have hw : |(-2092173993/10000000000 : ℝ)|=(2092173993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s5_7 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (872273761/2000000000 : ℝ)*x 0 + (175481/390625 : ℝ)*x 1 + (846844629/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872273761/2000000000 : ℝ)^4179 ≤ (6663267997499/20000000000000 : ℝ)^3155 := by
    have hnat : (872273761 : ℕ)^4179*20000000000000^3155 ≤ 6663267997499^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872273761 2000000000 6663267997499 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (175481/390625 : ℝ)^4179 ≤ (6929538183587/20000000000000 : ℝ)^3155 := by
    have hnat : (175481 : ℕ)^4179*20000000000000^3155 ≤ 6929538183587^3155*390625^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175481 390625 6929538183587 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846844629/2000000000 : ℝ)^4179 ≤ (1601798454127/5000000000000 : ℝ)^3155 := by
    have hnat : (846844629 : ℕ)^4179*5000000000000^3155 ≤ 1601798454127^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846844629 2000000000 1601798454127 5000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872273761/2000000000 : ℝ), (175481/390625 : ℝ), (846844629/2000000000 : ℝ)] ![(6663267997499/20000000000000 : ℝ), (6929538183587/20000000000000 : ℝ), (1601798454127/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872273761/2000000000 : ℝ)|^4179 ≤ (6663267997499/20000000000000 : ℝ)^3155
        have hw : |(872273761/2000000000 : ℝ)|=(872273761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(175481/390625 : ℝ)|^4179 ≤ (6929538183587/20000000000000 : ℝ)^3155
        have hw : |(175481/390625 : ℝ)|=(175481/390625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(846844629/2000000000 : ℝ)|^4179 ≤ (1601798454127/5000000000000 : ℝ)^3155
        have hw : |(846844629/2000000000 : ℝ)|=(846844629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1165_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11349/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7049/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5609/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5609/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5609/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5609/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5609/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5609/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (5609/50000 : ℝ) ^ (8357/2048 : ℝ) ≤ (6638758157095281/50000000000000000000 : ℝ) := by
    have hpowers : (5609/50000 : ℝ)^8357 ≤ (6638758157095281/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5609 : ℕ)^8357*50000000000000000000^2048 ≤ 6638758157095281^2048*50000^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5609 50000 6638758157095281 50000000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5609/50000 : ℝ)) (X := (6638758157095281/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (8357/2048 : ℝ) ≤ (35082815699469851/100000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^8357 ≤ (35082815699469851/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7117 : ℕ)^8357*100000000000000000000^2048 ≤ 35082815699469851^2048*50000^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 35082815699469851 100000000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (35082815699469851/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006638758157095281/25000000000000000000 : ℝ) ≤ (10000650703079137/10000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (25006638758157095281/25000000000000000000 : ℝ)^2048 ≤ (10000650703079137/10000000000000000 : ℝ)^8357 := by
      have hnat : (25006638758157095281 : ℕ)^2048*10000000000000000^8357 ≤ 10000650703079137^8357*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006638758157095281 25000000000000000000 10000650703079137 10000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000650703079137/10000000000000000 : ℝ)) (X := (25006638758157095281/25000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048360332013660413/100000000000000000000 : ℝ) ≤ (10001184921448903/10000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (100048360332013660413/100000000000000000000 : ℝ)^2048 ≤ (10001184921448903/10000000000000000 : ℝ)^8357 := by
      have hnat : (100048360332013660413 : ℕ)^2048*10000000000000000^8357 ≤ 10001184921448903^8357*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048360332013660413 100000000000000000000 10001184921448903 10000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001184921448903/10000000000000000 : ℝ)) (X := (100048360332013660413/100000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035082815699469851/50000000000000000000 : ℝ) ≤ (10001719139818669/10000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (50035082815699469851/50000000000000000000 : ℝ)^2048 ≤ (10001719139818669/10000000000000000 : ℝ)^8357 := by
      have hnat : (50035082815699469851 : ℕ)^2048*10000000000000000^8357 ≤ 10001719139818669^8357*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035082815699469851 50000000000000000000 10001719139818669 10000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001719139818669/10000000000000000 : ℝ)) (X := (50035082815699469851/50000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6638758157095281/50000000000000000000 : ℝ) ≤ ((1884373549821412951/1885000000000000000 : ℝ)+2*(267109184883/150800000000000 : ℝ)*(5609/50000 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (1884373549821412951/1885000000000000000 : ℝ)+2*(267109184883/150800000000000 : ℝ)*(5609/50000 : ℝ)=(10000650703079137/10000000000000000 : ℝ) by norm_num, show 1+2*(6638758157095281/50000000000000000000 : ℝ)=(25006638758157095281/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35082815699469851/100000000000000000000 : ℝ)+(6638758157095281/50000000000000000000 : ℝ) ≤ ((1884373549821412951/1885000000000000000 : ℝ)+(267109184883/150800000000000 : ℝ)*((7117/50000 : ℝ)+(5609/50000 : ℝ)))^(8357/2048 : ℝ) := by
    rw [show (1884373549821412951/1885000000000000000 : ℝ)+(267109184883/150800000000000 : ℝ)*((7117/50000 : ℝ)+(5609/50000 : ℝ))=(10001184921448903/10000000000000000 : ℝ) by norm_num, show 1+(35082815699469851/100000000000000000000 : ℝ)+(6638758157095281/50000000000000000000 : ℝ)=(100048360332013660413/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35082815699469851/100000000000000000000 : ℝ) ≤ ((1884373549821412951/1885000000000000000 : ℝ)+2*(267109184883/150800000000000 : ℝ)*(7117/50000 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (1884373549821412951/1885000000000000000 : ℝ)+2*(267109184883/150800000000000 : ℝ)*(7117/50000 : ℝ)=(10001719139818669/10000000000000000 : ℝ) by norm_num, show 1+2*(35082815699469851/100000000000000000000 : ℝ)=(50035082815699469851/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1884373549821412951/1885000000000000000 : ℝ)*(X 1 0+X 2 0)+(267109184883/150800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (5609/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (1884373549821412951/1885000000000000000 : ℝ)) (alpha := (267109184883/150800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1884373549821412951/1885000000000000000 : ℝ)*(X 0 1+X 2 1)+(267109184883/150800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (5609/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (1884373549821412951/1885000000000000000 : ℝ)) (alpha := (267109184883/150800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1884373549821412951/1885000000000000000 : ℝ)*(X 0 2+X 1 2)+(267109184883/150800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (5609/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (1884373549821412951/1885000000000000000 : ℝ)) (alpha := (267109184883/150800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2155790351/10000000000 : ℝ)*X 0 0+(1078863171/2000000000 : ℝ)*X 0 1+(5264499753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345095937/10000000000 : ℝ)*X 1 0+(-1110827129/5000000000 : ℝ)*X 1 1+(5264499609/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345095939/10000000000 : ℝ)*X 2 0+(2632249743/5000000000 : ℝ)*X 2 1+(-2221654419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361357937/10000000000 : ℝ)*X 0 0+(846710297/2000000000 : ℝ)*X 0 1+(898596643/2000000000 : ℝ)*X 0 2+(4361357937/10000000000 : ℝ)*X 1 0+(846710297/2000000000 : ℝ)*X 1 1+(898596643/2000000000 : ℝ)*X 1 2+(4361357937/10000000000 : ℝ)*X 2 0+(846710297/2000000000 : ℝ)*X 2 1+(898596643/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-269474509/1250000000 : ℝ)*X 0 0+(526483447/1000000000 : ℝ)*X 0 1+(5393979519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531215153/1000000000 : ℝ)*X 1 0+(-83686953/400000000 : ℝ)*X 1 1+(5393979737/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664018921/1250000000 : ℝ)*X 2 0+(2696989887/5000000000 : ℝ)*X 2 1+(-2092173993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872273761/2000000000 : ℝ)*X 0 0+(175481/390625 : ℝ)*X 0 1+(846844629/2000000000 : ℝ)*X 0 2+(872273761/2000000000 : ℝ)*X 1 0+(175481/390625 : ℝ)*X 1 1+(846844629/2000000000 : ℝ)*X 1 2+(872273761/2000000000 : ℝ)*X 2 0+(175481/390625 : ℝ)*X 2 1+(846844629/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (865782833857957177612281/453125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55300747/25000000000000 : ℝ)*(base8) + (111574271/50000000000000 : ℝ)*(base21) + (1316577/12500000000000 : ℝ)*(base29) + (35724983/50000000000000 : ℝ)*(lower2) + (188449/12500000000000 : ℝ)*(lower4) + (577888996986127/10000000000000 : ℝ)*(major0) + (2889444990196943/50000000000000 : ℝ)*(major1) + (2889444990196943/50000000000000 : ℝ)*(major2) + (962899879580427/12500000000000 : ℝ)*(sp0) + (1925799811828447/25000000000000 : ℝ)*(sp1) + (7703188257073903/100000000000000 : ℝ)*(sp2) + (1927289186015421/50000000000000 : ℝ)*(sp3) + (10767091343/100000000000000 : ℝ)*(sp6) + (226722053/10000000000000 : ℝ)*(sp7) + (963645159812843/25000000000000 : ℝ)*(f.failure) + (1925799814461601/25000000000000 : ℝ)*(f.sum) + (4328609760404091/3770000000000000000000000000 : ℝ)*base66 + (585929858783328707/94250000000000000000000000000000 : ℝ)*base68 + (1358599942884828707/94250000000000000000000000000000 : ℝ)*base70 + (14650527499320803277/18850000000000000000000000000000 : ℝ)*base71 + (2097544522867/3770000000000000000000000000 : ℝ)*base73 + (602553404856378707/94250000000000000000000000000000 : ℝ)*base76 + (5081443607573553277/18850000000000000000000000000000 : ℝ)*base77 + (876556525487121293/94250000000000000000000000000000 : ℝ)*base79 + (21514398491793/3770000000000000000000000000 : ℝ)*base82 + (1746719/312500000000000000000 : ℝ)*base89 + (1746719/312500000000000000000 : ℝ)*base91 + (1746719/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23045931740805064336467/7540000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1259563479/100000000000000 : ℝ)*(base19) + (1039394819/100000000000000 : ℝ)*(base23) + (173769467/100000000000000 : ℝ)*(upper3) + (36940463/100000000000000 : ℝ)*(lower4) + (139535561/100000000000000 : ℝ)*(upper5) + (5808917610693477/100000000000000 : ℝ)*(major0) + (5808917610693477/100000000000000 : ℝ)*(major1) + (5808917610693477/100000000000000 : ℝ)*(major2) + (5552882441/12500000000000 : ℝ)*(sp1) + (7156990059/20000000000000 : ℝ)*(sp2) + (7743225733765269/100000000000000 : ℝ)*(sp4) + (3871590025571131/50000000000000 : ℝ)*(sp5) + (1548637781884031/20000000000000 : ℝ)*(sp6) + (60540771652167/1562500000000 : ℝ)*(sp7) + (60540771652167/1562500000000 : ℝ)*(f.failure) + (7743225733765269/100000000000000 : ℝ)*(f.sum) + (23289517389311/7540000000000000000000000000 : ℝ)*base65 + (619591525096408127/188500000000000000000000000000000 : ℝ)*base67 + (3398527281482091873/188500000000000000000000000000000 : ℝ)*base70 + (1121576976765408127/188500000000000000000000000000000 : ℝ)*base71 + (42685489136151/7540000000000000000000000000 : ℝ)*base73 + (5836311832079591873/188500000000000000000000000000000 : ℝ)*base76 + (1868324354628908127/188500000000000000000000000000000 : ℝ)*base77 + (2694421491438591873/188500000000000000000000000000000 : ℝ)*base80 + (29669910241409/7540000000000000000000000000 : ℝ)*base82 + (50097/39062500000000000000 : ℝ)*base89 + (50097/39062500000000000000 : ℝ)*base91 + (50097/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1165_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1165_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1165_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3287/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1165_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1165_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1165_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3287/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1165_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

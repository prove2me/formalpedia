-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1514_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:55:47.059521+00:00
-- url     : https://prove2.me/submissions/2feda5df-c425-48c3-924e-9f0c419d4c2a

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
theorem support_rectangle_w1514_s0_0 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-841857459/5000000000 : ℝ)*x 0 + (5911290163/10000000000 : ℝ)*x 1 + (2428085863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (841857459/5000000000 : ℝ)^4525 ≤ (9999113687107/100000000000000 : ℝ)^3501 := by
    have hnat : (841857459 : ℕ)^4525*100000000000000^3501 ≤ 9999113687107^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841857459 5000000000 9999113687107 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5911290163/10000000000 : ℝ)^4525 ≤ (50687645199663/100000000000000 : ℝ)^3501 := by
    have hnat : (5911290163 : ℕ)^4525*100000000000000^3501 ≤ 50687645199663^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5911290163 10000000000 50687645199663 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2428085863/5000000000 : ℝ)^4525 ≤ (19656620548483/50000000000000 : ℝ)^3501 := by
    have hnat : (2428085863 : ℕ)^4525*50000000000000^3501 ≤ 19656620548483^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2428085863 5000000000 19656620548483 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-841857459/5000000000 : ℝ), (5911290163/10000000000 : ℝ), (2428085863/5000000000 : ℝ)] ![(9999113687107/100000000000000 : ℝ), (50687645199663/100000000000000 : ℝ), (19656620548483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-841857459/5000000000 : ℝ)|^4525 ≤ (9999113687107/100000000000000 : ℝ)^3501
        have hw : |(-841857459/5000000000 : ℝ)|=(841857459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5911290163/10000000000 : ℝ)|^4525 ≤ (50687645199663/100000000000000 : ℝ)^3501
        have hw : |(5911290163/10000000000 : ℝ)|=(5911290163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2428085863/5000000000 : ℝ)|^4525 ≤ (19656620548483/50000000000000 : ℝ)^3501
        have hw : |(2428085863/5000000000 : ℝ)|=(2428085863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s0_1 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2738772509/5000000000 : ℝ)*x 0 + (-568744157/2500000000 : ℝ)*x 1 + (971234327/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2738772509/5000000000 : ℝ)^4525 ≤ (45933075067173/100000000000000 : ℝ)^3501 := by
    have hnat : (2738772509 : ℕ)^4525*100000000000000^3501 ≤ 45933075067173^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738772509 5000000000 45933075067173 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (568744157/2500000000 : ℝ)^4525 ≤ (7376842383821/50000000000000 : ℝ)^3501 := by
    have hnat : (568744157 : ℕ)^4525*50000000000000^3501 ≤ 7376842383821^3501*2500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568744157 2500000000 7376842383821 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (971234327/2000000000 : ℝ)^4525 ≤ (49141550181/125000000000 : ℝ)^3501 := by
    have hnat : (971234327 : ℕ)^4525*125000000000^3501 ≤ 49141550181^3501*2000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971234327 2000000000 49141550181 125000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2738772509/5000000000 : ℝ), (-568744157/2500000000 : ℝ), (971234327/2000000000 : ℝ)] ![(45933075067173/100000000000000 : ℝ), (7376842383821/50000000000000 : ℝ), (49141550181/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2738772509/5000000000 : ℝ)|^4525 ≤ (45933075067173/100000000000000 : ℝ)^3501
        have hw : |(2738772509/5000000000 : ℝ)|=(2738772509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-568744157/2500000000 : ℝ)|^4525 ≤ (7376842383821/50000000000000 : ℝ)^3501
        have hw : |(-568744157/2500000000 : ℝ)|=(568744157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(971234327/2000000000 : ℝ)|^4525 ≤ (49141550181/125000000000 : ℝ)^3501
        have hw : |(971234327/2000000000 : ℝ)|=(971234327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s0_2 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (684693137/1250000000 : ℝ)*x 0 + (1214042917/2500000000 : ℝ)*x 1 + (-1137488243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (684693137/1250000000 : ℝ)^4525 ≤ (45933075912569/100000000000000 : ℝ)^3501 := by
    have hnat : (684693137 : ℕ)^4525*100000000000000^3501 ≤ 45933075912569^3501*1250000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684693137 1250000000 45933075912569 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1214042917/2500000000 : ℝ)^4525 ≤ (39313240490091/100000000000000 : ℝ)^3501 := by
    have hnat : (1214042917 : ℕ)^4525*100000000000000^3501 ≤ 39313240490091^3501*2500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1214042917 2500000000 39313240490091 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1137488243/5000000000 : ℝ)^4525 ≤ (922105223587/6250000000000 : ℝ)^3501 := by
    have hnat : (1137488243 : ℕ)^4525*6250000000000^3501 ≤ 922105223587^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137488243 5000000000 922105223587 6250000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(684693137/1250000000 : ℝ), (1214042917/2500000000 : ℝ), (-1137488243/5000000000 : ℝ)] ![(45933075912569/100000000000000 : ℝ), (39313240490091/100000000000000 : ℝ), (922105223587/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(684693137/1250000000 : ℝ)|^4525 ≤ (45933075912569/100000000000000 : ℝ)^3501
        have hw : |(684693137/1250000000 : ℝ)|=(684693137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1214042917/2500000000 : ℝ)|^4525 ≤ (39313240490091/100000000000000 : ℝ)^3501
        have hw : |(1214042917/2500000000 : ℝ)|=(1214042917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1137488243/5000000000 : ℝ)|^4525 ≤ (922105223587/6250000000000 : ℝ)^3501
        have hw : |(-1137488243/5000000000 : ℝ)|=(1137488243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s0_3 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2072302459/5000000000 : ℝ)*x 0 + (3091287477/10000000000 : ℝ)*x 1 + (219489241/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2072302459/5000000000 : ℝ)^4525 ≤ (32033293977651/100000000000000 : ℝ)^3501 := by
    have hnat : (2072302459 : ℕ)^4525*100000000000000^3501 ≤ 32033293977651^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072302459 5000000000 32033293977651 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091287477/10000000000 : ℝ)^4525 ≤ (21928622781363/100000000000000 : ℝ)^3501 := by
    have hnat : (3091287477 : ℕ)^4525*100000000000000^3501 ≤ 21928622781363^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091287477 10000000000 21928622781363 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219489241/400000000 : ℝ)^4525 ≤ (9207616646279/20000000000000 : ℝ)^3501 := by
    have hnat : (219489241 : ℕ)^4525*20000000000000^3501 ≤ 9207616646279^3501*400000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219489241 400000000 9207616646279 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2072302459/5000000000 : ℝ), (3091287477/10000000000 : ℝ), (219489241/400000000 : ℝ)] ![(32033293977651/100000000000000 : ℝ), (21928622781363/100000000000000 : ℝ), (9207616646279/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2072302459/5000000000 : ℝ)|^4525 ≤ (32033293977651/100000000000000 : ℝ)^3501
        have hw : |(2072302459/5000000000 : ℝ)|=(2072302459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091287477/10000000000 : ℝ)|^4525 ≤ (21928622781363/100000000000000 : ℝ)^3501
        have hw : |(3091287477/10000000000 : ℝ)|=(3091287477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219489241/400000000 : ℝ)|^4525 ≤ (9207616646279/20000000000000 : ℝ)^3501
        have hw : |(219489241/400000000 : ℝ)|=(219489241/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s0_4 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-67488729/400000000 : ℝ)*x 0 + (30519217/62500000 : ℝ)*x 1 + (2941711889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67488729/400000000 : ℝ)^4525 ≤ (2506503071867/25000000000000 : ℝ)^3501 := by
    have hnat : (67488729 : ℕ)^4525*25000000000000^3501 ≤ 2506503071867^3501*400000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67488729 400000000 2506503071867 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30519217/62500000 : ℝ)^4525 ≤ (39594964651723/100000000000000 : ℝ)^3501 := by
    have hnat : (30519217 : ℕ)^4525*100000000000000^3501 ≤ 39594964651723^3501*62500000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30519217 62500000 39594964651723 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2941711889/5000000000 : ℝ)^4525 ≤ (39358611753/78125000000 : ℝ)^3501 := by
    have hnat : (2941711889 : ℕ)^4525*78125000000^3501 ≤ 39358611753^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2941711889 5000000000 39358611753 78125000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67488729/400000000 : ℝ), (30519217/62500000 : ℝ), (2941711889/5000000000 : ℝ)] ![(2506503071867/25000000000000 : ℝ), (39594964651723/100000000000000 : ℝ), (39358611753/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67488729/400000000 : ℝ)|^4525 ≤ (2506503071867/25000000000000 : ℝ)^3501
        have hw : |(-67488729/400000000 : ℝ)|=(67488729/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(30519217/62500000 : ℝ)|^4525 ≤ (39594964651723/100000000000000 : ℝ)^3501
        have hw : |(30519217/62500000 : ℝ)|=(30519217/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2941711889/5000000000 : ℝ)|^4525 ≤ (39358611753/78125000000 : ℝ)^3501
        have hw : |(2941711889/5000000000 : ℝ)|=(2941711889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s0_5 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5189265719/10000000000 : ℝ)*x 0 + (-311931131/2500000000 : ℝ)*x 1 + (5883423823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5189265719/10000000000 : ℝ)^4525 ≤ (10708234054629/25000000000000 : ℝ)^3501 := by
    have hnat : (5189265719 : ℕ)^4525*25000000000000^3501 ≤ 10708234054629^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5189265719 10000000000 10708234054629 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (311931131/2500000000 : ℝ)^4525 ≤ (3314472763/48828125000 : ℝ)^3501 := by
    have hnat : (311931131 : ℕ)^4525*48828125000^3501 ≤ 3314472763^3501*2500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311931131 2500000000 3314472763 48828125000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5883423823/10000000000 : ℝ)^4525 ≤ (50379023541873/100000000000000 : ℝ)^3501 := by
    have hnat : (5883423823 : ℕ)^4525*100000000000000^3501 ≤ 50379023541873^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5883423823 10000000000 50379023541873 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5189265719/10000000000 : ℝ), (-311931131/2500000000 : ℝ), (5883423823/10000000000 : ℝ)] ![(10708234054629/25000000000000 : ℝ), (3314472763/48828125000 : ℝ), (50379023541873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5189265719/10000000000 : ℝ)|^4525 ≤ (10708234054629/25000000000000 : ℝ)^3501
        have hw : |(5189265719/10000000000 : ℝ)|=(5189265719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-311931131/2500000000 : ℝ)|^4525 ≤ (3314472763/48828125000 : ℝ)^3501
        have hw : |(-311931131/2500000000 : ℝ)|=(311931131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5883423823/10000000000 : ℝ)|^4525 ≤ (50379023541873/100000000000000 : ℝ)^3501
        have hw : |(5883423823/10000000000 : ℝ)|=(5883423823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s0_6 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (518926569/1000000000 : ℝ)*x 0 + (5883423911/10000000000 : ℝ)*x 1 + (-124772443/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518926569/1000000000 : ℝ)^4525 ≤ (42832935909133/100000000000000 : ℝ)^3501 := by
    have hnat : (518926569 : ℕ)^4525*100000000000000^3501 ≤ 42832935909133^3501*1000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518926569 1000000000 42832935909133 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5883423911/10000000000 : ℝ)^4525 ≤ (25189512257903/50000000000000 : ℝ)^3501 := by
    have hnat : (5883423911 : ℕ)^4525*50000000000000^3501 ≤ 25189512257903^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5883423911 10000000000 25189512257903 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (124772443/1000000000 : ℝ)^4525 ≤ (6788039557657/100000000000000 : ℝ)^3501 := by
    have hnat : (124772443 : ℕ)^4525*100000000000000^3501 ≤ 6788039557657^3501*1000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124772443 1000000000 6788039557657 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518926569/1000000000 : ℝ), (5883423911/10000000000 : ℝ), (-124772443/1000000000 : ℝ)] ![(42832935909133/100000000000000 : ℝ), (25189512257903/50000000000000 : ℝ), (6788039557657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518926569/1000000000 : ℝ)|^4525 ≤ (42832935909133/100000000000000 : ℝ)^3501
        have hw : |(518926569/1000000000 : ℝ)|=(518926569/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5883423911/10000000000 : ℝ)|^4525 ≤ (25189512257903/50000000000000 : ℝ)^3501
        have hw : |(5883423911/10000000000 : ℝ)|=(5883423911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-124772443/1000000000 : ℝ)|^4525 ≤ (6788039557657/100000000000000 : ℝ)^3501
        have hw : |(-124772443/1000000000 : ℝ)|=(124772443/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s0_7 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4152560109/10000000000 : ℝ)*x 0 + (1356535023/2500000000 : ℝ)*x 1 + (1577283073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4152560109/10000000000 : ℝ)^4525 ≤ (32112784871499/100000000000000 : ℝ)^3501 := by
    have hnat : (4152560109 : ℕ)^4525*100000000000000^3501 ≤ 32112784871499^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152560109 10000000000 32112784871499 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356535023/2500000000 : ℝ)^4525 ≤ (4537669316731/10000000000000 : ℝ)^3501 := by
    have hnat : (1356535023 : ℕ)^4525*10000000000000^3501 ≤ 4537669316731^3501*2500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356535023 2500000000 4537669316731 10000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1577283073/5000000000 : ℝ)^4525 ≤ (22510521947673/100000000000000 : ℝ)^3501 := by
    have hnat : (1577283073 : ℕ)^4525*100000000000000^3501 ≤ 22510521947673^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577283073 5000000000 22510521947673 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4152560109/10000000000 : ℝ), (1356535023/2500000000 : ℝ), (1577283073/5000000000 : ℝ)] ![(32112784871499/100000000000000 : ℝ), (4537669316731/10000000000000 : ℝ), (22510521947673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4152560109/10000000000 : ℝ)|^4525 ≤ (32112784871499/100000000000000 : ℝ)^3501
        have hw : |(4152560109/10000000000 : ℝ)|=(4152560109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356535023/2500000000 : ℝ)|^4525 ≤ (4537669316731/10000000000000 : ℝ)^3501
        have hw : |(1356535023/2500000000 : ℝ)|=(1356535023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1577283073/5000000000 : ℝ)|^4525 ≤ (22510521947673/100000000000000 : ℝ)^3501
        have hw : |(1577283073/5000000000 : ℝ)|=(1577283073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1514_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2853/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12729/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4523/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4523 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4523*1^1024 ≤ 0^1024*1^4523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4523 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4523/1024 : ℝ) ≤ (1747036950610156051/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4523 ≤ (1747036950610156051/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4523*100000000000000000000^1024 ≤ 1747036950610156051^1024*5^4523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1747036950610156051 100000000000000000000 4523 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1747036950610156051/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4523 := by
      have hnat : (1 : ℕ)^1024*1^4523 ≤ 1^4523*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101747036950610156051/100000000000000000000 : ℝ) ≤ (1254911010874499/1250000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (101747036950610156051/100000000000000000000 : ℝ)^1024 ≤ (1254911010874499/1250000000000000 : ℝ)^4523 := by
      have hnat : (101747036950610156051 : ℕ)^1024*1250000000000000^4523 ≤ 1254911010874499^4523*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101747036950610156051 100000000000000000000 1254911010874499 1250000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1254911010874499/1250000000000000 : ℝ)) (X := (101747036950610156051/100000000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51747036950610156051/50000000000000000000 : ℝ) ≤ (629911010874499/625000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (51747036950610156051/50000000000000000000 : ℝ)^1024 ≤ (629911010874499/625000000000000 : ℝ)^4523 := by
      have hnat : (51747036950610156051 : ℕ)^1024*625000000000000^4523 ≤ 629911010874499^4523*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51747036950610156051 50000000000000000000 629911010874499 625000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (629911010874499/625000000000000 : ℝ)) (X := (51747036950610156051/50000000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(4911010874499/500000000000000 : ℝ)*(0 : ℝ))^(4523/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4911010874499/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1747036950610156051/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(4911010874499/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4523/1024 : ℝ) := by
    rw [show (1 : ℝ)+(4911010874499/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1254911010874499/1250000000000000 : ℝ) by norm_num, show 1+(1747036950610156051/100000000000000000000 : ℝ)+(0 : ℝ)=(101747036950610156051/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1747036950610156051/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(4911010874499/500000000000000 : ℝ)*(2/5 : ℝ))^(4523/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4911010874499/500000000000000 : ℝ)*(2/5 : ℝ)=(629911010874499/625000000000000 : ℝ) by norm_num, show 1+2*(1747036950610156051/100000000000000000000 : ℝ)=(51747036950610156051/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(4911010874499/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4911010874499/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(4911010874499/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4911010874499/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(4911010874499/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4911010874499/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-841857459/5000000000 : ℝ)*X 0 0+(5911290163/10000000000 : ℝ)*X 0 1+(2428085863/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2738772509/5000000000 : ℝ)*X 1 0+(-568744157/2500000000 : ℝ)*X 1 1+(971234327/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((684693137/1250000000 : ℝ)*X 2 0+(1214042917/2500000000 : ℝ)*X 2 1+(-1137488243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2072302459/5000000000 : ℝ)*X 0 0+(3091287477/10000000000 : ℝ)*X 0 1+(219489241/400000000 : ℝ)*X 0 2+(2072302459/5000000000 : ℝ)*X 1 0+(3091287477/10000000000 : ℝ)*X 1 1+(219489241/400000000 : ℝ)*X 1 2+(2072302459/5000000000 : ℝ)*X 2 0+(3091287477/10000000000 : ℝ)*X 2 1+(219489241/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-67488729/400000000 : ℝ)*X 0 0+(30519217/62500000 : ℝ)*X 0 1+(2941711889/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5189265719/10000000000 : ℝ)*X 1 0+(-311931131/2500000000 : ℝ)*X 1 1+(5883423823/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((518926569/1000000000 : ℝ)*X 2 0+(5883423911/10000000000 : ℝ)*X 2 1+(-124772443/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4152560109/10000000000 : ℝ)*X 0 0+(1356535023/2500000000 : ℝ)*X 0 1+(1577283073/5000000000 : ℝ)*X 0 2+(4152560109/10000000000 : ℝ)*X 1 0+(1356535023/2500000000 : ℝ)*X 1 1+(1577283073/5000000000 : ℝ)*X 1 2+(4152560109/10000000000 : ℝ)*X 2 0+(1356535023/2500000000 : ℝ)*X 2 1+(1577283073/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (74540815077886884518229/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (421463/1000000000000 : ℝ)*(base1) + (1389671329/100000000000000 : ℝ)*(base19) + (8769797/625000000000 : ℝ)*(base23) + (1973647/1250000000000 : ℝ)*(upper3) + (202222629/100000000000000 : ℝ)*(upper5) + (341286811476243/50000000000000 : ℝ)*(major0) + (341286811476243/50000000000000 : ℝ)*(major1) + (341286811476243/50000000000000 : ℝ)*(major2) + (947765447443113/100000000000000 : ℝ)*(sp0) + (947769153990889/100000000000000 : ℝ)*(sp1) + (947769140494699/100000000000000 : ℝ)*(sp2) + (417374284239217/100000000000000 : ℝ)*(sp3) + (1027673081/20000000000000 : ℝ)*(sp4) + (2177081723/100000000000000 : ℝ)*(sp7) + (417376503467239/100000000000000 : ℝ)*(f.failure) + (473885271831109/50000000000000 : ℝ)*(f.sum) + (3365953602257/12500000000000000000000000000 : ℝ)*base65 + (64819983072743/25000000000000000000000000000 : ℝ)*base68 + (102762590252257/25000000000000000000000000000 : ℝ)*base69 + (57264642652257/25000000000000000000000000000 : ℝ)*base71 + (21955178635243/12500000000000000000000000000 : ℝ)*base74 + (1847330577257/25000000000000000000000000000 : ℝ)*base75 + (59287984897743/25000000000000000000000000000 : ℝ)*base78 + (68093205897743/25000000000000000000000000000 : ℝ)*base80 + (46201977164757/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (82742943/10000000000000000000000 : ℝ)*base90 + (82742943/10000000000000000000000 : ℝ)*base92 + (82742943/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18276102871491051696351/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (416412253/50000000000000 : ℝ)*(base19) + (836252173/100000000000000 : ℝ)*(base23) + (5364017/25000000000000 : ℝ)*(base32) + (15575343/12500000000000 : ℝ)*(upper3) + (2560719/2500000000000 : ℝ)*(upper5) + (719937210233617/100000000000000 : ℝ)*(major0) + (719937210233617/100000000000000 : ℝ)*(major1) + (719937210233617/100000000000000 : ℝ)*(major2) + (1084126371/50000000000000 : ℝ)*(sp1) + (116525719/5000000000000 : ℝ)*(sp2) + (999650906718263/100000000000000 : ℝ)*(sp4) + (499823952820507/50000000000000 : ℝ)*(sp5) + (99964773995171/10000000000000 : ℝ)*(sp6) + (44022337045221/10000000000000 : ℝ)*(sp7) + (440223391908279/100000000000000 : ℝ)*(f.failure) + (999650906718263/100000000000000 : ℝ)*(f.sum) + (59261564957883/25000000000000000000000000000 : ℝ)*base65 + (412404523832883/50000000000000000000000000000 : ℝ)*base67 + (77061755867117/50000000000000000000000000000 : ℝ)*base70 + (170113792232883/50000000000000000000000000000 : ℝ)*base71 + (213433707632883/25000000000000000000000000000 : ℝ)*base73 + (293748640232883/50000000000000000000000000000 : ℝ)*base75 + (224675194332883/50000000000000000000000000000 : ℝ)*base77 + (92188909332883/50000000000000000000000000000 : ℝ)*base79 + (65716790832883/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (29602577/10000000000000000000000 : ℝ)*base89 + (29602577/10000000000000000000000 : ℝ)*base91 + (29602577/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1514_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2853/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12729/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1514_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1514_s1_0 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1836892983/10000000000 : ℝ)*x 0 + (5569181661/10000000000 : ℝ)*x 1 + (509982103/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1836892983/10000000000 : ℝ)^4525 ≤ (279754657107/2500000000000 : ℝ)^3501 := by
    have hnat : (1836892983 : ℕ)^4525*2500000000000^3501 ≤ 279754657107^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1836892983 10000000000 279754657107 2500000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5569181661/10000000000 : ℝ)^4525 ≤ (1877147682299/4000000000000 : ℝ)^3501 := by
    have hnat : (5569181661 : ℕ)^4525*4000000000000^3501 ≤ 1877147682299^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5569181661 10000000000 1877147682299 4000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (509982103/1000000000 : ℝ)^4525 ≤ (10470280410259/25000000000000 : ℝ)^3501 := by
    have hnat : (509982103 : ℕ)^4525*25000000000000^3501 ≤ 10470280410259^3501*1000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509982103 1000000000 10470280410259 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1836892983/10000000000 : ℝ), (5569181661/10000000000 : ℝ), (509982103/1000000000 : ℝ)] ![(279754657107/2500000000000 : ℝ), (1877147682299/4000000000000 : ℝ), (10470280410259/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1836892983/10000000000 : ℝ)|^4525 ≤ (279754657107/2500000000000 : ℝ)^3501
        have hw : |(-1836892983/10000000000 : ℝ)|=(1836892983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5569181661/10000000000 : ℝ)|^4525 ≤ (1877147682299/4000000000000 : ℝ)^3501
        have hw : |(5569181661/10000000000 : ℝ)|=(5569181661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(509982103/1000000000 : ℝ)|^4525 ≤ (10470280410259/25000000000000 : ℝ)^3501
        have hw : |(509982103/1000000000 : ℝ)|=(509982103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s1_1 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5260017/9765625 : ℝ)*x 0 + (-2083979877/10000000000 : ℝ)*x 1 + (1274955127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260017/9765625 : ℝ)^4525 ≤ (898921649661/2000000000000 : ℝ)^3501 := by
    have hnat : (5260017 : ℕ)^4525*2000000000000^3501 ≤ 898921649661^3501*9765625^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260017 9765625 898921649661 2000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2083979877/10000000000 : ℝ)^4525 ≤ (2634560279939/20000000000000 : ℝ)^3501 := by
    have hnat : (2083979877 : ℕ)^4525*20000000000000^3501 ≤ 2634560279939^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083979877 10000000000 2634560279939 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1274955127/2500000000 : ℝ)^4525 ≤ (41881116100391/100000000000000 : ℝ)^3501 := by
    have hnat : (1274955127 : ℕ)^4525*100000000000000^3501 ≤ 41881116100391^3501*2500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274955127 2500000000 41881116100391 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260017/9765625 : ℝ), (-2083979877/10000000000 : ℝ), (1274955127/2500000000 : ℝ)] ![(898921649661/2000000000000 : ℝ), (2634560279939/20000000000000 : ℝ), (41881116100391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260017/9765625 : ℝ)|^4525 ≤ (898921649661/2000000000000 : ℝ)^3501
        have hw : |(5260017/9765625 : ℝ)|=(5260017/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2083979877/10000000000 : ℝ)|^4525 ≤ (2634560279939/20000000000000 : ℝ)^3501
        have hw : |(-2083979877/10000000000 : ℝ)|=(2083979877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1274955127/2500000000 : ℝ)|^4525 ≤ (41881116100391/100000000000000 : ℝ)^3501
        have hw : |(1274955127/2500000000 : ℝ)|=(1274955127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s1_2 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336641069/625000000 : ℝ)*x 0 + (2549910427/5000000000 : ℝ)*x 1 + (-208397983/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336641069/625000000 : ℝ)^4525 ≤ (22473039602163/50000000000000 : ℝ)^3501 := by
    have hnat : (336641069 : ℕ)^4525*50000000000000^3501 ≤ 22473039602163^3501*625000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336641069 625000000 22473039602163 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2549910427/5000000000 : ℝ)^4525 ≤ (20940559886463/50000000000000 : ℝ)^3501 := by
    have hnat : (2549910427 : ℕ)^4525*50000000000000^3501 ≤ 20940559886463^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2549910427 5000000000 20940559886463 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208397983/1000000000 : ℝ)^4525 ≤ (2634560203143/20000000000000 : ℝ)^3501 := by
    have hnat : (208397983 : ℕ)^4525*20000000000000^3501 ≤ 2634560203143^3501*1000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208397983 1000000000 2634560203143 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336641069/625000000 : ℝ), (2549910427/5000000000 : ℝ), (-208397983/1000000000 : ℝ)] ![(22473039602163/50000000000000 : ℝ), (20940559886463/50000000000000 : ℝ), (2634560203143/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336641069/625000000 : ℝ)|^4525 ≤ (22473039602163/50000000000000 : ℝ)^3501
        have hw : |(336641069/625000000 : ℝ)|=(336641069/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2549910427/5000000000 : ℝ)|^4525 ≤ (20940559886463/50000000000000 : ℝ)^3501
        have hw : |(2549910427/5000000000 : ℝ)|=(2549910427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-208397983/1000000000 : ℝ)|^4525 ≤ (2634560203143/20000000000000 : ℝ)^3501
        have hw : |(-208397983/1000000000 : ℝ)|=(208397983/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s1_3 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2124441293/5000000000 : ℝ)*x 0 + (149765909/400000000 : ℝ)*x 1 + (4809963739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124441293/5000000000 : ℝ)^4525 ≤ (16539394465819/50000000000000 : ℝ)^3501 := by
    have hnat : (2124441293 : ℕ)^4525*50000000000000^3501 ≤ 16539394465819^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124441293 5000000000 16539394465819 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149765909/400000000 : ℝ)^4525 ≤ (2809078656719/10000000000000 : ℝ)^3501 := by
    have hnat : (149765909 : ℕ)^4525*10000000000000^3501 ≤ 2809078656719^3501*400000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149765909 400000000 2809078656719 10000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4809963739/10000000000 : ℝ)^4525 ≤ (19415212241463/50000000000000 : ℝ)^3501 := by
    have hnat : (4809963739 : ℕ)^4525*50000000000000^3501 ≤ 19415212241463^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4809963739 10000000000 19415212241463 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2124441293/5000000000 : ℝ), (149765909/400000000 : ℝ), (4809963739/10000000000 : ℝ)] ![(16539394465819/50000000000000 : ℝ), (2809078656719/10000000000000 : ℝ), (19415212241463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2124441293/5000000000 : ℝ)|^4525 ≤ (16539394465819/50000000000000 : ℝ)^3501
        have hw : |(2124441293/5000000000 : ℝ)|=(2124441293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(149765909/400000000 : ℝ)|^4525 ≤ (2809078656719/10000000000000 : ℝ)^3501
        have hw : |(149765909/400000000 : ℝ)|=(149765909/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4809963739/10000000000 : ℝ)|^4525 ≤ (19415212241463/50000000000000 : ℝ)^3501
        have hw : |(4809963739/10000000000 : ℝ)|=(4809963739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s1_4 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1837191151/10000000000 : ℝ)*x 0 + (5105055211/10000000000 : ℝ)*x 1 + (222554539/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1837191151/10000000000 : ℝ)^4525 ≤ (11192534031177/100000000000000 : ℝ)^3501 := by
    have hnat : (1837191151 : ℕ)^4525*100000000000000^3501 ≤ 11192534031177^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1837191151 10000000000 11192534031177 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5105055211/10000000000 : ℝ)^4525 ≤ (8387337390261/20000000000000 : ℝ)^3501 := by
    have hnat : (5105055211 : ℕ)^4525*20000000000000^3501 ≤ 8387337390261^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5105055211 10000000000 8387337390261 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222554539/400000000 : ℝ)^4525 ≤ (46870779013483/100000000000000 : ℝ)^3501 := by
    have hnat : (222554539 : ℕ)^4525*100000000000000^3501 ≤ 46870779013483^3501*400000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222554539 400000000 46870779013483 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1837191151/10000000000 : ℝ), (5105055211/10000000000 : ℝ), (222554539/400000000 : ℝ)] ![(11192534031177/100000000000000 : ℝ), (8387337390261/20000000000000 : ℝ), (46870779013483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1837191151/10000000000 : ℝ)|^4525 ≤ (11192534031177/100000000000000 : ℝ)^3501
        have hw : |(-1837191151/10000000000 : ℝ)|=(1837191151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5105055211/10000000000 : ℝ)|^4525 ≤ (8387337390261/20000000000000 : ℝ)^3501
        have hw : |(5105055211/10000000000 : ℝ)|=(5105055211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(222554539/400000000 : ℝ)|^4525 ≤ (46870779013483/100000000000000 : ℝ)^3501
        have hw : |(222554539/400000000 : ℝ)|=(222554539/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s1_5 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657825071/1250000000 : ℝ)*x 0 + (-809968423/5000000000 : ℝ)*x 1 + (5563863661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657825071/1250000000 : ℝ)^4525 ≤ (21808455853793/50000000000000 : ℝ)^3501 := by
    have hnat : (657825071 : ℕ)^4525*50000000000000^3501 ≤ 21808455853793^3501*1250000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657825071 1250000000 21808455853793 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (809968423/5000000000 : ℝ)^4525 ≤ (9512307244037/100000000000000 : ℝ)^3501 := by
    have hnat : (809968423 : ℕ)^4525*100000000000000^3501 ≤ 9512307244037^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809968423 5000000000 9512307244037 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5563863661/10000000000 : ℝ)^4525 ≤ (4687078103867/10000000000000 : ℝ)^3501 := by
    have hnat : (5563863661 : ℕ)^4525*10000000000000^3501 ≤ 4687078103867^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5563863661 10000000000 4687078103867 10000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657825071/1250000000 : ℝ), (-809968423/5000000000 : ℝ), (5563863661/10000000000 : ℝ)] ![(21808455853793/50000000000000 : ℝ), (9512307244037/100000000000000 : ℝ), (4687078103867/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657825071/1250000000 : ℝ)|^4525 ≤ (21808455853793/50000000000000 : ℝ)^3501
        have hw : |(657825071/1250000000 : ℝ)|=(657825071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-809968423/5000000000 : ℝ)|^4525 ≤ (9512307244037/100000000000000 : ℝ)^3501
        have hw : |(-809968423/5000000000 : ℝ)|=(809968423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5563863661/10000000000 : ℝ)|^4525 ≤ (4687078103867/10000000000000 : ℝ)^3501
        have hw : |(5563863661/10000000000 : ℝ)|=(5563863661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s1_6 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526260033/1000000000 : ℝ)*x 0 + (1112772753/2000000000 : ℝ)*x 1 + (-1619937033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526260033/1000000000 : ℝ)^4525 ≤ (43616909158069/100000000000000 : ℝ)^3501 := by
    have hnat : (526260033 : ℕ)^4525*100000000000000^3501 ≤ 43616909158069^3501*1000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526260033 1000000000 43616909158069 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1112772753/2000000000 : ℝ)^4525 ≤ (5858847771379/12500000000000 : ℝ)^3501 := by
    have hnat : (1112772753 : ℕ)^4525*12500000000000^3501 ≤ 5858847771379^3501*2000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112772753 2000000000 5858847771379 12500000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1619937033/10000000000 : ℝ)^4525 ≤ (9512308663277/100000000000000 : ℝ)^3501 := by
    have hnat : (1619937033 : ℕ)^4525*100000000000000^3501 ≤ 9512308663277^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1619937033 10000000000 9512308663277 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526260033/1000000000 : ℝ), (1112772753/2000000000 : ℝ), (-1619937033/10000000000 : ℝ)] ![(43616909158069/100000000000000 : ℝ), (5858847771379/12500000000000 : ℝ), (9512308663277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526260033/1000000000 : ℝ)|^4525 ≤ (43616909158069/100000000000000 : ℝ)^3501
        have hw : |(526260033/1000000000 : ℝ)|=(526260033/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1112772753/2000000000 : ℝ)|^4525 ≤ (5858847771379/12500000000000 : ℝ)^3501
        have hw : |(1112772753/2000000000 : ℝ)|=(1112772753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1619937033/10000000000 : ℝ)|^4525 ≤ (9512308663277/100000000000000 : ℝ)^3501
        have hw : |(-1619937033/10000000000 : ℝ)|=(1619937033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s1_7 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4249560047/10000000000 : ℝ)*x 0 + (479807811/1000000000 : ℝ)*x 1 + (58690993/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4249560047/10000000000 : ℝ)^4525 ≤ (33085605970487/100000000000000 : ℝ)^3501 := by
    have hnat : (4249560047 : ℕ)^4525*100000000000000^3501 ≤ 33085605970487^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249560047 10000000000 33085605970487 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (479807811/1000000000 : ℝ)^4525 ≤ (9676613241493/25000000000000 : ℝ)^3501 := by
    have hnat : (479807811 : ℕ)^4525*25000000000000^3501 ≤ 9676613241493^3501*1000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479807811 1000000000 9676613241493 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58690993/156250000 : ℝ)^4525 ≤ (28207941052789/100000000000000 : ℝ)^3501 := by
    have hnat : (58690993 : ℕ)^4525*100000000000000^3501 ≤ 28207941052789^3501*156250000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58690993 156250000 28207941052789 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4249560047/10000000000 : ℝ), (479807811/1000000000 : ℝ), (58690993/156250000 : ℝ)] ![(33085605970487/100000000000000 : ℝ), (9676613241493/25000000000000 : ℝ), (28207941052789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4249560047/10000000000 : ℝ)|^4525 ≤ (33085605970487/100000000000000 : ℝ)^3501
        have hw : |(4249560047/10000000000 : ℝ)|=(4249560047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(479807811/1000000000 : ℝ)|^4525 ≤ (9676613241493/25000000000000 : ℝ)^3501
        have hw : |(479807811/1000000000 : ℝ)|=(479807811/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(58690993/156250000 : ℝ)|^4525 ≤ (28207941052789/100000000000000 : ℝ)^3501
        have hw : |(58690993/156250000 : ℝ)|=(58690993/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1514_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12729/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2853/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8383/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18311/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12729/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2853/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12729/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2853/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12729/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2853/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12729/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2853/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12729/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2853/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12729/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2853/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2853/100000 : ℝ) ^ (4523/1024 : ℝ) ≤ (15034188576053/100000000000000000000 : ℝ) := by
    have hpowers : (2853/100000 : ℝ)^4523 ≤ (15034188576053/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2853 : ℕ)^4523*100000000000000000000^1024 ≤ 15034188576053^1024*100000^4523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2853 100000 15034188576053 100000000000000000000 4523 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2853/100000 : ℝ)) (X := (15034188576053/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12729/50000 : ℝ) ^ (4523/1024 : ℝ) ≤ (237427213880120487/100000000000000000000 : ℝ) := by
    have hpowers : (12729/50000 : ℝ)^4523 ≤ (237427213880120487/100000000000000000000 : ℝ)^1024 := by
      have hnat : (12729 : ℕ)^4523*100000000000000000000^1024 ≤ 237427213880120487^1024*50000^4523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12729 50000 237427213880120487 100000000000000000000 4523 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12729/50000 : ℝ)) (X := (237427213880120487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000015034188576053/50000000000000000000 : ℝ) ≤ (5000000340371597/5000000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (50000015034188576053/50000000000000000000 : ℝ)^1024 ≤ (5000000340371597/5000000000000000 : ℝ)^4523 := by
      have hnat : (50000015034188576053 : ℕ)^1024*5000000000000000^4523 ≤ 5000000340371597^4523*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000015034188576053 50000000000000000000 5000000340371597 5000000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000340371597/5000000000000000 : ℝ)) (X := (50000015034188576053/50000000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5011872112403434827/5000000000000000000 : ℝ) ≤ (5002685362231691/5000000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (5011872112403434827/5000000000000000000 : ℝ)^1024 ≤ (5002685362231691/5000000000000000 : ℝ)^4523 := by
      have hnat : (5011872112403434827 : ℕ)^1024*5000000000000000^4523 ≤ 5002685362231691^4523*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5011872112403434827 5000000000000000000 5002685362231691 5000000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002685362231691/5000000000000000 : ℝ)) (X := (5011872112403434827/5000000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50237427213880120487/50000000000000000000 : ℝ) ≤ (1001074076818357/1000000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (50237427213880120487/50000000000000000000 : ℝ)^1024 ≤ (1001074076818357/1000000000000000 : ℝ)^4523 := by
      have hnat : (50237427213880120487 : ℕ)^1024*1000000000000000^4523 ≤ 1001074076818357^4523*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50237427213880120487 50000000000000000000 1001074076818357 1000000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001074076818357/1000000000000000 : ℝ)) (X := (50237427213880120487/50000000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15034188576053/100000000000000000000 : ℝ) ≤ ((37669895653122084607/37675000000000000000 : ℝ)+2*(447503643349/188375000000000 : ℝ)*(2853/100000 : ℝ))^(4523/1024 : ℝ) := by
    rw [show (37669895653122084607/37675000000000000000 : ℝ)+2*(447503643349/188375000000000 : ℝ)*(2853/100000 : ℝ)=(5000000340371597/5000000000000000 : ℝ) by norm_num, show 1+2*(15034188576053/100000000000000000000 : ℝ)=(50000015034188576053/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(237427213880120487/100000000000000000000 : ℝ)+(15034188576053/100000000000000000000 : ℝ) ≤ ((37669895653122084607/37675000000000000000 : ℝ)+(447503643349/188375000000000 : ℝ)*((12729/50000 : ℝ)+(2853/100000 : ℝ)))^(4523/1024 : ℝ) := by
    rw [show (37669895653122084607/37675000000000000000 : ℝ)+(447503643349/188375000000000 : ℝ)*((12729/50000 : ℝ)+(2853/100000 : ℝ))=(5002685362231691/5000000000000000 : ℝ) by norm_num, show 1+(237427213880120487/100000000000000000000 : ℝ)+(15034188576053/100000000000000000000 : ℝ)=(5011872112403434827/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(237427213880120487/100000000000000000000 : ℝ) ≤ ((37669895653122084607/37675000000000000000 : ℝ)+2*(447503643349/188375000000000 : ℝ)*(12729/50000 : ℝ))^(4523/1024 : ℝ) := by
    rw [show (37669895653122084607/37675000000000000000 : ℝ)+2*(447503643349/188375000000000 : ℝ)*(12729/50000 : ℝ)=(1001074076818357/1000000000000000 : ℝ) by norm_num, show 1+2*(237427213880120487/100000000000000000000 : ℝ)=(50237427213880120487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37669895653122084607/37675000000000000000 : ℝ)*(X 1 0+X 2 0)+(447503643349/188375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (2853/100000 : ℝ)) (hi := (12729/50000 : ℝ)) (c := (37669895653122084607/37675000000000000000 : ℝ)) (alpha := (447503643349/188375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37669895653122084607/37675000000000000000 : ℝ)*(X 0 1+X 2 1)+(447503643349/188375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (2853/100000 : ℝ)) (hi := (12729/50000 : ℝ)) (c := (37669895653122084607/37675000000000000000 : ℝ)) (alpha := (447503643349/188375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37669895653122084607/37675000000000000000 : ℝ)*(X 0 2+X 1 2)+(447503643349/188375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (2853/100000 : ℝ)) (hi := (12729/50000 : ℝ)) (c := (37669895653122084607/37675000000000000000 : ℝ)) (alpha := (447503643349/188375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1836892983/10000000000 : ℝ)*X 0 0+(5569181661/10000000000 : ℝ)*X 0 1+(509982103/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5260017/9765625 : ℝ)*X 1 0+(-2083979877/10000000000 : ℝ)*X 1 1+(1274955127/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((336641069/625000000 : ℝ)*X 2 0+(2549910427/5000000000 : ℝ)*X 2 1+(-208397983/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2124441293/5000000000 : ℝ)*X 0 0+(149765909/400000000 : ℝ)*X 0 1+(4809963739/10000000000 : ℝ)*X 0 2+(2124441293/5000000000 : ℝ)*X 1 0+(149765909/400000000 : ℝ)*X 1 1+(4809963739/10000000000 : ℝ)*X 1 2+(2124441293/5000000000 : ℝ)*X 2 0+(149765909/400000000 : ℝ)*X 2 1+(4809963739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1837191151/10000000000 : ℝ)*X 0 0+(5105055211/10000000000 : ℝ)*X 0 1+(222554539/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((657825071/1250000000 : ℝ)*X 1 0+(-809968423/5000000000 : ℝ)*X 1 1+(5563863661/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((526260033/1000000000 : ℝ)*X 2 0+(1112772753/2000000000 : ℝ)*X 2 1+(-1619937033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4249560047/10000000000 : ℝ)*X 0 0+(479807811/1000000000 : ℝ)*X 0 1+(58690993/156250000 : ℝ)*X 0 2+(4249560047/10000000000 : ℝ)*X 1 0+(479807811/1000000000 : ℝ)*X 1 1+(58690993/156250000 : ℝ)*X 1 2+(4249560047/10000000000 : ℝ)*X 2 0+(479807811/1000000000 : ℝ)*X 2 1+(58690993/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (661882936605020236693241229/117734375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8652259/50000000000000 : ℝ)*(base1) + (1077633679/100000000000000 : ℝ)*(base19) + (59836523/6250000000000 : ℝ)*(base23) + (14615907/20000000000000 : ℝ)*(upper3) + (727407/1000000000000 : ℝ)*(upper5) + (95900875467799/6250000000000 : ℝ)*(major0) + (95900875467799/6250000000000 : ℝ)*(major1) + (95900875467799/6250000000000 : ℝ)*(major2) + (53264131932361/2500000000000 : ℝ)*(sp0) + (532642850054553/25000000000000 : ℝ)*(sp1) + (532642880116881/25000000000000 : ℝ)*(sp2) + (234562954001357/25000000000000 : ℝ)*(sp3) + (7217861969/100000000000000 : ℝ)*(sp4) + (3516413309/100000000000000 : ℝ)*(sp7) + (187651069944651/20000000000000 : ℝ)*(f.failure) + (2130572477851891/100000000000000 : ℝ)*(f.sum) + (21913008313659/9418750000000000000000000000 : ℝ)*base66 + (1043615278636176243/235468750000000000000000000000000 : ℝ)*base67 + (930559256570238743/235468750000000000000000000000000 : ℝ)*base69 + (287678938030386257/235468750000000000000000000000000 : ℝ)*base72 + (10548316471207/18837500000000000000000000000 : ℝ)*base73 + (1355356350468355007/235468750000000000000000000000000 : ℝ)*base76 + (1546206661780386257/235468750000000000000000000000000 : ℝ)*base78 + (2407770325563667507/235468750000000000000000000000000 : ℝ)*base80 + (24952841391741/9418750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6402013/2000000000000000000000 : ℝ)*base89 + (6402013/2000000000000000000000 : ℝ)*base91 + (6402013/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (256157219176129353459123/37675000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65106951/5000000000000 : ℝ)*(base19) + (331571513/25000000000000 : ℝ)*(base23) + (48056357/25000000000000 : ℝ)*(upper3) + (54289503/100000000000000 : ℝ)*(lower4) + (81875369/100000000000000 : ℝ)*(upper5) + (1569692418120929/100000000000000 : ℝ)*(major0) + (1569692418120929/100000000000000 : ℝ)*(major1) + (1569692418120929/100000000000000 : ℝ)*(major2) + (4589669723/50000000000000 : ℝ)*(sp1) + (10011611747/100000000000000 : ℝ)*(sp2) + (2179557404209887/100000000000000 : ℝ)*(sp4) + (2179546922731421/100000000000000 : ℝ)*(sp5) + (272443258289011/12500000000000 : ℝ)*(sp6) + (959827205394303/100000000000000 : ℝ)*(sp7) + (959827205394303/100000000000000 : ℝ)*(f.failure) + (2179557404209887/100000000000000 : ℝ)*(f.sum) + (31038323725421/9418750000000000000000000000 : ℝ)*base65 + (19438586179232860097/3767500000000000000000000000000000 : ℝ)*base68 + (6231564814122139903/3767500000000000000000000000000000 : ℝ)*base69 + (13592228438392139903/3767500000000000000000000000000000 : ℝ)*base71 + (75808930649483/18837500000000000000000000000 : ℝ)*base74 + (6034561937547860097/3767500000000000000000000000000000 : ℝ)*base76 + (9334099602332139903/3767500000000000000000000000000000 : ℝ)*base77 + (4894499419750360097/3767500000000000000000000000000000 : ℝ)*base80 + (17199995135017/18837500000000000000000000000 : ℝ)*base81 + (41841911/10000000000000000000000 : ℝ)*base90 + (41841911/10000000000000000000000 : ℝ)*base92 + (41841911/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1514_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12729/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2853/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8383/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18311/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1514_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1514_s2_0 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1861180789/10000000000 : ℝ)*x 0 + (5457281459/10000000000 : ℝ)*x 1 + (5195985663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1861180789/10000000000 : ℝ)^4525 ≤ (11381790293147/100000000000000 : ℝ)^3501 := by
    have hnat : (1861180789 : ℕ)^4525*100000000000000^3501 ≤ 11381790293147^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1861180789 10000000000 11381790293147 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457281459/10000000000 : ℝ)^4525 ≤ (45713568996557/100000000000000 : ℝ)^3501 := by
    have hnat : (5457281459 : ℕ)^4525*100000000000000^3501 ≤ 45713568996557^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457281459 10000000000 45713568996557 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195985663/10000000000 : ℝ)^4525 ≤ (42904640696449/100000000000000 : ℝ)^3501 := by
    have hnat : (5195985663 : ℕ)^4525*100000000000000^3501 ≤ 42904640696449^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195985663 10000000000 42904640696449 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1861180789/10000000000 : ℝ), (5457281459/10000000000 : ℝ), (5195985663/10000000000 : ℝ)] ![(11381790293147/100000000000000 : ℝ), (45713568996557/100000000000000 : ℝ), (42904640696449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1861180789/10000000000 : ℝ)|^4525 ≤ (11381790293147/100000000000000 : ℝ)^3501
        have hw : |(-1861180789/10000000000 : ℝ)|=(1861180789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457281459/10000000000 : ℝ)|^4525 ≤ (45713568996557/100000000000000 : ℝ)^3501
        have hw : |(5457281459/10000000000 : ℝ)|=(5457281459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195985663/10000000000 : ℝ)|^4525 ≤ (42904640696449/100000000000000 : ℝ)^3501
        have hw : |(5195985663/10000000000 : ℝ)|=(5195985663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s2_1 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535780659/1000000000 : ℝ)*x 0 + (-997837327/5000000000 : ℝ)*x 1 + (5195986347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535780659/1000000000 : ℝ)^4525 ≤ (11159867481151/25000000000000 : ℝ)^3501 := by
    have hnat : (535780659 : ℕ)^4525*25000000000000^3501 ≤ 11159867481151^3501*1000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535780659 1000000000 11159867481151 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (997837327/5000000000 : ℝ)^4525 ≤ (12455882063179/100000000000000 : ℝ)^3501 := by
    have hnat : (997837327 : ℕ)^4525*100000000000000^3501 ≤ 12455882063179^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997837327 5000000000 12455882063179 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195986347/10000000000 : ℝ)^4525 ≤ (21452323998191/50000000000000 : ℝ)^3501 := by
    have hnat : (5195986347 : ℕ)^4525*50000000000000^3501 ≤ 21452323998191^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195986347 10000000000 21452323998191 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535780659/1000000000 : ℝ), (-997837327/5000000000 : ℝ), (5195986347/10000000000 : ℝ)] ![(11159867481151/25000000000000 : ℝ), (12455882063179/100000000000000 : ℝ), (21452323998191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535780659/1000000000 : ℝ)|^4525 ≤ (11159867481151/25000000000000 : ℝ)^3501
        have hw : |(535780659/1000000000 : ℝ)|=(535780659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-997837327/5000000000 : ℝ)|^4525 ≤ (12455882063179/100000000000000 : ℝ)^3501
        have hw : |(-997837327/5000000000 : ℝ)|=(997837327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195986347/10000000000 : ℝ)|^4525 ≤ (21452323998191/50000000000000 : ℝ)^3501
        have hw : |(5195986347/10000000000 : ℝ)|=(5195986347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s2_2 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1339451861/2500000000 : ℝ)*x 0 + (5195985799/10000000000 : ℝ)*x 1 + (-3118241/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339451861/2500000000 : ℝ)^4525 ≤ (44639479120973/100000000000000 : ℝ)^3501 := by
    have hnat : (1339451861 : ℕ)^4525*100000000000000^3501 ≤ 44639479120973^3501*2500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339451861 2500000000 44639479120973 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195985799/10000000000 : ℝ)^4525 ≤ (21452321073949/50000000000000 : ℝ)^3501 := by
    have hnat : (5195985799 : ℕ)^4525*50000000000000^3501 ≤ 21452321073949^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195985799 10000000000 21452321073949 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3118241/15625000 : ℝ)^4525 ≤ (1556984840431/12500000000000 : ℝ)^3501 := by
    have hnat : (3118241 : ℕ)^4525*12500000000000^3501 ≤ 1556984840431^3501*15625000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118241 15625000 1556984840431 12500000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339451861/2500000000 : ℝ), (5195985799/10000000000 : ℝ), (-3118241/15625000 : ℝ)] ![(44639479120973/100000000000000 : ℝ), (21452321073949/50000000000000 : ℝ), (1556984840431/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339451861/2500000000 : ℝ)|^4525 ≤ (44639479120973/100000000000000 : ℝ)^3501
        have hw : |(1339451861/2500000000 : ℝ)|=(1339451861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195985799/10000000000 : ℝ)|^4525 ≤ (21452321073949/50000000000000 : ℝ)^3501
        have hw : |(5195985799/10000000000 : ℝ)|=(5195985799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3118241/15625000 : ℝ)|^4525 ≤ (1556984840431/12500000000000 : ℝ)^3501
        have hw : |(-3118241/15625000 : ℝ)|=(3118241/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s2_3 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4266324827/10000000000 : ℝ)*x 0 + (3978386503/10000000000 : ℝ)*x 1 + (914346633/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4266324827/10000000000 : ℝ)^4525 ≤ (6650880981863/20000000000000 : ℝ)^3501 := by
    have hnat : (4266324827 : ℕ)^4525*20000000000000^3501 ≤ 6650880981863^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4266324827 10000000000 6650880981863 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3978386503/10000000000 : ℝ)^4525 ≤ (30382682951453/100000000000000 : ℝ)^3501 := by
    have hnat : (3978386503 : ℕ)^4525*100000000000000^3501 ≤ 30382682951453^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3978386503 10000000000 30382682951453 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (914346633/2000000000 : ℝ)^4525 ≤ (7272582425541/20000000000000 : ℝ)^3501 := by
    have hnat : (914346633 : ℕ)^4525*20000000000000^3501 ≤ 7272582425541^3501*2000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914346633 2000000000 7272582425541 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4266324827/10000000000 : ℝ), (3978386503/10000000000 : ℝ), (914346633/2000000000 : ℝ)] ![(6650880981863/20000000000000 : ℝ), (30382682951453/100000000000000 : ℝ), (7272582425541/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4266324827/10000000000 : ℝ)|^4525 ≤ (6650880981863/20000000000000 : ℝ)^3501
        have hw : |(4266324827/10000000000 : ℝ)|=(4266324827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3978386503/10000000000 : ℝ)|^4525 ≤ (30382682951453/100000000000000 : ℝ)^3501
        have hw : |(3978386503/10000000000 : ℝ)|=(3978386503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(914346633/2000000000 : ℝ)|^4525 ≤ (7272582425541/20000000000000 : ℝ)^3501
        have hw : |(914346633/2000000000 : ℝ)|=(914346633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s2_4 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-930615589/5000000000 : ℝ)*x 0 + (3248511/6250000 : ℝ)*x 1 + (5455635841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (930615589/5000000000 : ℝ)^4525 ≤ (1138218857081/10000000000000 : ℝ)^3501 := by
    have hnat : (930615589 : ℕ)^4525*10000000000000^3501 ≤ 1138218857081^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930615589 5000000000 1138218857081 10000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3248511/6250000 : ℝ)^4525 ≤ (10730514552259/25000000000000 : ℝ)^3501 := by
    have hnat : (3248511 : ℕ)^4525*25000000000000^3501 ≤ 10730514552259^3501*6250000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3248511 6250000 10730514552259 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455635841/10000000000 : ℝ)^4525 ≤ (22847876602471/50000000000000 : ℝ)^3501 := by
    have hnat : (5455635841 : ℕ)^4525*50000000000000^3501 ≤ 22847876602471^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455635841 10000000000 22847876602471 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-930615589/5000000000 : ℝ), (3248511/6250000 : ℝ), (5455635841/10000000000 : ℝ)] ![(1138218857081/10000000000000 : ℝ), (10730514552259/25000000000000 : ℝ), (22847876602471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-930615589/5000000000 : ℝ)|^4525 ≤ (1138218857081/10000000000000 : ℝ)^3501
        have hw : |(-930615589/5000000000 : ℝ)|=(930615589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3248511/6250000 : ℝ)|^4525 ≤ (10730514552259/25000000000000 : ℝ)^3501
        have hw : |(3248511/6250000 : ℝ)|=(3248511/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455635841/10000000000 : ℝ)|^4525 ≤ (22847876602471/50000000000000 : ℝ)^3501
        have hw : |(5455635841/10000000000 : ℝ)|=(5455635841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s2_5 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644587501/5000000000 : ℝ)*x 0 + (-1736024863/10000000000 : ℝ)*x 1 + (5455636891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644587501/5000000000 : ℝ)^4525 ≤ (43901793846011/100000000000000 : ℝ)^3501 := by
    have hnat : (2644587501 : ℕ)^4525*100000000000000^3501 ≤ 43901793846011^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644587501 5000000000 43901793846011 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1736024863/10000000000 : ℝ)^4525 ≤ (2080488312571/20000000000000 : ℝ)^3501 := by
    have hnat : (1736024863 : ℕ)^4525*20000000000000^3501 ≤ 2080488312571^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1736024863 10000000000 2080488312571 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455636891/10000000000 : ℝ)^4525 ≤ (2855985285747/6250000000000 : ℝ)^3501 := by
    have hnat : (5455636891 : ℕ)^4525*6250000000000^3501 ≤ 2855985285747^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455636891 10000000000 2855985285747 6250000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644587501/5000000000 : ℝ), (-1736024863/10000000000 : ℝ), (5455636891/10000000000 : ℝ)] ![(43901793846011/100000000000000 : ℝ), (2080488312571/20000000000000 : ℝ), (2855985285747/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644587501/5000000000 : ℝ)|^4525 ≤ (43901793846011/100000000000000 : ℝ)^3501
        have hw : |(2644587501/5000000000 : ℝ)|=(2644587501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1736024863/10000000000 : ℝ)|^4525 ≤ (2080488312571/20000000000000 : ℝ)^3501
        have hw : |(-1736024863/10000000000 : ℝ)|=(1736024863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455636891/10000000000 : ℝ)|^4525 ≤ (2855985285747/6250000000000 : ℝ)^3501
        have hw : |(5455636891/10000000000 : ℝ)|=(5455636891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s2_6 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644587921/5000000000 : ℝ)*x 0 + (2727818059/5000000000 : ℝ)*x 1 + (-1736024781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644587921/5000000000 : ℝ)^4525 ≤ (21950901428787/50000000000000 : ℝ)^3501 := by
    have hnat : (2644587921 : ℕ)^4525*50000000000000^3501 ≤ 21950901428787^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644587921 5000000000 21950901428787 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2727818059/5000000000 : ℝ)^4525 ≤ (45695756203667/100000000000000 : ℝ)^3501 := by
    have hnat : (2727818059 : ℕ)^4525*100000000000000^3501 ≤ 45695756203667^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727818059 5000000000 45695756203667 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1736024781/10000000000 : ℝ)^4525 ≤ (2600610231947/25000000000000 : ℝ)^3501 := by
    have hnat : (1736024781 : ℕ)^4525*25000000000000^3501 ≤ 2600610231947^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1736024781 10000000000 2600610231947 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644587921/5000000000 : ℝ), (2727818059/5000000000 : ℝ), (-1736024781/10000000000 : ℝ)] ![(21950901428787/50000000000000 : ℝ), (45695756203667/100000000000000 : ℝ), (2600610231947/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644587921/5000000000 : ℝ)|^4525 ≤ (21950901428787/50000000000000 : ℝ)^3501
        have hw : |(2644587921/5000000000 : ℝ)|=(2644587921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2727818059/5000000000 : ℝ)|^4525 ≤ (45695756203667/100000000000000 : ℝ)^3501
        have hw : |(2727818059/5000000000 : ℝ)|=(2727818059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1736024781/10000000000 : ℝ)|^4525 ≤ (2600610231947/25000000000000 : ℝ)^3501
        have hw : |(-1736024781/10000000000 : ℝ)|=(1736024781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s2_7 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2133221389/5000000000 : ℝ)*x 0 + (4568029519/10000000000 : ℝ)*x 1 + (497765311/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133221389/5000000000 : ℝ)^4525 ≤ (8313898301659/25000000000000 : ℝ)^3501 := by
    have hnat : (2133221389 : ℕ)^4525*25000000000000^3501 ≤ 8313898301659^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133221389 5000000000 8313898301659 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4568029519/10000000000 : ℝ)^4525 ≤ (7264968436381/20000000000000 : ℝ)^3501 := by
    have hnat : (4568029519 : ℕ)^4525*20000000000000^3501 ≤ 7264968436381^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4568029519 10000000000 7264968436381 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497765311/1250000000 : ℝ)^4525 ≤ (30419564603931/100000000000000 : ℝ)^3501 := by
    have hnat : (497765311 : ℕ)^4525*100000000000000^3501 ≤ 30419564603931^3501*1250000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497765311 1250000000 30419564603931 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133221389/5000000000 : ℝ), (4568029519/10000000000 : ℝ), (497765311/1250000000 : ℝ)] ![(8313898301659/25000000000000 : ℝ), (7264968436381/20000000000000 : ℝ), (30419564603931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133221389/5000000000 : ℝ)|^4525 ≤ (8313898301659/25000000000000 : ℝ)^3501
        have hw : |(2133221389/5000000000 : ℝ)|=(2133221389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4568029519/10000000000 : ℝ)|^4525 ≤ (7264968436381/20000000000000 : ℝ)^3501
        have hw : |(4568029519/10000000000 : ℝ)|=(4568029519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(497765311/1250000000 : ℝ)|^4525 ≤ (30419564603931/100000000000000 : ℝ)^3501
        have hw : |(497765311/1250000000 : ℝ)|=(497765311/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1514_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18311/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5229/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15989/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18311/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8383/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18311/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8383/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18311/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8383/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18311/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8383/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18311/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8383/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18311/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8383/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8383/100000 : ℝ) ^ (4523/1024 : ℝ) ≤ (439140873736697/25000000000000000000 : ℝ) := by
    have hpowers : (8383/100000 : ℝ)^4523 ≤ (439140873736697/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8383 : ℕ)^4523*25000000000000000000^1024 ≤ 439140873736697^1024*100000^4523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8383 100000 439140873736697 25000000000000000000 4523 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8383/100000 : ℝ)) (X := (439140873736697/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18311/100000 : ℝ) ^ (4523/1024 : ℝ) ≤ (55386629924429921/100000000000000000000 : ℝ) := by
    have hpowers : (18311/100000 : ℝ)^4523 ≤ (55386629924429921/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18311 : ℕ)^4523*100000000000000000000^1024 ≤ 55386629924429921^1024*100000^4523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18311 100000 55386629924429921 100000000000000000000 4523 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18311/100000 : ℝ)) (X := (55386629924429921/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500439140873736697/12500000000000000000 : ℝ) ≤ (625004970972189/625000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (12500439140873736697/12500000000000000000 : ℝ)^1024 ≤ (625004970972189/625000000000000 : ℝ)^4523 := by
      have hnat : (12500439140873736697 : ℕ)^1024*625000000000000^4523 ≤ 625004970972189^4523*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500439140873736697 12500000000000000000 625004970972189 625000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625004970972189/625000000000000 : ℝ)) (X := (12500439140873736697/12500000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100057143193419376709/100000000000000000000 : ℝ) ≤ (5000646713474699/5000000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (100057143193419376709/100000000000000000000 : ℝ)^1024 ≤ (5000646713474699/5000000000000000 : ℝ)^4523 := by
      have hnat : (100057143193419376709 : ℕ)^1024*5000000000000000^4523 ≤ 5000646713474699^4523*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100057143193419376709 100000000000000000000 5000646713474699 5000000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000646713474699/5000000000000000 : ℝ)) (X := (100057143193419376709/100000000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50055386629924429921/50000000000000000000 : ℝ) ≤ (2500626829585943/2500000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (50055386629924429921/50000000000000000000 : ℝ)^1024 ≤ (2500626829585943/2500000000000000 : ℝ)^4523 := by
      have hnat : (50055386629924429921 : ℕ)^1024*2500000000000000^4523 ≤ 2500626829585943^4523*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50055386629924429921 50000000000000000000 2500626829585943 2500000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500626829585943/2500000000000000 : ℝ)) (X := (50055386629924429921/50000000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(439140873736697/25000000000000000000 : ℝ) ≤ ((339933005225589739/340000000000000000 : ℝ)+2*(8314324619/6800000000000 : ℝ)*(8383/100000 : ℝ))^(4523/1024 : ℝ) := by
    rw [show (339933005225589739/340000000000000000 : ℝ)+2*(8314324619/6800000000000 : ℝ)*(8383/100000 : ℝ)=(625004970972189/625000000000000 : ℝ) by norm_num, show 1+2*(439140873736697/25000000000000000000 : ℝ)=(12500439140873736697/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(55386629924429921/100000000000000000000 : ℝ)+(439140873736697/25000000000000000000 : ℝ) ≤ ((339933005225589739/340000000000000000 : ℝ)+(8314324619/6800000000000 : ℝ)*((18311/100000 : ℝ)+(8383/100000 : ℝ)))^(4523/1024 : ℝ) := by
    rw [show (339933005225589739/340000000000000000 : ℝ)+(8314324619/6800000000000 : ℝ)*((18311/100000 : ℝ)+(8383/100000 : ℝ))=(5000646713474699/5000000000000000 : ℝ) by norm_num, show 1+(55386629924429921/100000000000000000000 : ℝ)+(439140873736697/25000000000000000000 : ℝ)=(100057143193419376709/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(55386629924429921/100000000000000000000 : ℝ) ≤ ((339933005225589739/340000000000000000 : ℝ)+2*(8314324619/6800000000000 : ℝ)*(18311/100000 : ℝ))^(4523/1024 : ℝ) := by
    rw [show (339933005225589739/340000000000000000 : ℝ)+2*(8314324619/6800000000000 : ℝ)*(18311/100000 : ℝ)=(2500626829585943/2500000000000000 : ℝ) by norm_num, show 1+2*(55386629924429921/100000000000000000000 : ℝ)=(50055386629924429921/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (339933005225589739/340000000000000000 : ℝ)*(X 1 0+X 2 0)+(8314324619/6800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (8383/100000 : ℝ)) (hi := (18311/100000 : ℝ)) (c := (339933005225589739/340000000000000000 : ℝ)) (alpha := (8314324619/6800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (339933005225589739/340000000000000000 : ℝ)*(X 0 1+X 2 1)+(8314324619/6800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (8383/100000 : ℝ)) (hi := (18311/100000 : ℝ)) (c := (339933005225589739/340000000000000000 : ℝ)) (alpha := (8314324619/6800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (339933005225589739/340000000000000000 : ℝ)*(X 0 2+X 1 2)+(8314324619/6800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (8383/100000 : ℝ)) (hi := (18311/100000 : ℝ)) (c := (339933005225589739/340000000000000000 : ℝ)) (alpha := (8314324619/6800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1861180789/10000000000 : ℝ)*X 0 0+(5457281459/10000000000 : ℝ)*X 0 1+(5195985663/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535780659/1000000000 : ℝ)*X 1 0+(-997837327/5000000000 : ℝ)*X 1 1+(5195986347/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1339451861/2500000000 : ℝ)*X 2 0+(5195985799/10000000000 : ℝ)*X 2 1+(-3118241/15625000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4266324827/10000000000 : ℝ)*X 0 0+(3978386503/10000000000 : ℝ)*X 0 1+(914346633/2000000000 : ℝ)*X 0 2+(4266324827/10000000000 : ℝ)*X 1 0+(3978386503/10000000000 : ℝ)*X 1 1+(914346633/2000000000 : ℝ)*X 1 2+(4266324827/10000000000 : ℝ)*X 2 0+(3978386503/10000000000 : ℝ)*X 2 1+(914346633/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-930615589/5000000000 : ℝ)*X 0 0+(3248511/6250000 : ℝ)*X 0 1+(5455635841/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644587501/5000000000 : ℝ)*X 1 0+(-1736024863/10000000000 : ℝ)*X 1 1+(5455636891/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644587921/5000000000 : ℝ)*X 2 0+(2727818059/5000000000 : ℝ)*X 2 1+(-1736024781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2133221389/5000000000 : ℝ)*X 0 0+(4568029519/10000000000 : ℝ)*X 0 1+(497765311/1250000000 : ℝ)*X 0 2+(2133221389/5000000000 : ℝ)*X 1 0+(4568029519/10000000000 : ℝ)*X 1 1+(497765311/1250000000 : ℝ)*X 1 2+(2133221389/5000000000 : ℝ)*X 2 0+(4568029519/10000000000 : ℝ)*X 2 1+(497765311/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7355063387685787955282751/8500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (453031179/100000000000000 : ℝ)*(base19) + (66337013/10000000000000 : ℝ)*(base23) + (4485937/100000000000000 : ℝ)*(upper3) + (107069643/50000000000000 : ℝ)*(upper4) + (20598899/12500000000000 : ℝ)*(upper5) + (1378119081169697/50000000000000 : ℝ)*(major0) + (1378119081169697/50000000000000 : ℝ)*(major1) + (1378119081169697/50000000000000 : ℝ)*(major2) + (1913544046388717/50000000000000 : ℝ)*(sp0) + (239194120668741/6250000000000 : ℝ)*(sp1) + (1913552860180453/50000000000000 : ℝ)*(sp2) + (337072453874513/20000000000000 : ℝ)*(sp3) + (9145476801/50000000000000 : ℝ)*(sp4) + (1528546359/20000000000000 : ℝ)*(sp7) + (42134247802609/2500000000000 : ℝ)*(f.failure) + (956776595932759/25000000000000 : ℝ)*(f.sum) + (490375409333/170000000000000000000000000 : ℝ)*base65 + (133002979218910917/17000000000000000000000000000000 : ℝ)*base68 + (110996932730089083/17000000000000000000000000000000 : ℝ)*base69 + (128529940598089083/17000000000000000000000000000000 : ℝ)*base71 + (801644615477/170000000000000000000000000 : ℝ)*base74 + (79076236594089083/17000000000000000000000000000000 : ℝ)*base75 + (88127124209910917/17000000000000000000000000000000 : ℝ)*base78 + (74220518485089083/17000000000000000000000000000000 : ℝ)*base79 + (722785203793/170000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (184633/250000000000000000000 : ℝ)*base90 + (184633/250000000000000000000 : ℝ)*base92 + (184633/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5022206122663610916170361/425000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (489292437/50000000000000 : ℝ)*(base23) + (168312759/100000000000000 : ℝ)*(lower2) + (143029353/50000000000000 : ℝ)*(upper3) + (17807697/6250000000000 : ℝ)*(lower4) + (139561365043633/5000000000000 : ℝ)*(major0) + (139561365043633/5000000000000 : ℝ)*(major1) + (139561365043633/5000000000000 : ℝ)*(major2) + (931164403/20000000000000 : ℝ)*(sp1) + (1955660483/12500000000000 : ℝ)*(sp2) + (373400247/12500000000000 : ℝ)*(sp3) + (3875689322644613/100000000000000 : ℝ)*(sp4) + (1937842333411299/50000000000000 : ℝ)*(sp5) + (968918174693969/25000000000000 : ℝ)*(sp6) + (853380949000099/50000000000000 : ℝ)*(sp7) + (853382442601087/50000000000000 : ℝ)*(f.failure) + (3875689322644613/100000000000000 : ℝ)*(f.sum) + (73762828567/17000000000000000000000000 : ℝ)*base66 + (15137950999568213/1700000000000000000000000000000 : ℝ)*base68 + (4690937101468213/1700000000000000000000000000000 : ℝ)*base70 + (25072816877968213/1700000000000000000000000000000 : ℝ)*base72 + (80855227/27200000000000000000000 : ℝ)*base74 + (21376296834468213/1700000000000000000000000000000 : ℝ)*base76 + (96648037946631787/1700000000000000000000000000000 : ℝ)*base77 + (20385082436368213/1700000000000000000000000000000 : ℝ)*base80 + (7820918311/17000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (50761481/5000000000000000000000 : ℝ)*base89 + (50761481/5000000000000000000000 : ℝ)*base91 + (50761481/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1514_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18311/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5229/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15989/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1514_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1514_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5229/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15989/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1514_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1514_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1514_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5229/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15989/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1514_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

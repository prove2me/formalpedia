-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1470_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:10:15.158346+00:00
-- url     : https://prove2.me/submissions/df963988-7d61-49aa-bdaf-578e70b041cc

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
theorem support_rectangle_w1470_s3_0 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-482769343/2500000000 : ℝ)*x 0 + (5444024867/10000000000 : ℝ)*x 1 + (2605242253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (482769343/2500000000 : ℝ)^4437 ≤ (5895065784011/50000000000000 : ℝ)^3413 := by
    have hnat : (482769343 : ℕ)^4437*50000000000000^3413 ≤ 5895065784011^3413*2500000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482769343 2500000000 5895065784011 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5444024867/10000000000 : ℝ)^4437 ≤ (5670200368967/12500000000000 : ℝ)^3413 := by
    have hnat : (5444024867 : ℕ)^4437*12500000000000^3413 ≤ 5670200368967^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444024867 10000000000 5670200368967 12500000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2605242253/5000000000 : ℝ)^4437 ≤ (267801659191/625000000000 : ℝ)^3413 := by
    have hnat : (2605242253 : ℕ)^4437*625000000000^3413 ≤ 267801659191^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605242253 5000000000 267801659191 625000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-482769343/2500000000 : ℝ), (5444024867/10000000000 : ℝ), (2605242253/5000000000 : ℝ)] ![(5895065784011/50000000000000 : ℝ), (5670200368967/12500000000000 : ℝ), (267801659191/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-482769343/2500000000 : ℝ)|^4437 ≤ (5895065784011/50000000000000 : ℝ)^3413
        have hw : |(-482769343/2500000000 : ℝ)|=(482769343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5444024867/10000000000 : ℝ)|^4437 ≤ (5670200368967/12500000000000 : ℝ)^3413
        have hw : |(5444024867/10000000000 : ℝ)|=(5444024867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2605242253/5000000000 : ℝ)|^4437 ≤ (267801659191/625000000000 : ℝ)^3413
        have hw : |(2605242253/5000000000 : ℝ)|=(2605242253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s3_1 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41837377/78125000 : ℝ)*x 0 + (-1025461981/5000000000 : ℝ)*x 1 + (2605242093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41837377/78125000 : ℝ)^4437 ≤ (5550202258831/12500000000000 : ℝ)^3413 := by
    have hnat : (41837377 : ℕ)^4437*12500000000000^3413 ≤ 5550202258831^3413*78125000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41837377 78125000 5550202258831 12500000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025461981/5000000000 : ℝ)^4437 ≤ (3187529963563/25000000000000 : ℝ)^3413 := by
    have hnat : (1025461981 : ℕ)^4437*25000000000000^3413 ≤ 3187529963563^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025461981 5000000000 3187529963563 25000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2605242093/5000000000 : ℝ)^4437 ≤ (42848262049519/100000000000000 : ℝ)^3413 := by
    have hnat : (2605242093 : ℕ)^4437*100000000000000^3413 ≤ 42848262049519^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605242093 5000000000 42848262049519 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41837377/78125000 : ℝ), (-1025461981/5000000000 : ℝ), (2605242093/5000000000 : ℝ)] ![(5550202258831/12500000000000 : ℝ), (3187529963563/25000000000000 : ℝ), (42848262049519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41837377/78125000 : ℝ)|^4437 ≤ (5550202258831/12500000000000 : ℝ)^3413
        have hw : |(41837377/78125000 : ℝ)|=(41837377/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1025461981/5000000000 : ℝ)|^4437 ≤ (3187529963563/25000000000000 : ℝ)^3413
        have hw : |(-1025461981/5000000000 : ℝ)|=(1025461981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2605242093/5000000000 : ℝ)|^4437 ≤ (42848262049519/100000000000000 : ℝ)^3413
        have hw : |(2605242093/5000000000 : ℝ)|=(2605242093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s3_2 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669398081/1250000000 : ℝ)*x 0 + (2605241943/5000000000 : ℝ)*x 1 + (-1025461919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669398081/1250000000 : ℝ)^4437 ≤ (44401622296007/100000000000000 : ℝ)^3413 := by
    have hnat : (669398081 : ℕ)^4437*100000000000000^3413 ≤ 44401622296007^3413*1250000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669398081 1250000000 44401622296007 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2605241943/5000000000 : ℝ)^4437 ≤ (42848258842293/100000000000000 : ℝ)^3413 := by
    have hnat : (2605241943 : ℕ)^4437*100000000000000^3413 ≤ 42848258842293^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605241943 5000000000 42848258842293 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025461919/5000000000 : ℝ)^4437 ≤ (12750118852087/100000000000000 : ℝ)^3413 := by
    have hnat : (1025461919 : ℕ)^4437*100000000000000^3413 ≤ 12750118852087^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025461919 5000000000 12750118852087 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669398081/1250000000 : ℝ), (2605241943/5000000000 : ℝ), (-1025461919/5000000000 : ℝ)] ![(44401622296007/100000000000000 : ℝ), (42848258842293/100000000000000 : ℝ), (12750118852087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669398081/1250000000 : ℝ)|^4437 ≤ (44401622296007/100000000000000 : ℝ)^3413
        have hw : |(669398081/1250000000 : ℝ)|=(669398081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2605241943/5000000000 : ℝ)|^4437 ≤ (42848258842293/100000000000000 : ℝ)^3413
        have hw : |(2605241943/5000000000 : ℝ)|=(2605241943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1025461919/5000000000 : ℝ)|^4437 ≤ (12750118852087/100000000000000 : ℝ)^3413
        have hw : |(-1025461919/5000000000 : ℝ)|=(1025461919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s3_3 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536154149/1250000000 : ℝ)*x 0 + (4039033497/10000000000 : ℝ)*x 1 + (4552971547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536154149/1250000000 : ℝ)^4437 ≤ (3327229702349/10000000000000 : ℝ)^3413 := by
    have hnat : (536154149 : ℕ)^4437*10000000000000^3413 ≤ 3327229702349^3413*1250000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536154149 1250000000 3327229702349 10000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4039033497/10000000000 : ℝ)^4437 ≤ (3846441825479/12500000000000 : ℝ)^3413 := by
    have hnat : (4039033497 : ℕ)^4437*12500000000000^3413 ≤ 3846441825479^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4039033497 10000000000 3846441825479 12500000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4552971547/10000000000 : ℝ)^4437 ≤ (7191233671917/20000000000000 : ℝ)^3413 := by
    have hnat : (4552971547 : ℕ)^4437*20000000000000^3413 ≤ 7191233671917^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4552971547 10000000000 7191233671917 20000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536154149/1250000000 : ℝ), (4039033497/10000000000 : ℝ), (4552971547/10000000000 : ℝ)] ![(3327229702349/10000000000000 : ℝ), (3846441825479/12500000000000 : ℝ), (7191233671917/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536154149/1250000000 : ℝ)|^4437 ≤ (3327229702349/10000000000000 : ℝ)^3413
        have hw : |(536154149/1250000000 : ℝ)|=(536154149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4039033497/10000000000 : ℝ)|^4437 ≤ (3846441825479/12500000000000 : ℝ)^3413
        have hw : |(4039033497/10000000000 : ℝ)|=(4039033497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4552971547/10000000000 : ℝ)|^4437 ≤ (7191233671917/20000000000000 : ℝ)^3413
        have hw : |(4552971547/10000000000 : ℝ)|=(4552971547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s3_4 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1931112639/10000000000 : ℝ)*x 0 + (162866559/312500000 : ℝ)*x 1 + (5442769831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1931112639/10000000000 : ℝ)^4437 ≤ (11790411493111/100000000000000 : ℝ)^3413 := by
    have hnat : (1931112639 : ℕ)^4437*100000000000000^3413 ≤ 11790411493111^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931112639 10000000000 11790411493111 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162866559/312500000 : ℝ)^4437 ≤ (42861580018719/100000000000000 : ℝ)^3413 := by
    have hnat : (162866559 : ℕ)^4437*100000000000000^3413 ≤ 42861580018719^3413*312500000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162866559 312500000 42861580018719 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442769831/10000000000 : ℝ)^4437 ≤ (5668501058983/12500000000000 : ℝ)^3413 := by
    have hnat : (5442769831 : ℕ)^4437*12500000000000^3413 ≤ 5668501058983^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442769831 10000000000 5668501058983 12500000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1931112639/10000000000 : ℝ), (162866559/312500000 : ℝ), (5442769831/10000000000 : ℝ)] ![(11790411493111/100000000000000 : ℝ), (42861580018719/100000000000000 : ℝ), (5668501058983/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1931112639/10000000000 : ℝ)|^4437 ≤ (11790411493111/100000000000000 : ℝ)^3413
        have hw : |(-1931112639/10000000000 : ℝ)|=(1931112639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162866559/312500000 : ℝ)|^4437 ≤ (42861580018719/100000000000000 : ℝ)^3413
        have hw : |(162866559/312500000 : ℝ)|=(162866559/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442769831/10000000000 : ℝ)|^4437 ≤ (5668501058983/12500000000000 : ℝ)^3413
        have hw : |(5442769831/10000000000 : ℝ)|=(5442769831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s3_5 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294294867/10000000000 : ℝ)*x 0 + (-227329801/1250000000 : ℝ)*x 1 + (5442769927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294294867/10000000000 : ℝ)^4437 ≤ (8749283052089/20000000000000 : ℝ)^3413 := by
    have hnat : (5294294867 : ℕ)^4437*20000000000000^3413 ≤ 8749283052089^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294294867 10000000000 8749283052089 20000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (227329801/1250000000 : ℝ)^4437 ≤ (5452787604319/50000000000000 : ℝ)^3413 := by
    have hnat : (227329801 : ℕ)^4437*50000000000000^3413 ≤ 5452787604319^3413*1250000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227329801 1250000000 5452787604319 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442769927/10000000000 : ℝ)^4437 ≤ (9069601902339/20000000000000 : ℝ)^3413 := by
    have hnat : (5442769927 : ℕ)^4437*20000000000000^3413 ≤ 9069601902339^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442769927 10000000000 9069601902339 20000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294294867/10000000000 : ℝ), (-227329801/1250000000 : ℝ), (5442769927/10000000000 : ℝ)] ![(8749283052089/20000000000000 : ℝ), (5452787604319/50000000000000 : ℝ), (9069601902339/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294294867/10000000000 : ℝ)|^4437 ≤ (8749283052089/20000000000000 : ℝ)^3413
        have hw : |(5294294867/10000000000 : ℝ)|=(5294294867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-227329801/1250000000 : ℝ)|^4437 ≤ (5452787604319/50000000000000 : ℝ)^3413
        have hw : |(-227329801/1250000000 : ℝ)|=(227329801/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442769927/10000000000 : ℝ)|^4437 ≤ (9069601902339/20000000000000 : ℝ)^3413
        have hw : |(5442769927/10000000000 : ℝ)|=(5442769927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s3_6 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661786877/1250000000 : ℝ)*x 0 + (5442769889/10000000000 : ℝ)*x 1 + (-113664891/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661786877/1250000000 : ℝ)^4437 ≤ (10936604215253/25000000000000 : ℝ)^3413 := by
    have hnat : (661786877 : ℕ)^4437*25000000000000^3413 ≤ 10936604215253^3413*1250000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661786877 1250000000 10936604215253 25000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442769889/10000000000 : ℝ)^4437 ≤ (708562642189/1562500000000 : ℝ)^3413 := by
    have hnat : (5442769889 : ℕ)^4437*1562500000000^3413 ≤ 708562642189^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442769889 10000000000 708562642189 1562500000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113664891/625000000 : ℝ)^4437 ≤ (10905574023691/100000000000000 : ℝ)^3413 := by
    have hnat : (113664891 : ℕ)^4437*100000000000000^3413 ≤ 10905574023691^3413*625000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113664891 625000000 10905574023691 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661786877/1250000000 : ℝ), (5442769889/10000000000 : ℝ), (-113664891/625000000 : ℝ)] ![(10936604215253/25000000000000 : ℝ), (708562642189/1562500000000 : ℝ), (10905574023691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661786877/1250000000 : ℝ)|^4437 ≤ (10936604215253/25000000000000 : ℝ)^3413
        have hw : |(661786877/1250000000 : ℝ)|=(661786877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442769889/10000000000 : ℝ)|^4437 ≤ (708562642189/1562500000000 : ℝ)^3413
        have hw : |(5442769889/10000000000 : ℝ)|=(5442769889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-113664891/625000000 : ℝ)|^4437 ≤ (10905574023691/100000000000000 : ℝ)^3413
        have hw : |(-113664891/625000000 : ℝ)|=(113664891/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s3_7 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (857862131/2000000000 : ℝ)*x 0 + (4550231087/10000000000 : ℝ)*x 1 + (4041794817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (857862131/2000000000 : ℝ)^4437 ≤ (33273078204641/100000000000000 : ℝ)^3413 := by
    have hnat : (857862131 : ℕ)^4437*100000000000000^3413 ≤ 33273078204641^3413*2000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857862131 2000000000 33273078204641 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4550231087/10000000000 : ℝ)^4437 ≤ (35928035371963/100000000000000 : ℝ)^3413 := by
    have hnat : (4550231087 : ℕ)^4437*100000000000000^3413 ≤ 35928035371963^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4550231087 10000000000 35928035371963 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4041794817/10000000000 : ℝ)^4437 ≤ (15399443208169/50000000000000 : ℝ)^3413 := by
    have hnat : (4041794817 : ℕ)^4437*50000000000000^3413 ≤ 15399443208169^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4041794817 10000000000 15399443208169 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(857862131/2000000000 : ℝ), (4550231087/10000000000 : ℝ), (4041794817/10000000000 : ℝ)] ![(33273078204641/100000000000000 : ℝ), (35928035371963/100000000000000 : ℝ), (15399443208169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(857862131/2000000000 : ℝ)|^4437 ≤ (33273078204641/100000000000000 : ℝ)^3413
        have hw : |(857862131/2000000000 : ℝ)|=(857862131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4550231087/10000000000 : ℝ)|^4437 ≤ (35928035371963/100000000000000 : ℝ)^3413
        have hw : |(4550231087/10000000000 : ℝ)|=(4550231087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4041794817/10000000000 : ℝ)|^4437 ≤ (15399443208169/50000000000000 : ℝ)^3413
        have hw : |(4041794817/10000000000 : ℝ)|=(4041794817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1470_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40008003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16179/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2019/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10641/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15583/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16179/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2019/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16179/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2019/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16179/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2019/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16179/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2019/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16179/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2019/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16179/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2019/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2019/20000 : ℝ) ^ (4435/1024 : ℝ) ≤ (4861049272524807/100000000000000000000 : ℝ) := by
    have hpowers : (2019/20000 : ℝ)^4435 ≤ (4861049272524807/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2019 : ℕ)^4435*100000000000000000000^1024 ≤ 4861049272524807^1024*20000^4435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2019 20000 4861049272524807 100000000000000000000 4435 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2019/20000 : ℝ)) (X := (4861049272524807/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16179/100000 : ℝ) ^ (4435/1024 : ℝ) ≤ (37490949884317843/100000000000000000000 : ℝ) := by
    have hpowers : (16179/100000 : ℝ)^4435 ≤ (37490949884317843/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16179 : ℕ)^4435*100000000000000000000^1024 ≤ 37490949884317843^1024*100000^4435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16179 100000 37490949884317843 100000000000000000000 4435 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16179/100000 : ℝ)) (X := (37490949884317843/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004861049272524807/50000000000000000000 : ℝ) ≤ (5000112232883089/5000000000000000 : ℝ) ^ (4435/1024 : ℝ) := by
    have hpowers : (50004861049272524807/50000000000000000000 : ℝ)^1024 ≤ (5000112232883089/5000000000000000 : ℝ)^4435 := by
      have hnat : (50004861049272524807 : ℕ)^1024*5000000000000000^4435 ≤ 5000112232883089^4435*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004861049272524807 50000000000000000000 5000112232883089 5000000000000000 1024 4435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000112232883089/5000000000000000 : ℝ)) (X := (50004861049272524807/50000000000000000000 : ℝ)) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000847039983136853/2000000000000000000 : ℝ) ≤ (10000977708807867/10000000000000000 : ℝ) ^ (4435/1024 : ℝ) := by
    have hpowers : (2000847039983136853/2000000000000000000 : ℝ)^1024 ≤ (10000977708807867/10000000000000000 : ℝ)^4435 := by
      have hnat : (2000847039983136853 : ℕ)^1024*10000000000000000^4435 ≤ 10000977708807867^4435*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000847039983136853 2000000000000000000 10000977708807867 10000000000000000 1024 4435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000977708807867/10000000000000000 : ℝ)) (X := (2000847039983136853/2000000000000000000 : ℝ)) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037490949884317843/50000000000000000000 : ℝ) ≤ (2500432737962389/2500000000000000 : ℝ) ^ (4435/1024 : ℝ) := by
    have hpowers : (50037490949884317843/50000000000000000000 : ℝ)^1024 ≤ (2500432737962389/2500000000000000 : ℝ)^4435 := by
      have hnat : (50037490949884317843 : ℕ)^1024*2500000000000000^4435 ≤ 2500432737962389^4435*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037490949884317843 50000000000000000000 2500432737962389 2500000000000000 1024 4435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500432737962389/2500000000000000 : ℝ)) (X := (50037490949884317843/50000000000000000000 : ℝ)) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4861049272524807/100000000000000000000 : ℝ) ≤ ((10137692945451621007/10140000000000000000 : ℝ)+2*(753243041689/608400000000000 : ℝ)*(2019/20000 : ℝ))^(4435/1024 : ℝ) := by
    rw [show (10137692945451621007/10140000000000000000 : ℝ)+2*(753243041689/608400000000000 : ℝ)*(2019/20000 : ℝ)=(5000112232883089/5000000000000000 : ℝ) by norm_num, show 1+2*(4861049272524807/100000000000000000000 : ℝ)=(50004861049272524807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37490949884317843/100000000000000000000 : ℝ)+(4861049272524807/100000000000000000000 : ℝ) ≤ ((10137692945451621007/10140000000000000000 : ℝ)+(753243041689/608400000000000 : ℝ)*((16179/100000 : ℝ)+(2019/20000 : ℝ)))^(4435/1024 : ℝ) := by
    rw [show (10137692945451621007/10140000000000000000 : ℝ)+(753243041689/608400000000000 : ℝ)*((16179/100000 : ℝ)+(2019/20000 : ℝ))=(10000977708807867/10000000000000000 : ℝ) by norm_num, show 1+(37490949884317843/100000000000000000000 : ℝ)+(4861049272524807/100000000000000000000 : ℝ)=(2000847039983136853/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37490949884317843/100000000000000000000 : ℝ) ≤ ((10137692945451621007/10140000000000000000 : ℝ)+2*(753243041689/608400000000000 : ℝ)*(16179/100000 : ℝ))^(4435/1024 : ℝ) := by
    rw [show (10137692945451621007/10140000000000000000 : ℝ)+2*(753243041689/608400000000000 : ℝ)*(16179/100000 : ℝ)=(2500432737962389/2500000000000000 : ℝ) by norm_num, show 1+2*(37490949884317843/100000000000000000000 : ℝ)=(50037490949884317843/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10137692945451621007/10140000000000000000 : ℝ)*(X 1 0+X 2 0)+(753243041689/608400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4435/1024 : ℝ)) (lo := (2019/20000 : ℝ)) (hi := (16179/100000 : ℝ)) (c := (10137692945451621007/10140000000000000000 : ℝ)) (alpha := (753243041689/608400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10137692945451621007/10140000000000000000 : ℝ)*(X 0 1+X 2 1)+(753243041689/608400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4435/1024 : ℝ)) (lo := (2019/20000 : ℝ)) (hi := (16179/100000 : ℝ)) (c := (10137692945451621007/10140000000000000000 : ℝ)) (alpha := (753243041689/608400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10137692945451621007/10140000000000000000 : ℝ)*(X 0 2+X 1 2)+(753243041689/608400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4435/1024 : ℝ)) (lo := (2019/20000 : ℝ)) (hi := (16179/100000 : ℝ)) (c := (10137692945451621007/10140000000000000000 : ℝ)) (alpha := (753243041689/608400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-482769343/2500000000 : ℝ)*X 0 0+(5444024867/10000000000 : ℝ)*X 0 1+(2605242253/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((41837377/78125000 : ℝ)*X 1 0+(-1025461981/5000000000 : ℝ)*X 1 1+(2605242093/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669398081/1250000000 : ℝ)*X 2 0+(2605241943/5000000000 : ℝ)*X 2 1+(-1025461919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((536154149/1250000000 : ℝ)*X 0 0+(4039033497/10000000000 : ℝ)*X 0 1+(4552971547/10000000000 : ℝ)*X 0 2+(536154149/1250000000 : ℝ)*X 1 0+(4039033497/10000000000 : ℝ)*X 1 1+(4552971547/10000000000 : ℝ)*X 1 2+(536154149/1250000000 : ℝ)*X 2 0+(4039033497/10000000000 : ℝ)*X 2 1+(4552971547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1931112639/10000000000 : ℝ)*X 0 0+(162866559/312500000 : ℝ)*X 0 1+(5442769831/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294294867/10000000000 : ℝ)*X 1 0+(-227329801/1250000000 : ℝ)*X 1 1+(5442769927/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661786877/1250000000 : ℝ)*X 2 0+(5442769889/10000000000 : ℝ)*X 2 1+(-113664891/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((857862131/2000000000 : ℝ)*X 0 0+(4550231087/10000000000 : ℝ)*X 0 1+(4041794817/10000000000 : ℝ)*X 0 2+(857862131/2000000000 : ℝ)*X 1 0+(4550231087/10000000000 : ℝ)*X 1 1+(4041794817/10000000000 : ℝ)*X 1 2+(857862131/2000000000 : ℝ)*X 2 0+(4550231087/10000000000 : ℝ)*X 2 1+(4041794817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (345232077906181124875022299/31687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (389865127/20000000000000 : ℝ)*(base19) + (497703761/25000000000000 : ℝ)*(base23) + (145634623/100000000000000 : ℝ)*(lower2) + (174289007/100000000000000 : ℝ)*(upper3) + (6788909/5000000000000 : ℝ)*(upper5) + (194617111974419/6250000000000 : ℝ)*(major0) + (194617111974419/6250000000000 : ℝ)*(major1) + (194617111974419/6250000000000 : ℝ)*(major2) + (107048465283809/2500000000000 : ℝ)*(sp0) + (2140981726622719/50000000000000 : ℝ)*(sp1) + (1070490852939007/25000000000000 : ℝ)*(sp2) + (1945769772790507/100000000000000 : ℝ)*(sp3) + (3348902339/12500000000000 : ℝ)*(sp4) + (12044656557/100000000000000 : ℝ)*(sp7) + (243222727180883/12500000000000 : ℝ)*(f.failure) + (66905709415173/1562500000000 : ℝ)*(f.sum) + (5669752981709/7605000000000000000000000000 : ℝ)*base65 + (803332594523859799/190125000000000000000000000000000 : ℝ)*base67 + (174554917931859799/190125000000000000000000000000000 : ℝ)*base69 + (1588448744957765201/190125000000000000000000000000000 : ℝ)*base72 + (17270342258077/3802500000000000000000000000 : ℝ)*base73 + (2904107196862640201/190125000000000000000000000000000 : ℝ)*base76 + (102742412249765201/190125000000000000000000000000000 : ℝ)*base78 + (1714486018110140201/190125000000000000000000000000000 : ℝ)*base80 + (12897623723347/3802500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1393351/312500000000000000000 : ℝ)*base90 + (1393351/312500000000000000000 : ℝ)*base92 + (1393351/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4941551195084964057557/422500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1610208439/100000000000000 : ℝ)*(base19) + (1029993859/50000000000000 : ℝ)*(base23) + (4008249/1562500000000 : ℝ)*(upper3) + (122701767/100000000000000 : ℝ)*(lower4) + (179126801/100000000000000 : ℝ)*(upper5) + (196720895211063/6250000000000 : ℝ)*(major0) + (196720895211063/6250000000000 : ℝ)*(major1) + (196720895211063/6250000000000 : ℝ)*(major2) + (11167976153/50000000000000 : ℝ)*(sp1) + (15350393231/50000000000000 : ℝ)*(sp2) + (4328252815376869/100000000000000 : ℝ)*(sp4) + (4328228869216123/100000000000000 : ℝ)*(sp5) + (67628438353167/1562500000000 : ℝ)*(sp6) + (196681544151117/10000000000000 : ℝ)*(sp7) + (196681544151117/10000000000000 : ℝ)*(f.failure) + (4328252815376869/100000000000000 : ℝ)*(f.sum) + (4356635109311/2535000000000000000000000000 : ℝ)*base65 + (296985763356199559/63375000000000000000000000000000 : ℝ)*base68 + (233746548539824559/63375000000000000000000000000000 : ℝ)*base70 + (53817114824425441/63375000000000000000000000000000 : ℝ)*base71 + (202255537157/1267500000000000000000000000 : ℝ)*base74 + (114643140636925441/63375000000000000000000000000000 : ℝ)*base75 + (300867626094199559/63375000000000000000000000000000 : ℝ)*base78 + (353770772638300441/63375000000000000000000000000000 : ℝ)*base79 + (1538833958833/1267500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1389351/250000000000000000000 : ℝ)*base89 + (1389351/250000000000000000000 : ℝ)*base91 + (1389351/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1470_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40008003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16179/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2019/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10641/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15583/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1470_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1470_s4_0 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-965891497/5000000000 : ℝ)*x 0 + (1087897859/2000000000 : ℝ)*x 1 + (1303638793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (965891497/5000000000 : ℝ)^4437 ≤ (5897866299879/50000000000000 : ℝ)^3413 := by
    have hnat : (965891497 : ℕ)^4437*50000000000000^3413 ≤ 5897866299879^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965891497 5000000000 5897866299879 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087897859/2000000000 : ℝ)^4437 ≤ (11328119582879/25000000000000 : ℝ)^3413 := by
    have hnat : (1087897859 : ℕ)^4437*25000000000000^3413 ≤ 11328119582879^3413*2000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087897859 2000000000 11328119582879 25000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303638793/2500000000 : ℝ)^4437 ≤ (42891789052867/100000000000000 : ℝ)^3413 := by
    have hnat : (1303638793 : ℕ)^4437*100000000000000^3413 ≤ 42891789052867^3413*2500000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303638793 2500000000 42891789052867 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-965891497/5000000000 : ℝ), (1087897859/2000000000 : ℝ), (1303638793/2500000000 : ℝ)] ![(5897866299879/50000000000000 : ℝ), (11328119582879/25000000000000 : ℝ), (42891789052867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-965891497/5000000000 : ℝ)|^4437 ≤ (5897866299879/50000000000000 : ℝ)^3413
        have hw : |(-965891497/5000000000 : ℝ)|=(965891497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087897859/2000000000 : ℝ)|^4437 ≤ (11328119582879/25000000000000 : ℝ)^3413
        have hw : |(1087897859/2000000000 : ℝ)|=(1087897859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303638793/2500000000 : ℝ)|^4437 ≤ (42891789052867/100000000000000 : ℝ)^3413
        have hw : |(1303638793/2500000000 : ℝ)|=(1303638793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s4_1 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167312801/312500000 : ℝ)*x 0 + (-2047103663/10000000000 : ℝ)*x 1 + (2607277623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167312801/312500000 : ℝ)^4437 ≤ (5548619655371/12500000000000 : ℝ)^3413 := by
    have hnat : (167312801 : ℕ)^4437*12500000000000^3413 ≤ 5548619655371^3413*312500000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167312801 312500000 5548619655371 12500000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2047103663/10000000000 : ℝ)^4437 ≤ (12719252900143/100000000000000 : ℝ)^3413 := by
    have hnat : (2047103663 : ℕ)^4437*100000000000000^3413 ≤ 12719252900143^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047103663 10000000000 12719252900143 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607277623/5000000000 : ℝ)^4437 ≤ (5361473730521/12500000000000 : ℝ)^3413 := by
    have hnat : (2607277623 : ℕ)^4437*12500000000000^3413 ≤ 5361473730521^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607277623 5000000000 5361473730521 12500000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167312801/312500000 : ℝ), (-2047103663/10000000000 : ℝ), (2607277623/5000000000 : ℝ)] ![(5548619655371/12500000000000 : ℝ), (12719252900143/100000000000000 : ℝ), (5361473730521/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167312801/312500000 : ℝ)|^4437 ≤ (5548619655371/12500000000000 : ℝ)^3413
        have hw : |(167312801/312500000 : ℝ)|=(167312801/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2047103663/10000000000 : ℝ)|^4437 ≤ (12719252900143/100000000000000 : ℝ)^3413
        have hw : |(-2047103663/10000000000 : ℝ)|=(2047103663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607277623/5000000000 : ℝ)|^4437 ≤ (5361473730521/12500000000000 : ℝ)^3413
        have hw : |(2607277623/5000000000 : ℝ)|=(2607277623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s4_2 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354009677/10000000000 : ℝ)*x 0 + (5214555183/10000000000 : ℝ)*x 1 + (-1023551843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354009677/10000000000 : ℝ)^4437 ≤ (4438895772799/10000000000000 : ℝ)^3413 := by
    have hnat : (5354009677 : ℕ)^4437*10000000000000^3413 ≤ 4438895772799^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354009677 10000000000 4438895772799 10000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214555183/10000000000 : ℝ)^4437 ≤ (42891789170493/100000000000000 : ℝ)^3413 := by
    have hnat : (5214555183 : ℕ)^4437*100000000000000^3413 ≤ 42891789170493^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214555183 10000000000 42891789170493 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1023551843/5000000000 : ℝ)^4437 ≤ (508770123437/4000000000000 : ℝ)^3413 := by
    have hnat : (1023551843 : ℕ)^4437*4000000000000^3413 ≤ 508770123437^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023551843 5000000000 508770123437 4000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354009677/10000000000 : ℝ), (5214555183/10000000000 : ℝ), (-1023551843/5000000000 : ℝ)] ![(4438895772799/10000000000000 : ℝ), (42891789170493/100000000000000 : ℝ), (508770123437/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354009677/10000000000 : ℝ)|^4437 ≤ (4438895772799/10000000000000 : ℝ)^3413
        have hw : |(5354009677/10000000000 : ℝ)|=(5354009677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214555183/10000000000 : ℝ)|^4437 ≤ (42891789170493/100000000000000 : ℝ)^3413
        have hw : |(5214555183/10000000000 : ℝ)|=(5214555183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1023551843/5000000000 : ℝ)|^4437 ≤ (508770123437/4000000000000 : ℝ)^3413
        have hw : |(-1023551843/5000000000 : ℝ)|=(1023551843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s4_3 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2144835457/5000000000 : ℝ)*x 0 + (4048451177/10000000000 : ℝ)*x 1 + (908690033/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144835457/5000000000 : ℝ)^4437 ≤ (665534226357/2000000000000 : ℝ)^3413 := by
    have hnat : (2144835457 : ℕ)^4437*2000000000000^3413 ≤ 665534226357^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144835457 5000000000 665534226357 2000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4048451177/10000000000 : ℝ)^4437 ≤ (15432421483477/50000000000000 : ℝ)^3413 := by
    have hnat : (4048451177 : ℕ)^4437*50000000000000^3413 ≤ 15432421483477^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4048451177 10000000000 15432421483477 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (908690033/2000000000 : ℝ)^4437 ≤ (17929222851443/50000000000000 : ℝ)^3413 := by
    have hnat : (908690033 : ℕ)^4437*50000000000000^3413 ≤ 17929222851443^3413*2000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908690033 2000000000 17929222851443 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2144835457/5000000000 : ℝ), (4048451177/10000000000 : ℝ), (908690033/2000000000 : ℝ)] ![(665534226357/2000000000000 : ℝ), (15432421483477/50000000000000 : ℝ), (17929222851443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2144835457/5000000000 : ℝ)|^4437 ≤ (665534226357/2000000000000 : ℝ)^3413
        have hw : |(2144835457/5000000000 : ℝ)|=(2144835457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4048451177/10000000000 : ℝ)|^4437 ≤ (15432421483477/50000000000000 : ℝ)^3413
        have hw : |(4048451177/10000000000 : ℝ)|=(4048451177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(908690033/2000000000 : ℝ)|^4437 ≤ (17929222851443/50000000000000 : ℝ)^3413
        have hw : |(908690033/2000000000 : ℝ)|=(908690033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s4_4 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-965907117/5000000000 : ℝ)*x 0 + (1043142203/2000000000 : ℝ)*x 1 + (543832503/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (965907117/5000000000 : ℝ)^4437 ≤ (2359196117681/20000000000000 : ℝ)^3413 := by
    have hnat : (965907117 : ℕ)^4437*20000000000000^3413 ≤ 2359196117681^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965907117 5000000000 2359196117681 20000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043142203/2000000000 : ℝ)^4437 ≤ (21452074595471/50000000000000 : ℝ)^3413 := by
    have hnat : (1043142203 : ℕ)^4437*50000000000000^3413 ≤ 21452074595471^3413*2000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043142203 2000000000 21452074595471 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543832503/1000000000 : ℝ)^4437 ≤ (4529987020011/10000000000000 : ℝ)^3413 := by
    have hnat : (543832503 : ℕ)^4437*10000000000000^3413 ≤ 4529987020011^3413*1000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543832503 1000000000 4529987020011 10000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-965907117/5000000000 : ℝ), (1043142203/2000000000 : ℝ), (543832503/1000000000 : ℝ)] ![(2359196117681/20000000000000 : ℝ), (21452074595471/50000000000000 : ℝ), (4529987020011/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-965907117/5000000000 : ℝ)|^4437 ≤ (2359196117681/20000000000000 : ℝ)^3413
        have hw : |(-965907117/5000000000 : ℝ)|=(965907117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043142203/2000000000 : ℝ)|^4437 ≤ (21452074595471/50000000000000 : ℝ)^3413
        have hw : |(1043142203/2000000000 : ℝ)|=(1043142203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543832503/1000000000 : ℝ)|^4437 ≤ (4529987020011/10000000000000 : ℝ)^3413
        have hw : |(543832503/1000000000 : ℝ)|=(543832503/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s4_5 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295367153/10000000000 : ℝ)*x 0 + (-28489591/156250000 : ℝ)*x 1 + (5438325229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295367153/10000000000 : ℝ)^4437 ≤ (43757934168617/100000000000000 : ℝ)^3413 := by
    have hnat : (5295367153 : ℕ)^4437*100000000000000^3413 ≤ 43757934168617^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295367153 10000000000 43757934168617 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28489591/156250000 : ℝ)^4437 ≤ (5471096726067/50000000000000 : ℝ)^3413 := by
    have hnat : (28489591 : ℕ)^4437*50000000000000^3413 ≤ 5471096726067^3413*156250000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28489591 156250000 5471096726067 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438325229/10000000000 : ℝ)^4437 ≤ (5662484044383/12500000000000 : ℝ)^3413 := by
    have hnat : (5438325229 : ℕ)^4437*12500000000000^3413 ≤ 5662484044383^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438325229 10000000000 5662484044383 12500000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295367153/10000000000 : ℝ), (-28489591/156250000 : ℝ), (5438325229/10000000000 : ℝ)] ![(43757934168617/100000000000000 : ℝ), (5471096726067/50000000000000 : ℝ), (5662484044383/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295367153/10000000000 : ℝ)|^4437 ≤ (43757934168617/100000000000000 : ℝ)^3413
        have hw : |(5295367153/10000000000 : ℝ)|=(5295367153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28489591/156250000 : ℝ)|^4437 ≤ (5471096726067/50000000000000 : ℝ)^3413
        have hw : |(-28489591/156250000 : ℝ)|=(28489591/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438325229/10000000000 : ℝ)|^4437 ≤ (5662484044383/12500000000000 : ℝ)^3413
        have hw : |(5438325229/10000000000 : ℝ)|=(5438325229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s4_6 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295367281/10000000000 : ℝ)*x 0 + (5438325213/10000000000 : ℝ)*x 1 + (-1823333671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295367281/10000000000 : ℝ)^4437 ≤ (10939483885921/25000000000000 : ℝ)^3413 := by
    have hnat : (5295367281 : ℕ)^4437*25000000000000^3413 ≤ 10939483885921^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295367281 10000000000 10939483885921 25000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438325213/10000000000 : ℝ)^4437 ≤ (22649936090901/50000000000000 : ℝ)^3413 := by
    have hnat : (5438325213 : ℕ)^4437*50000000000000^3413 ≤ 22649936090901^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438325213 10000000000 22649936090901 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1823333671/10000000000 : ℝ)^4437 ≤ (10942192258469/100000000000000 : ℝ)^3413 := by
    have hnat : (1823333671 : ℕ)^4437*100000000000000^3413 ≤ 10942192258469^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1823333671 10000000000 10942192258469 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295367281/10000000000 : ℝ), (5438325213/10000000000 : ℝ), (-1823333671/10000000000 : ℝ)] ![(10939483885921/25000000000000 : ℝ), (22649936090901/50000000000000 : ℝ), (10942192258469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295367281/10000000000 : ℝ)|^4437 ≤ (10939483885921/25000000000000 : ℝ)^3413
        have hw : |(5295367281/10000000000 : ℝ)|=(5295367281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438325213/10000000000 : ℝ)|^4437 ≤ (22649936090901/50000000000000 : ℝ)^3413
        have hw : |(5438325213/10000000000 : ℝ)|=(5438325213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1823333671/10000000000 : ℝ)|^4437 ≤ (10942192258469/100000000000000 : ℝ)^3413
        have hw : |(-1823333671/10000000000 : ℝ)|=(1823333671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s4_7 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2144870017/5000000000 : ℝ)*x 0 + (4540906951/10000000000 : ℝ)*x 1 + (810202631/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144870017/5000000000 : ℝ)^4437 ≤ (33277408384561/100000000000000 : ℝ)^3413 := by
    have hnat : (2144870017 : ℕ)^4437*100000000000000^3413 ≤ 33277408384561^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144870017 5000000000 33277408384561 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4540906951/10000000000 : ℝ)^4437 ≤ (2239522114339/6250000000000 : ℝ)^3413 := by
    have hnat : (4540906951 : ℕ)^4437*6250000000000^3413 ≤ 2239522114339^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540906951 10000000000 2239522114339 6250000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (810202631/2000000000 : ℝ)^4437 ≤ (30890237774341/100000000000000 : ℝ)^3413 := by
    have hnat : (810202631 : ℕ)^4437*100000000000000^3413 ≤ 30890237774341^3413*2000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      810202631 2000000000 30890237774341 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2144870017/5000000000 : ℝ), (4540906951/10000000000 : ℝ), (810202631/2000000000 : ℝ)] ![(33277408384561/100000000000000 : ℝ), (2239522114339/6250000000000 : ℝ), (30890237774341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2144870017/5000000000 : ℝ)|^4437 ≤ (33277408384561/100000000000000 : ℝ)^3413
        have hw : |(2144870017/5000000000 : ℝ)|=(2144870017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4540906951/10000000000 : ℝ)|^4437 ≤ (2239522114339/6250000000000 : ℝ)^3413
        have hw : |(4540906951/10000000000 : ℝ)|=(4540906951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(810202631/2000000000 : ℝ)|^4437 ≤ (30890237774341/100000000000000 : ℝ)^3413
        have hw : |(810202631/2000000000 : ℝ)|=(810202631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1470_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40008003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15583/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10641/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10729/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15583/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10641/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15583/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10641/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15583/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10641/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15583/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10641/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15583/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10641/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15583/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10641/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10641/100000 : ℝ) ^ (4435/1024 : ℝ) ≤ (1526679093066621/25000000000000000000 : ℝ) := by
    have hpowers : (10641/100000 : ℝ)^4435 ≤ (1526679093066621/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10641 : ℕ)^4435*25000000000000000000^1024 ≤ 1526679093066621^1024*100000^4435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10641 100000 1526679093066621 25000000000000000000 4435 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10641/100000 : ℝ)) (X := (1526679093066621/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15583/100000 : ℝ) ^ (4435/1024 : ℝ) ≤ (31866006116887613/100000000000000000000 : ℝ) := by
    have hpowers : (15583/100000 : ℝ)^4435 ≤ (31866006116887613/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15583 : ℕ)^4435*100000000000000000000^1024 ≤ 31866006116887613^1024*100000^4435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15583 100000 31866006116887613 100000000000000000000 4435 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15583/100000 : ℝ)) (X := (31866006116887613/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501526679093066621/12500000000000000000 : ℝ) ≤ (5000140991744907/5000000000000000 : ℝ) ^ (4435/1024 : ℝ) := by
    have hpowers : (12501526679093066621/12500000000000000000 : ℝ)^1024 ≤ (5000140991744907/5000000000000000 : ℝ)^4435 := by
      have hnat : (12501526679093066621 : ℕ)^1024*5000000000000000^4435 ≤ 5000140991744907^4435*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501526679093066621 12500000000000000000 5000140991744907 5000000000000000 1024 4435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000140991744907/5000000000000000 : ℝ)) (X := (12501526679093066621/12500000000000000000 : ℝ)) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037972722489154097/100000000000000000000 : ℝ) ≤ (10000876626629533/10000000000000000 : ℝ) ^ (4435/1024 : ℝ) := by
    have hpowers : (100037972722489154097/100000000000000000000 : ℝ)^1024 ≤ (10000876626629533/10000000000000000 : ℝ)^4435 := by
      have hnat : (100037972722489154097 : ℕ)^1024*10000000000000000^4435 ≤ 10000876626629533^4435*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037972722489154097 100000000000000000000 10000876626629533 10000000000000000 1024 4435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000876626629533/10000000000000000 : ℝ)) (X := (100037972722489154097/100000000000000000000 : ℝ)) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031866006116887613/50000000000000000000 : ℝ) ≤ (2500367817442313/2500000000000000 : ℝ) ^ (4435/1024 : ℝ) := by
    have hpowers : (50031866006116887613/50000000000000000000 : ℝ)^1024 ≤ (2500367817442313/2500000000000000 : ℝ)^4435 := by
      have hnat : (50031866006116887613 : ℕ)^1024*2500000000000000^4435 ≤ 2500367817442313^4435*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031866006116887613 50000000000000000000 2500367817442313 2500000000000000 1024 4435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500367817442313/2500000000000000 : ℝ)) (X := (50031866006116887613/50000000000000000000 : ℝ)) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1526679093066621/25000000000000000000 : ℝ) ≤ ((4940873836710716103/4942000000000000000 : ℝ)+2*(594643139719/494200000000000 : ℝ)*(10641/100000 : ℝ))^(4435/1024 : ℝ) := by
    rw [show (4940873836710716103/4942000000000000000 : ℝ)+2*(594643139719/494200000000000 : ℝ)*(10641/100000 : ℝ)=(5000140991744907/5000000000000000 : ℝ) by norm_num, show 1+2*(1526679093066621/25000000000000000000 : ℝ)=(12501526679093066621/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31866006116887613/100000000000000000000 : ℝ)+(1526679093066621/25000000000000000000 : ℝ) ≤ ((4940873836710716103/4942000000000000000 : ℝ)+(594643139719/494200000000000 : ℝ)*((15583/100000 : ℝ)+(10641/100000 : ℝ)))^(4435/1024 : ℝ) := by
    rw [show (4940873836710716103/4942000000000000000 : ℝ)+(594643139719/494200000000000 : ℝ)*((15583/100000 : ℝ)+(10641/100000 : ℝ))=(10000876626629533/10000000000000000 : ℝ) by norm_num, show 1+(31866006116887613/100000000000000000000 : ℝ)+(1526679093066621/25000000000000000000 : ℝ)=(100037972722489154097/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31866006116887613/100000000000000000000 : ℝ) ≤ ((4940873836710716103/4942000000000000000 : ℝ)+2*(594643139719/494200000000000 : ℝ)*(15583/100000 : ℝ))^(4435/1024 : ℝ) := by
    rw [show (4940873836710716103/4942000000000000000 : ℝ)+2*(594643139719/494200000000000 : ℝ)*(15583/100000 : ℝ)=(2500367817442313/2500000000000000 : ℝ) by norm_num, show 1+2*(31866006116887613/100000000000000000000 : ℝ)=(50031866006116887613/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4940873836710716103/4942000000000000000 : ℝ)*(X 1 0+X 2 0)+(594643139719/494200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4435/1024 : ℝ)) (lo := (10641/100000 : ℝ)) (hi := (15583/100000 : ℝ)) (c := (4940873836710716103/4942000000000000000 : ℝ)) (alpha := (594643139719/494200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4940873836710716103/4942000000000000000 : ℝ)*(X 0 1+X 2 1)+(594643139719/494200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4435/1024 : ℝ)) (lo := (10641/100000 : ℝ)) (hi := (15583/100000 : ℝ)) (c := (4940873836710716103/4942000000000000000 : ℝ)) (alpha := (594643139719/494200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4940873836710716103/4942000000000000000 : ℝ)*(X 0 2+X 1 2)+(594643139719/494200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4435/1024 : ℝ)) (lo := (10641/100000 : ℝ)) (hi := (15583/100000 : ℝ)) (c := (4940873836710716103/4942000000000000000 : ℝ)) (alpha := (594643139719/494200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-965891497/5000000000 : ℝ)*X 0 0+(1087897859/2000000000 : ℝ)*X 0 1+(1303638793/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167312801/312500000 : ℝ)*X 1 0+(-2047103663/10000000000 : ℝ)*X 1 1+(2607277623/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354009677/10000000000 : ℝ)*X 2 0+(5214555183/10000000000 : ℝ)*X 2 1+(-1023551843/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2144835457/5000000000 : ℝ)*X 0 0+(4048451177/10000000000 : ℝ)*X 0 1+(908690033/2000000000 : ℝ)*X 0 2+(2144835457/5000000000 : ℝ)*X 1 0+(4048451177/10000000000 : ℝ)*X 1 1+(908690033/2000000000 : ℝ)*X 1 2+(2144835457/5000000000 : ℝ)*X 2 0+(4048451177/10000000000 : ℝ)*X 2 1+(908690033/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-965907117/5000000000 : ℝ)*X 0 0+(1043142203/2000000000 : ℝ)*X 0 1+(543832503/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295367153/10000000000 : ℝ)*X 1 0+(-28489591/156250000 : ℝ)*X 1 1+(5438325229/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295367281/10000000000 : ℝ)*X 2 0+(5438325213/10000000000 : ℝ)*X 2 1+(-1823333671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2144870017/5000000000 : ℝ)*X 0 0+(4540906951/10000000000 : ℝ)*X 0 1+(810202631/2000000000 : ℝ)*X 0 2+(2144870017/5000000000 : ℝ)*X 1 0+(4540906951/10000000000 : ℝ)*X 1 1+(810202631/2000000000 : ℝ)*X 1 2+(2144870017/5000000000 : ℝ)*X 2 0+(4540906951/10000000000 : ℝ)*X 2 1+(810202631/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47153956574281840329471021/17650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9424321/2000000000000 : ℝ)*(base19) + (471267319/100000000000000 : ℝ)*(base23) + (19978477/100000000000000 : ℝ)*(lower2) + (354181/400000000000 : ℝ)*(upper3) + (45813801/100000000000000 : ℝ)*(upper5) + (3232987456587417/100000000000000 : ℝ)*(major0) + (3232987456587417/100000000000000 : ℝ)*(major1) + (3232987456587417/100000000000000 : ℝ)*(major2) + (4445754267420643/100000000000000 : ℝ)*(sp0) + (2222880693323561/50000000000000 : ℝ)*(sp1) + (1111440346648963/25000000000000 : ℝ)*(sp2) + (1010104605254971/50000000000000 : ℝ)*(sp3) + (237201329/3125000000000 : ℝ)*(sp4) + (3755747969/100000000000000 : ℝ)*(sp7) + (252526620782239/12500000000000 : ℝ)*(f.failure) + (4445761857863171/100000000000000 : ℝ)*(f.sum) + (48005591795423/24710000000000000000000000000 : ℝ)*base65 + (4187632818623705951/494200000000000000000000000000000 : ℝ)*base67 + (5432143466901105951/494200000000000000000000000000000 : ℝ)*base69 + (2553354110332294049/494200000000000000000000000000000 : ℝ)*base72 + (192205809787253/24710000000000000000000000000 : ℝ)*base73 + (232264680241905951/494200000000000000000000000000000 : ℝ)*base75 + (1240628827727705951/494200000000000000000000000000000 : ℝ)*base77 + (9179874025327505951/494200000000000000000000000000000 : ℝ)*base79 + (93011572515193/24710000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2133717/312500000000000000000 : ℝ)*base89 + (2133717/312500000000000000000 : ℝ)*base91 + (2133717/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (412523109848464920923536323/61775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (669561053/100000000000000 : ℝ)*(base19) + (44129667/4000000000000 : ℝ)*(base23) + (19052879/12500000000000 : ℝ)*(upper3) + (24347519/20000000000000 : ℝ)*(lower4) + (41118481/50000000000000 : ℝ)*(upper5) + (816667073068753/25000000000000 : ℝ)*(major0) + (816667073068753/25000000000000 : ℝ)*(major1) + (816667073068753/25000000000000 : ℝ)*(major2) + (10832609193/100000000000000 : ℝ)*(sp1) + (19429415943/100000000000000 : ℝ)*(sp2) + (2246038542116853/50000000000000 : ℝ)*(sp4) + (224603279103173/5000000000000 : ℝ)*(sp5) + (561507068947011/12500000000000 : ℝ)*(sp6) + (510314819430473/25000000000000 : ℝ)*(sp7) + (510314819430473/25000000000000 : ℝ)*(f.failure) + (2246038542116853/50000000000000 : ℝ)*(f.sum) + (4856259073103/6177500000000000000000000000 : ℝ)*base66 + (244522003683800441/123550000000000000000000000000000 : ℝ)*base68 + (953010147525299559/123550000000000000000000000000000 : ℝ)*base69 + (470911839879099559/123550000000000000000000000000000 : ℝ)*base71 + (27752957649201/12355000000000000000000000000 : ℝ)*base74 + (24708663149600441/123550000000000000000000000000000 : ℝ)*base76 + (273481314139449559/123550000000000000000000000000000 : ℝ)*base77 + (1080759591639549559/123550000000000000000000000000000 : ℝ)*base79 + (1389539190667/386093750000000000000000000 : ℝ)*base81 + (2924581/625000000000000000000 : ℝ)*base90 + (2924581/625000000000000000000 : ℝ)*base92 + (2924581/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1470_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40008003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15583/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10641/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10729/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1470_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1470_s5_0 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-965940983/5000000000 : ℝ)*x 0 + (5438841939/10000000000 : ℝ)*x 1 + (5215137289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (965940983/5000000000 : ℝ)^4437 ≤ (11796518261137/100000000000000 : ℝ)^3413 := by
    have hnat : (965940983 : ℕ)^4437*100000000000000^3413 ≤ 11796518261137^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965940983 5000000000 11796518261137 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438841939/10000000000 : ℝ)^4437 ≤ (9061093568691/20000000000000 : ℝ)^3413 := by
    have hnat : (5438841939 : ℕ)^4437*20000000000000^3413 ≤ 9061093568691^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438841939 10000000000 9061093568691 20000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215137289/10000000000 : ℝ)^4437 ≤ (42898013884227/100000000000000 : ℝ)^3413 := by
    have hnat : (5215137289 : ℕ)^4437*100000000000000^3413 ≤ 42898013884227^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215137289 10000000000 42898013884227 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-965940983/5000000000 : ℝ), (5438841939/10000000000 : ℝ), (5215137289/10000000000 : ℝ)] ![(11796518261137/100000000000000 : ℝ), (9061093568691/20000000000000 : ℝ), (42898013884227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-965940983/5000000000 : ℝ)|^4437 ≤ (11796518261137/100000000000000 : ℝ)^3413
        have hw : |(-965940983/5000000000 : ℝ)|=(965940983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438841939/10000000000 : ℝ)|^4437 ≤ (9061093568691/20000000000000 : ℝ)^3413
        have hw : |(5438841939/10000000000 : ℝ)|=(5438841939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215137289/10000000000 : ℝ)|^4437 ≤ (42898013884227/100000000000000 : ℝ)^3413
        have hw : |(5215137289/10000000000 : ℝ)|=(5215137289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s5_1 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353842011/10000000000 : ℝ)*x 0 + (-2046556861/10000000000 : ℝ)*x 1 + (1043027443/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353842011/10000000000 : ℝ)^4437 ≤ (44387150587571/100000000000000 : ℝ)^3413 := by
    have hnat : (5353842011 : ℕ)^4437*100000000000000^3413 ≤ 44387150587571^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353842011 10000000000 44387150587571 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2046556861/10000000000 : ℝ)^4437 ≤ (6357418152461/50000000000000 : ℝ)^3413 := by
    have hnat : (2046556861 : ℕ)^4437*50000000000000^3413 ≤ 6357418152461^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046556861 10000000000 6357418152461 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043027443/2000000000 : ℝ)^4437 ≤ (42898013092899/100000000000000 : ℝ)^3413 := by
    have hnat : (1043027443 : ℕ)^4437*100000000000000^3413 ≤ 42898013092899^3413*2000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043027443 2000000000 42898013092899 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353842011/10000000000 : ℝ), (-2046556861/10000000000 : ℝ), (1043027443/2000000000 : ℝ)] ![(44387150587571/100000000000000 : ℝ), (6357418152461/50000000000000 : ℝ), (42898013092899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353842011/10000000000 : ℝ)|^4437 ≤ (44387150587571/100000000000000 : ℝ)^3413
        have hw : |(5353842011/10000000000 : ℝ)|=(5353842011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2046556861/10000000000 : ℝ)|^4437 ≤ (6357418152461/50000000000000 : ℝ)^3413
        have hw : |(-2046556861/10000000000 : ℝ)|=(2046556861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043027443/2000000000 : ℝ)|^4437 ≤ (42898013092899/100000000000000 : ℝ)^3413
        have hw : |(1043027443/2000000000 : ℝ)|=(1043027443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s5_2 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676921119/5000000000 : ℝ)*x 0 + (5215136929/10000000000 : ℝ)*x 1 + (-255819617/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676921119/5000000000 : ℝ)^4437 ≤ (22193576517107/50000000000000 : ℝ)^3413 := by
    have hnat : (2676921119 : ℕ)^4437*50000000000000^3413 ≤ 22193576517107^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676921119 5000000000 22193576517107 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215136929/10000000000 : ℝ)^4437 ≤ (1715920401381/4000000000000 : ℝ)^3413 := by
    have hnat : (5215136929 : ℕ)^4437*4000000000000^3413 ≤ 1715920401381^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215136929 10000000000 1715920401381 4000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (255819617/1250000000 : ℝ)^4437 ≤ (12714836910683/100000000000000 : ℝ)^3413 := by
    have hnat : (255819617 : ℕ)^4437*100000000000000^3413 ≤ 12714836910683^3413*1250000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255819617 1250000000 12714836910683 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676921119/5000000000 : ℝ), (5215136929/10000000000 : ℝ), (-255819617/1250000000 : ℝ)] ![(22193576517107/50000000000000 : ℝ), (1715920401381/4000000000000 : ℝ), (12714836910683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676921119/5000000000 : ℝ)|^4437 ≤ (22193576517107/50000000000000 : ℝ)^3413
        have hw : |(2676921119/5000000000 : ℝ)|=(2676921119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215136929/10000000000 : ℝ)|^4437 ≤ (1715920401381/4000000000000 : ℝ)^3413
        have hw : |(5215136929/10000000000 : ℝ)|=(5215136929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-255819617/1250000000 : ℝ)|^4437 ≤ (12714836910683/100000000000000 : ℝ)^3413
        have hw : |(-255819617/1250000000 : ℝ)|=(255819617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s5_3 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107243299/250000000 : ℝ)*x 0 + (4049796761/10000000000 : ℝ)*x 1 + (181683609/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107243299/250000000 : ℝ)^4437 ≤ (2079832934943/6250000000000 : ℝ)^3413 := by
    have hnat : (107243299 : ℕ)^4437*6250000000000^3413 ≤ 2079832934943^3413*250000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107243299 250000000 2079832934943 6250000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4049796761/10000000000 : ℝ)^4437 ≤ (15439090023723/50000000000000 : ℝ)^3413 := by
    have hnat : (4049796761 : ℕ)^4437*50000000000000^3413 ≤ 15439090023723^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4049796761 10000000000 15439090023723 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181683609/400000000 : ℝ)^4437 ≤ (2240280811031/6250000000000 : ℝ)^3413 := by
    have hnat : (181683609 : ℕ)^4437*6250000000000^3413 ≤ 2240280811031^3413*400000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181683609 400000000 2240280811031 6250000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107243299/250000000 : ℝ), (4049796761/10000000000 : ℝ), (181683609/400000000 : ℝ)] ![(2079832934943/6250000000000 : ℝ), (15439090023723/50000000000000 : ℝ), (2240280811031/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107243299/250000000 : ℝ)|^4437 ≤ (2079832934943/6250000000000 : ℝ)^3413
        have hw : |(107243299/250000000 : ℝ)|=(107243299/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4049796761/10000000000 : ℝ)|^4437 ≤ (15439090023723/50000000000000 : ℝ)^3413
        have hw : |(4049796761/10000000000 : ℝ)|=(4049796761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(181683609/400000000 : ℝ)|^4437 ≤ (2240280811031/6250000000000 : ℝ)^3413
        have hw : |(181683609/400000000 : ℝ)|=(181683609/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s5_4 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-120744547/625000000 : ℝ)*x 0 + (5216280321/10000000000 : ℝ)*x 1 + (5437690579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (120744547/625000000 : ℝ)^4437 ≤ (460811041/3906250000 : ℝ)^3413 := by
    have hnat : (120744547 : ℕ)^4437*3906250000^3413 ≤ 460811041^3413*625000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120744547 625000000 460811041 3906250000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216280321/10000000000 : ℝ)^4437 ≤ (42910237431249/100000000000000 : ℝ)^3413 := by
    have hnat : (5216280321 : ℕ)^4437*100000000000000^3413 ≤ 42910237431249^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216280321 10000000000 42910237431249 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437690579/10000000000 : ℝ)^4437 ≤ (9058599980903/20000000000000 : ℝ)^3413 := by
    have hnat : (5437690579 : ℕ)^4437*20000000000000^3413 ≤ 9058599980903^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437690579 10000000000 9058599980903 20000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-120744547/625000000 : ℝ), (5216280321/10000000000 : ℝ), (5437690579/10000000000 : ℝ)] ![(460811041/3906250000 : ℝ), (42910237431249/100000000000000 : ℝ), (9058599980903/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-120744547/625000000 : ℝ)|^4437 ≤ (460811041/3906250000 : ℝ)^3413
        have hw : |(-120744547/625000000 : ℝ)|=(120744547/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216280321/10000000000 : ℝ)|^4437 ≤ (42910237431249/100000000000000 : ℝ)^3413
        have hw : |(5216280321/10000000000 : ℝ)|=(5216280321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437690579/10000000000 : ℝ)|^4437 ≤ (9058599980903/20000000000000 : ℝ)^3413
        have hw : |(5437690579/10000000000 : ℝ)|=(5437690579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s5_5 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647760281/5000000000 : ℝ)*x 0 + (-912001769/5000000000 : ℝ)*x 1 + (1087538101/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647760281/5000000000 : ℝ)^4437 ≤ (2187979110213/5000000000000 : ℝ)^3413 := by
    have hnat : (2647760281 : ℕ)^4437*5000000000000^3413 ≤ 2187979110213^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647760281 5000000000 2187979110213 5000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (912001769/5000000000 : ℝ)^4437 ≤ (2736854668229/25000000000000 : ℝ)^3413 := by
    have hnat : (912001769 : ℕ)^4437*25000000000000^3413 ≤ 2736854668229^3413*5000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912001769 5000000000 2736854668229 25000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087538101/2000000000 : ℝ)^4437 ≤ (45292999103203/100000000000000 : ℝ)^3413 := by
    have hnat : (1087538101 : ℕ)^4437*100000000000000^3413 ≤ 45292999103203^3413*2000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087538101 2000000000 45292999103203 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647760281/5000000000 : ℝ), (-912001769/5000000000 : ℝ), (1087538101/2000000000 : ℝ)] ![(2187979110213/5000000000000 : ℝ), (2736854668229/25000000000000 : ℝ), (45292999103203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647760281/5000000000 : ℝ)|^4437 ≤ (2187979110213/5000000000000 : ℝ)^3413
        have hw : |(2647760281/5000000000 : ℝ)|=(2647760281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-912001769/5000000000 : ℝ)|^4437 ≤ (2736854668229/25000000000000 : ℝ)^3413
        have hw : |(-912001769/5000000000 : ℝ)|=(912001769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087538101/2000000000 : ℝ)|^4437 ≤ (45292999103203/100000000000000 : ℝ)^3413
        have hw : |(1087538101/2000000000 : ℝ)|=(1087538101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s5_6 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295520553/10000000000 : ℝ)*x 0 + (5437690541/10000000000 : ℝ)*x 1 + (-1824003501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295520553/10000000000 : ℝ)^4437 ≤ (1750383284303/4000000000000 : ℝ)^3413 := by
    have hnat : (5295520553 : ℕ)^4437*4000000000000^3413 ≤ 1750383284303^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295520553 10000000000 1750383284303 4000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437690541/10000000000 : ℝ)^4437 ≤ (4529299949303/10000000000000 : ℝ)^3413 := by
    have hnat : (5437690541 : ℕ)^4437*10000000000000^3413 ≤ 4529299949303^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437690541 10000000000 4529299949303 10000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1824003501/10000000000 : ℝ)^4437 ≤ (547370919211/5000000000000 : ℝ)^3413 := by
    have hnat : (1824003501 : ℕ)^4437*5000000000000^3413 ≤ 547370919211^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824003501 10000000000 547370919211 5000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295520553/10000000000 : ℝ), (5437690541/10000000000 : ℝ), (-1824003501/10000000000 : ℝ)] ![(1750383284303/4000000000000 : ℝ), (4529299949303/10000000000000 : ℝ), (547370919211/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295520553/10000000000 : ℝ)|^4437 ≤ (1750383284303/4000000000000 : ℝ)^3413
        have hw : |(5295520553/10000000000 : ℝ)|=(5295520553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437690541/10000000000 : ℝ)|^4437 ≤ (4529299949303/10000000000000 : ℝ)^3413
        have hw : |(5437690541/10000000000 : ℝ)|=(5437690541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1824003501/10000000000 : ℝ)|^4437 ≤ (547370919211/5000000000000 : ℝ)^3413
        have hw : |(-1824003501/10000000000 : ℝ)|=(1824003501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1470_s5_7 (p : ℝ) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4289799979/10000000000 : ℝ)*x 0 + (4539574831/10000000000 : ℝ)*x 1 + (4052330583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4289799979/10000000000 : ℝ)^4437 ≤ (33278012925251/100000000000000 : ℝ)^3413 := by
    have hnat : (4289799979 : ℕ)^4437*100000000000000^3413 ≤ 33278012925251^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4289799979 10000000000 33278012925251 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4539574831/10000000000 : ℝ)^4437 ≤ (35818688814509/100000000000000 : ℝ)^3413 := by
    have hnat : (4539574831 : ℕ)^4437*100000000000000^3413 ≤ 35818688814509^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4539574831 10000000000 35818688814509 100000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4052330583/10000000000 : ℝ)^4437 ≤ (15451649122279/50000000000000 : ℝ)^3413 := by
    have hnat : (4052330583 : ℕ)^4437*50000000000000^3413 ≤ 15451649122279^3413*10000000000^4437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4052330583 10000000000 15451649122279 50000000000000 4437 3413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4437/1024 : ℝ)) 4437 3413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4289799979/10000000000 : ℝ), (4539574831/10000000000 : ℝ), (4052330583/10000000000 : ℝ)] ![(33278012925251/100000000000000 : ℝ), (35818688814509/100000000000000 : ℝ), (15451649122279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4289799979/10000000000 : ℝ)|^4437 ≤ (33278012925251/100000000000000 : ℝ)^3413
        have hw : |(4289799979/10000000000 : ℝ)|=(4289799979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4539574831/10000000000 : ℝ)|^4437 ≤ (35818688814509/100000000000000 : ℝ)^3413
        have hw : |(4539574831/10000000000 : ℝ)|=(4539574831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4052330583/10000000000 : ℝ)|^4437 ≤ (15451649122279/50000000000000 : ℝ)^3413
        have hw : |(4052330583/10000000000 : ℝ)|=(4052330583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1470_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40008003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10729/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10741/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (619/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10729/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10729/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10729/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10729/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10729/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10729/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10729/100000 : ℝ) ^ (4435/1024 : ℝ) ≤ (1582118772805561/25000000000000000000 : ℝ) := by
    have hpowers : (10729/100000 : ℝ)^4435 ≤ (1582118772805561/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10729 : ℕ)^4435*25000000000000000000^1024 ≤ 1582118772805561^1024*100000^4435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10729 100000 1582118772805561 25000000000000000000 4435 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10729/100000 : ℝ)) (X := (1582118772805561/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4435/1024 : ℝ) ≤ (15516562839935211/50000000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4435 ≤ (15516562839935211/50000000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4435*50000000000000000000^1024 ≤ 15516562839935211^1024*3125^4435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 15516562839935211 50000000000000000000 4435 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (15516562839935211/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501582118772805561/12500000000000000000 : ℝ) ≤ (10000292222913153/10000000000000000 : ℝ) ^ (4435/1024 : ℝ) := by
    have hpowers : (12501582118772805561/12500000000000000000 : ℝ)^1024 ≤ (10000292222913153/10000000000000000 : ℝ)^4435 := by
      have hnat : (12501582118772805561 : ℕ)^1024*10000000000000000^4435 ≤ 10000292222913153^4435*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501582118772805561 12500000000000000000 10000292222913153 10000000000000000 1024 4435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000292222913153/10000000000000000 : ℝ)) (X := (12501582118772805561/12500000000000000000 : ℝ)) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018680800385546333/50000000000000000000 : ℝ) ≤ (2500215630121827/2500000000000000 : ℝ) ^ (4435/1024 : ℝ) := by
    have hpowers : (50018680800385546333/50000000000000000000 : ℝ)^1024 ≤ (2500215630121827/2500000000000000 : ℝ)^4435 := by
      have hnat : (50018680800385546333 : ℕ)^1024*2500000000000000^4435 ≤ 2500215630121827^4435*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018680800385546333 50000000000000000000 2500215630121827 2500000000000000 1024 4435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500215630121827/2500000000000000 : ℝ)) (X := (50018680800385546333/50000000000000000000 : ℝ)) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015516562839935211/25000000000000000000 : ℝ) ≤ (10001432818061463/10000000000000000 : ℝ) ^ (4435/1024 : ℝ) := by
    have hpowers : (25015516562839935211/25000000000000000000 : ℝ)^1024 ≤ (10001432818061463/10000000000000000 : ℝ)^4435 := by
      have hnat : (25015516562839935211 : ℕ)^1024*10000000000000000^4435 ≤ 10001432818061463^4435*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015516562839935211 25000000000000000000 10001432818061463 10000000000000000 1024 4435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001432818061463/10000000000000000 : ℝ)) (X := (25015516562839935211/25000000000000000000 : ℝ)) (by norm_num) 4435 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1582118772805561/25000000000000000000 : ℝ) ≤ ((47579153243497477137/47590000000000000000 : ℝ)+2*(114059514831/95180000000000 : ℝ)*(10729/100000 : ℝ))^(4435/1024 : ℝ) := by
    rw [show (47579153243497477137/47590000000000000000 : ℝ)+2*(114059514831/95180000000000 : ℝ)*(10729/100000 : ℝ)=(10000292222913153/10000000000000000 : ℝ) by norm_num, show 1+2*(1582118772805561/25000000000000000000 : ℝ)=(12501582118772805561/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15516562839935211/50000000000000000000 : ℝ)+(1582118772805561/25000000000000000000 : ℝ) ≤ ((47579153243497477137/47590000000000000000 : ℝ)+(114059514831/95180000000000 : ℝ)*((484/3125 : ℝ)+(10729/100000 : ℝ)))^(4435/1024 : ℝ) := by
    rw [show (47579153243497477137/47590000000000000000 : ℝ)+(114059514831/95180000000000 : ℝ)*((484/3125 : ℝ)+(10729/100000 : ℝ))=(2500215630121827/2500000000000000 : ℝ) by norm_num, show 1+(15516562839935211/50000000000000000000 : ℝ)+(1582118772805561/25000000000000000000 : ℝ)=(50018680800385546333/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15516562839935211/50000000000000000000 : ℝ) ≤ ((47579153243497477137/47590000000000000000 : ℝ)+2*(114059514831/95180000000000 : ℝ)*(484/3125 : ℝ))^(4435/1024 : ℝ) := by
    rw [show (47579153243497477137/47590000000000000000 : ℝ)+2*(114059514831/95180000000000 : ℝ)*(484/3125 : ℝ)=(10001432818061463/10000000000000000 : ℝ) by norm_num, show 1+2*(15516562839935211/50000000000000000000 : ℝ)=(25015516562839935211/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (47579153243497477137/47590000000000000000 : ℝ)*(X 1 0+X 2 0)+(114059514831/95180000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4435/1024 : ℝ)) (lo := (10729/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (47579153243497477137/47590000000000000000 : ℝ)) (alpha := (114059514831/95180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (47579153243497477137/47590000000000000000 : ℝ)*(X 0 1+X 2 1)+(114059514831/95180000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4435/1024 : ℝ)) (lo := (10729/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (47579153243497477137/47590000000000000000 : ℝ)) (alpha := (114059514831/95180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (47579153243497477137/47590000000000000000 : ℝ)*(X 0 2+X 1 2)+(114059514831/95180000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4435/1024 : ℝ)) (lo := (10729/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (47579153243497477137/47590000000000000000 : ℝ)) (alpha := (114059514831/95180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-965940983/5000000000 : ℝ)*X 0 0+(5438841939/10000000000 : ℝ)*X 0 1+(5215137289/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353842011/10000000000 : ℝ)*X 1 0+(-2046556861/10000000000 : ℝ)*X 1 1+(1043027443/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676921119/5000000000 : ℝ)*X 2 0+(5215136929/10000000000 : ℝ)*X 2 1+(-255819617/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((107243299/250000000 : ℝ)*X 0 0+(4049796761/10000000000 : ℝ)*X 0 1+(181683609/400000000 : ℝ)*X 0 2+(107243299/250000000 : ℝ)*X 1 0+(4049796761/10000000000 : ℝ)*X 1 1+(181683609/400000000 : ℝ)*X 1 2+(107243299/250000000 : ℝ)*X 2 0+(4049796761/10000000000 : ℝ)*X 2 1+(181683609/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-120744547/625000000 : ℝ)*X 0 0+(5216280321/10000000000 : ℝ)*X 0 1+(5437690579/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647760281/5000000000 : ℝ)*X 1 0+(-912001769/5000000000 : ℝ)*X 1 1+(1087538101/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295520553/10000000000 : ℝ)*X 2 0+(5437690541/10000000000 : ℝ)*X 2 1+(-1824003501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4289799979/10000000000 : ℝ)*X 0 0+(4539574831/10000000000 : ℝ)*X 0 1+(4052330583/10000000000 : ℝ)*X 0 2+(4289799979/10000000000 : ℝ)*X 1 0+(4539574831/10000000000 : ℝ)*X 1 1+(4052330583/10000000000 : ℝ)*X 1 2+(4289799979/10000000000 : ℝ)*X 2 0+(4539574831/10000000000 : ℝ)*X 2 1+(4052330583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1470_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15797548794482127422525473383/2379500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8498091/625000000000 : ℝ)*(base19) + (189666923/12500000000000 : ℝ)*(base23) + (188239353/100000000000000 : ℝ)*(upper3) + (17075519/100000000000000 : ℝ)*(upper4) + (127846611/100000000000000 : ℝ)*(upper5) + (3250772585957347/100000000000000 : ℝ)*(major0) + (3250772585957347/100000000000000 : ℝ)*(major1) + (3250772585957347/100000000000000 : ℝ)*(major2) + (2235099606668181/50000000000000 : ℝ)*(sp0) + (447021714233531/10000000000000 : ℝ)*(sp1) + (2235108492347243/50000000000000 : ℝ)*(sp2) + (1015658464306697/50000000000000 : ℝ)*(sp3) + (19288693507/100000000000000 : ℝ)*(sp4) + (9519970747/100000000000000 : ℝ)*(sp7) + (1015663224292071/50000000000000 : ℝ)*(f.failure) + (447021850202987/10000000000000 : ℝ)*(f.sum) + (5106456355383/2379500000000000000000000000 : ℝ)*base66 + (9617270833764175539/4759000000000000000000000000000000 : ℝ)*base67 + (31024418474670175539/4759000000000000000000000000000000 : ℝ)*base69 + (20061983803848824461/4759000000000000000000000000000000 : ℝ)*base72 + (1971431992261/2379500000000000000000000000 : ℝ)*base74 + (5366800703109175539/4759000000000000000000000000000000 : ℝ)*base75 + (16948604400670824461/4759000000000000000000000000000000 : ℝ)*base78 + (11533187939553175539/4759000000000000000000000000000000 : ℝ)*base79 + (2674132783453/1189750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (11944213/1250000000000000000000 : ℝ)*base89 + (11944213/1250000000000000000000 : ℝ)*base91 + (11944213/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2600805281280609644106838881/237950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1917426071/100000000000000 : ℝ)*(base19) + (411888481/20000000000000 : ℝ)*(base23) + (224156573/100000000000000 : ℝ)*(upper3) + (32682663/50000000000000 : ℝ)*(lower4) + (59156629/25000000000000 : ℝ)*(upper5) + (656886052488229/20000000000000 : ℝ)*(major0) + (656886052488229/20000000000000 : ℝ)*(major1) + (656886052488229/20000000000000 : ℝ)*(major2) + (6933288109/25000000000000 : ℝ)*(sp1) + (941161123/3125000000000 : ℝ)*(sp2) + (141140683503317/3125000000000 : ℝ)*(sp4) + (1129118055381909/25000000000000 : ℝ)*(sp5) + (4516469695507803/100000000000000 : ℝ)*(sp6) + (513089572110289/25000000000000 : ℝ)*(sp7) + (513089572110289/25000000000000 : ℝ)*(f.failure) + (141140683503317/3125000000000 : ℝ)*(f.sum) + (26924791686429/4759000000000000000000000000 : ℝ)*base66 + (5609294671690620373/951800000000000000000000000000000 : ℝ)*base67 + (811504787144579627/951800000000000000000000000000000 : ℝ)*base70 + (1559919543925020373/951800000000000000000000000000000 : ℝ)*base71 + (7062474683847/4759000000000000000000000000 : ℝ)*base73 + (19169647323876220373/951800000000000000000000000000000 : ℝ)*base75 + (5048685717596820373/951800000000000000000000000000000 : ℝ)*base77 + (4581769708303220373/951800000000000000000000000000000 : ℝ)*base79 + (3798578522049/1189750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2392867/625000000000000000000 : ℝ)*base89 + (2392867/625000000000000000000 : ℝ)*base91 + (2392867/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1470_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40008003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10729/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10741/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (619/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1470_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1470_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40008003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16179/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2019/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10741/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (619/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1470_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1470_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1470_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4435/1024 : ℝ) ≤ p) (hpb : p ≤ (4437/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40008003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16179/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2019/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10741/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (619/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1470_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

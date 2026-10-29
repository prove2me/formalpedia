-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1506_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:54:16.121892+00:00
-- url     : https://prove2.me/submissions/058ba0ec-1b7d-4102-84bd-514dd5f0851d

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
theorem support_rectangle_w1506_s3_0 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1876382049/10000000000 : ℝ)*x 0 + (217500981/400000000 : ℝ)*x 1 + (651771497/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1876382049/10000000000 : ℝ)^4509 ≤ (11476269734951/100000000000000 : ℝ)^3485 := by
    have hnat : (1876382049 : ℕ)^4509*100000000000000^3485 ≤ 11476269734951^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876382049 10000000000 11476269734951 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217500981/400000000 : ℝ)^4509 ≤ (1818502812781/4000000000000 : ℝ)^3485 := by
    have hnat : (217500981 : ℕ)^4509*4000000000000^3485 ≤ 1818502812781^3485*400000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217500981 400000000 1818502812781 4000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651771497/1250000000 : ℝ)^4509 ≤ (10765289980191/25000000000000 : ℝ)^3485 := by
    have hnat : (651771497 : ℕ)^4509*25000000000000^3485 ≤ 10765289980191^3485*1250000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651771497 1250000000 10765289980191 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1876382049/10000000000 : ℝ), (217500981/400000000 : ℝ), (651771497/1250000000 : ℝ)] ![(11476269734951/100000000000000 : ℝ), (1818502812781/4000000000000 : ℝ), (10765289980191/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1876382049/10000000000 : ℝ)|^4509 ≤ (11476269734951/100000000000000 : ℝ)^3485
        have hw : |(-1876382049/10000000000 : ℝ)|=(1876382049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217500981/400000000 : ℝ)|^4509 ≤ (1818502812781/4000000000000 : ℝ)^3485
        have hw : |(217500981/400000000 : ℝ)|=(217500981/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(651771497/1250000000 : ℝ)|^4509 ≤ (10765289980191/25000000000000 : ℝ)^3485
        have hw : |(651771497/1250000000 : ℝ)|=(651771497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s3_1 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352839427/10000000000 : ℝ)*x 0 + (-1990870139/10000000000 : ℝ)*x 1 + (5214171929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352839427/10000000000 : ℝ)^4509 ≤ (44548586125121/100000000000000 : ℝ)^3485 := by
    have hnat : (5352839427 : ℕ)^4509*100000000000000^3485 ≤ 44548586125121^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352839427 10000000000 44548586125121 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1990870139/10000000000 : ℝ)^4509 ≤ (12390254436687/100000000000000 : ℝ)^3485 := by
    have hnat : (1990870139 : ℕ)^4509*100000000000000^3485 ≤ 12390254436687^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990870139 10000000000 12390254436687 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214171929/10000000000 : ℝ)^4509 ≤ (21530579709283/50000000000000 : ℝ)^3485 := by
    have hnat : (5214171929 : ℕ)^4509*50000000000000^3485 ≤ 21530579709283^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214171929 10000000000 21530579709283 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352839427/10000000000 : ℝ), (-1990870139/10000000000 : ℝ), (5214171929/10000000000 : ℝ)] ![(44548586125121/100000000000000 : ℝ), (12390254436687/100000000000000 : ℝ), (21530579709283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352839427/10000000000 : ℝ)|^4509 ≤ (44548586125121/100000000000000 : ℝ)^3485
        have hw : |(5352839427/10000000000 : ℝ)|=(5352839427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1990870139/10000000000 : ℝ)|^4509 ≤ (12390254436687/100000000000000 : ℝ)^3485
        have hw : |(-1990870139/10000000000 : ℝ)|=(1990870139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214171929/10000000000 : ℝ)|^4509 ≤ (21530579709283/50000000000000 : ℝ)^3485
        have hw : |(5214171929/10000000000 : ℝ)|=(5214171929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s3_2 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352839401/10000000000 : ℝ)*x 0 + (5214171959/10000000000 : ℝ)*x 1 + (-995435067/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352839401/10000000000 : ℝ)^4509 ≤ (22274292922579/50000000000000 : ℝ)^3485 := by
    have hnat : (5352839401 : ℕ)^4509*50000000000000^3485 ≤ 22274292922579^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352839401 10000000000 22274292922579 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214171959/10000000000 : ℝ)^4509 ≤ (21530579869559/50000000000000 : ℝ)^3485 := by
    have hnat : (5214171959 : ℕ)^4509*50000000000000^3485 ≤ 21530579869559^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214171959 10000000000 21530579869559 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (995435067/5000000000 : ℝ)^4509 ≤ (6195127198213/50000000000000 : ℝ)^3485 := by
    have hnat : (995435067 : ℕ)^4509*50000000000000^3485 ≤ 6195127198213^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995435067 5000000000 6195127198213 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352839401/10000000000 : ℝ), (5214171959/10000000000 : ℝ), (-995435067/5000000000 : ℝ)] ![(22274292922579/50000000000000 : ℝ), (21530579869559/50000000000000 : ℝ), (6195127198213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352839401/10000000000 : ℝ)|^4509 ≤ (22274292922579/50000000000000 : ℝ)^3485
        have hw : |(5352839401/10000000000 : ℝ)|=(5352839401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214171959/10000000000 : ℝ)|^4509 ≤ (21530579869559/50000000000000 : ℝ)^3485
        have hw : |(5214171959/10000000000 : ℝ)|=(5214171959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-995435067/5000000000 : ℝ)|^4509 ≤ (6195127198213/50000000000000 : ℝ)^3485
        have hw : |(-995435067/5000000000 : ℝ)|=(995435067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s3_3 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068060061/2500000000 : ℝ)*x 0 + (805284841/2000000000 : ℝ)*x 1 + (2265377243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068060061/2500000000 : ℝ)^4509 ≤ (8318997049603/25000000000000 : ℝ)^3485 := by
    have hnat : (1068060061 : ℕ)^4509*25000000000000^3485 ≤ 8318997049603^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068060061 2500000000 8318997049603 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (805284841/2000000000 : ℝ)^4509 ≤ (30820008587481/100000000000000 : ℝ)^3485 := by
    have hnat : (805284841 : ℕ)^4509*100000000000000^3485 ≤ 30820008587481^3485*2000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805284841 2000000000 30820008587481 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2265377243/5000000000 : ℝ)^4509 ≤ (35904003202913/100000000000000 : ℝ)^3485 := by
    have hnat : (2265377243 : ℕ)^4509*100000000000000^3485 ≤ 35904003202913^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265377243 5000000000 35904003202913 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068060061/2500000000 : ℝ), (805284841/2000000000 : ℝ), (2265377243/5000000000 : ℝ)] ![(8318997049603/25000000000000 : ℝ), (30820008587481/100000000000000 : ℝ), (35904003202913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068060061/2500000000 : ℝ)|^4509 ≤ (8318997049603/25000000000000 : ℝ)^3485
        have hw : |(1068060061/2500000000 : ℝ)|=(1068060061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(805284841/2000000000 : ℝ)|^4509 ≤ (30820008587481/100000000000000 : ℝ)^3485
        have hw : |(805284841/2000000000 : ℝ)|=(805284841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2265377243/5000000000 : ℝ)|^4509 ≤ (35904003202913/100000000000000 : ℝ)^3485
        have hw : |(2265377243/5000000000 : ℝ)|=(2265377243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s3_4 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-938207013/5000000000 : ℝ)*x 0 + (5215355421/10000000000 : ℝ)*x 1 + (1359083027/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (938207013/5000000000 : ℝ)^4509 ≤ (11476522778771/100000000000000 : ℝ)^3485 := by
    have hnat : (938207013 : ℕ)^4509*100000000000000^3485 ≤ 11476522778771^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938207013 5000000000 11476522778771 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215355421/10000000000 : ℝ)^4509 ≤ (10768451387071/25000000000000 : ℝ)^3485 := by
    have hnat : (5215355421 : ℕ)^4509*25000000000000^3485 ≤ 10768451387071^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215355421 10000000000 10768451387071 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359083027/2500000000 : ℝ)^4509 ≤ (22724835833017/50000000000000 : ℝ)^3485 := by
    have hnat : (1359083027 : ℕ)^4509*50000000000000^3485 ≤ 22724835833017^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359083027 2500000000 22724835833017 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-938207013/5000000000 : ℝ), (5215355421/10000000000 : ℝ), (1359083027/2500000000 : ℝ)] ![(11476522778771/100000000000000 : ℝ), (10768451387071/25000000000000 : ℝ), (22724835833017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-938207013/5000000000 : ℝ)|^4509 ≤ (11476522778771/100000000000000 : ℝ)^3485
        have hw : |(-938207013/5000000000 : ℝ)|=(938207013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215355421/10000000000 : ℝ)|^4509 ≤ (10768451387071/25000000000000 : ℝ)^3485
        have hw : |(5215355421/10000000000 : ℝ)|=(5215355421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359083027/2500000000 : ℝ)|^4509 ≤ (22724835833017/50000000000000 : ℝ)^3485
        have hw : |(1359083027/2500000000 : ℝ)|=(1359083027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s3_5 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529425859/1000000000 : ℝ)*x 0 + (-44217747/250000000 : ℝ)*x 1 + (5436332191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529425859/1000000000 : ℝ)^4509 ≤ (171557874781/390625000000 : ℝ)^3485 := by
    have hnat : (529425859 : ℕ)^4509*390625000000^3485 ≤ 171557874781^3485*1000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529425859 1000000000 171557874781 390625000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44217747/250000000 : ℝ)^4509 ≤ (5315755736459/50000000000000 : ℝ)^3485 := by
    have hnat : (44217747 : ℕ)^4509*50000000000000^3485 ≤ 5315755736459^3485*250000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44217747 250000000 5315755736459 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436332191/10000000000 : ℝ)^4509 ≤ (11362418140959/25000000000000 : ℝ)^3485 := by
    have hnat : (5436332191 : ℕ)^4509*25000000000000^3485 ≤ 11362418140959^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436332191 10000000000 11362418140959 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529425859/1000000000 : ℝ), (-44217747/250000000 : ℝ), (5436332191/10000000000 : ℝ)] ![(171557874781/390625000000 : ℝ), (5315755736459/50000000000000 : ℝ), (11362418140959/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529425859/1000000000 : ℝ)|^4509 ≤ (171557874781/390625000000 : ℝ)^3485
        have hw : |(529425859/1000000000 : ℝ)|=(529425859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44217747/250000000 : ℝ)|^4509 ≤ (5315755736459/50000000000000 : ℝ)^3485
        have hw : |(-44217747/250000000 : ℝ)|=(44217747/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436332191/10000000000 : ℝ)|^4509 ≤ (11362418140959/25000000000000 : ℝ)^3485
        have hw : |(5436332191/10000000000 : ℝ)|=(5436332191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s3_6 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294258653/10000000000 : ℝ)*x 0 + (67954151/125000000 : ℝ)*x 1 + (-442177487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294258653/10000000000 : ℝ)^4509 ≤ (21959408310059/50000000000000 : ℝ)^3485 := by
    have hnat : (5294258653 : ℕ)^4509*50000000000000^3485 ≤ 21959408310059^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294258653 10000000000 21959408310059 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67954151/125000000 : ℝ)^4509 ≤ (22724835681581/50000000000000 : ℝ)^3485 := by
    have hnat : (67954151 : ℕ)^4509*50000000000000^3485 ≤ 22724835681581^3485*125000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67954151 125000000 22724835681581 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442177487/2500000000 : ℝ)^4509 ≤ (10631512001759/100000000000000 : ℝ)^3485 := by
    have hnat : (442177487 : ℕ)^4509*100000000000000^3485 ≤ 10631512001759^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442177487 2500000000 10631512001759 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294258653/10000000000 : ℝ), (67954151/125000000 : ℝ), (-442177487/2500000000 : ℝ)] ![(21959408310059/50000000000000 : ℝ), (22724835681581/50000000000000 : ℝ), (10631512001759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294258653/10000000000 : ℝ)|^4509 ≤ (21959408310059/50000000000000 : ℝ)^3485
        have hw : |(5294258653/10000000000 : ℝ)|=(5294258653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67954151/125000000 : ℝ)|^4509 ≤ (22724835681581/50000000000000 : ℝ)^3485
        have hw : |(67954151/125000000 : ℝ)|=(67954151/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-442177487/2500000000 : ℝ)|^4509 ≤ (10631512001759/100000000000000 : ℝ)^3485
        have hw : |(-442177487/2500000000 : ℝ)|=(442177487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s3_7 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4272312591/10000000000 : ℝ)*x 0 + (4528082337/10000000000 : ℝ)*x 1 + (4029116513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4272312591/10000000000 : ℝ)^4509 ≤ (33276717277019/100000000000000 : ℝ)^3485 := by
    have hnat : (4272312591 : ℕ)^4509*100000000000000^3485 ≤ 33276717277019^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4272312591 10000000000 33276717277019 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4528082337/10000000000 : ℝ)^4509 ≤ (35876608106631/100000000000000 : ℝ)^3485 := by
    have hnat : (4528082337 : ℕ)^4509*100000000000000^3485 ≤ 35876608106631^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528082337 10000000000 35876608106631 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4029116513/10000000000 : ℝ)^4509 ≤ (15423337299933/50000000000000 : ℝ)^3485 := by
    have hnat : (4029116513 : ℕ)^4509*50000000000000^3485 ≤ 15423337299933^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029116513 10000000000 15423337299933 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4272312591/10000000000 : ℝ), (4528082337/10000000000 : ℝ), (4029116513/10000000000 : ℝ)] ![(33276717277019/100000000000000 : ℝ), (35876608106631/100000000000000 : ℝ), (15423337299933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4272312591/10000000000 : ℝ)|^4509 ≤ (33276717277019/100000000000000 : ℝ)^3485
        have hw : |(4272312591/10000000000 : ℝ)|=(4272312591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4528082337/10000000000 : ℝ)|^4509 ≤ (35876608106631/100000000000000 : ℝ)^3485
        have hw : |(4528082337/10000000000 : ℝ)|=(4528082337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4029116513/10000000000 : ℝ)|^4509 ≤ (15423337299933/50000000000000 : ℝ)^3485
        have hw : |(4029116513/10000000000 : ℝ)|=(4029116513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1506_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (801/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (433/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7777/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (801/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10397/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (801/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10397/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (801/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10397/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (801/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10397/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (801/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10397/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (801/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10397/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10397/100000 : ℝ) ^ (4507/1024 : ℝ) ≤ (4710329870984433/100000000000000000000 : ℝ) := by
    have hpowers : (10397/100000 : ℝ)^4507 ≤ (4710329870984433/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10397 : ℕ)^4507*100000000000000000000^1024 ≤ 4710329870984433^1024*100000^4507 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10397 100000 4710329870984433 100000000000000000000 4507 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10397/100000 : ℝ)) (X := (4710329870984433/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (801/5000 : ℝ) ^ (4507/1024 : ℝ) ≤ (15790565394113861/50000000000000000000 : ℝ) := by
    have hpowers : (801/5000 : ℝ)^4507 ≤ (15790565394113861/50000000000000000000 : ℝ)^1024 := by
      have hnat : (801 : ℕ)^4507*50000000000000000000^1024 ≤ 15790565394113861^1024*5000^4507 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        801 5000 15790565394113861 50000000000000000000 4507 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (801/5000 : ℝ)) (X := (15790565394113861/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004710329870984433/50000000000000000000 : ℝ) ≤ (10000214031605073/10000000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (50004710329870984433/50000000000000000000 : ℝ)^1024 ≤ (10000214031605073/10000000000000000 : ℝ)^4507 := by
      have hnat : (50004710329870984433 : ℕ)^1024*10000000000000000^4507 ≤ 10000214031605073^4507*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004710329870984433 50000000000000000000 10000214031605073 10000000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000214031605073/10000000000000000 : ℝ)) (X := (50004710329870984433/50000000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007258292131842431/20000000000000000000 : ℝ) ≤ (5000412217057333/5000000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (20007258292131842431/20000000000000000000 : ℝ)^1024 ≤ (5000412217057333/5000000000000000 : ℝ)^4507 := by
      have hnat : (20007258292131842431 : ℕ)^1024*5000000000000000^4507 ≤ 5000412217057333^4507*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007258292131842431 20000000000000000000 5000412217057333 5000000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000412217057333/5000000000000000 : ℝ)) (X := (20007258292131842431/20000000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015790565394113861/25000000000000000000 : ℝ) ≤ (10001434836624259/10000000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (25015790565394113861/25000000000000000000 : ℝ)^1024 ≤ (10001434836624259/10000000000000000 : ℝ)^4507 := by
      have hnat : (25015790565394113861 : ℕ)^1024*10000000000000000^4507 ≤ 10001434836624259^4507*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015790565394113861 25000000000000000000 10001434836624259 10000000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001434836624259/10000000000000000 : ℝ)) (X := (25015790565394113861/25000000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4710329870984433/100000000000000000000 : ℝ) ≤ ((56218510789930848637/56230000000000000000 : ℝ)+2*(610402509593/562300000000000 : ℝ)*(10397/100000 : ℝ))^(4507/1024 : ℝ) := by
    rw [show (56218510789930848637/56230000000000000000 : ℝ)+2*(610402509593/562300000000000 : ℝ)*(10397/100000 : ℝ)=(10000214031605073/10000000000000000 : ℝ) by norm_num, show 1+2*(4710329870984433/100000000000000000000 : ℝ)=(50004710329870984433/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15790565394113861/50000000000000000000 : ℝ)+(4710329870984433/100000000000000000000 : ℝ) ≤ ((56218510789930848637/56230000000000000000 : ℝ)+(610402509593/562300000000000 : ℝ)*((801/5000 : ℝ)+(10397/100000 : ℝ)))^(4507/1024 : ℝ) := by
    rw [show (56218510789930848637/56230000000000000000 : ℝ)+(610402509593/562300000000000 : ℝ)*((801/5000 : ℝ)+(10397/100000 : ℝ))=(5000412217057333/5000000000000000 : ℝ) by norm_num, show 1+(15790565394113861/50000000000000000000 : ℝ)+(4710329870984433/100000000000000000000 : ℝ)=(20007258292131842431/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15790565394113861/50000000000000000000 : ℝ) ≤ ((56218510789930848637/56230000000000000000 : ℝ)+2*(610402509593/562300000000000 : ℝ)*(801/5000 : ℝ))^(4507/1024 : ℝ) := by
    rw [show (56218510789930848637/56230000000000000000 : ℝ)+2*(610402509593/562300000000000 : ℝ)*(801/5000 : ℝ)=(10001434836624259/10000000000000000 : ℝ) by norm_num, show 1+2*(15790565394113861/50000000000000000000 : ℝ)=(25015790565394113861/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56218510789930848637/56230000000000000000 : ℝ)*(X 1 0+X 2 0)+(610402509593/562300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (10397/100000 : ℝ)) (hi := (801/5000 : ℝ)) (c := (56218510789930848637/56230000000000000000 : ℝ)) (alpha := (610402509593/562300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56218510789930848637/56230000000000000000 : ℝ)*(X 0 1+X 2 1)+(610402509593/562300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (10397/100000 : ℝ)) (hi := (801/5000 : ℝ)) (c := (56218510789930848637/56230000000000000000 : ℝ)) (alpha := (610402509593/562300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56218510789930848637/56230000000000000000 : ℝ)*(X 0 2+X 1 2)+(610402509593/562300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (10397/100000 : ℝ)) (hi := (801/5000 : ℝ)) (c := (56218510789930848637/56230000000000000000 : ℝ)) (alpha := (610402509593/562300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1876382049/10000000000 : ℝ)*X 0 0+(217500981/400000000 : ℝ)*X 0 1+(651771497/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352839427/10000000000 : ℝ)*X 1 0+(-1990870139/10000000000 : ℝ)*X 1 1+(5214171929/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352839401/10000000000 : ℝ)*X 2 0+(5214171959/10000000000 : ℝ)*X 2 1+(-995435067/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1068060061/2500000000 : ℝ)*X 0 0+(805284841/2000000000 : ℝ)*X 0 1+(2265377243/5000000000 : ℝ)*X 0 2+(1068060061/2500000000 : ℝ)*X 1 0+(805284841/2000000000 : ℝ)*X 1 1+(2265377243/5000000000 : ℝ)*X 1 2+(1068060061/2500000000 : ℝ)*X 2 0+(805284841/2000000000 : ℝ)*X 2 1+(2265377243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-938207013/5000000000 : ℝ)*X 0 0+(5215355421/10000000000 : ℝ)*X 0 1+(1359083027/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529425859/1000000000 : ℝ)*X 1 0+(-44217747/250000000 : ℝ)*X 1 1+(5436332191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294258653/10000000000 : ℝ)*X 2 0+(67954151/125000000 : ℝ)*X 2 1+(-442177487/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4272312591/10000000000 : ℝ)*X 0 0+(4528082337/10000000000 : ℝ)*X 0 1+(4029116513/10000000000 : ℝ)*X 0 2+(4272312591/10000000000 : ℝ)*X 1 0+(4528082337/10000000000 : ℝ)*X 1 1+(4029116513/10000000000 : ℝ)*X 1 2+(4272312591/10000000000 : ℝ)*X 2 0+(4528082337/10000000000 : ℝ)*X 2 1+(4029116513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1758029887826350048085829927/281150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (583340237/50000000000000 : ℝ)*(base19) + (1058663071/100000000000000 : ℝ)*(base23) + (46179103/100000000000000 : ℝ)*(lower2) + (15421807/10000000000000 : ℝ)*(upper3) + (45715561/50000000000000 : ℝ)*(upper5) + (323005272166943/10000000000000 : ℝ)*(major0) + (323005272166943/10000000000000 : ℝ)*(major1) + (323005272166943/10000000000000 : ℝ)*(major2) + (4477244876876069/100000000000000 : ℝ)*(sp0) + (4477260954154329/100000000000000 : ℝ)*(sp1) + (1119315265542933/25000000000000 : ℝ)*(sp2) + (495708720275537/25000000000000 : ℝ)*(sp3) + (8621979367/50000000000000 : ℝ)*(sp4) + (1029121087/12500000000000 : ℝ)*(sp7) + (396568622814169/20000000000000 : ℝ)*(f.failure) + (4477262120834803/100000000000000 : ℝ)*(f.sum) + (16491476702989/5623000000000000000000000000 : ℝ)*base65 + (1559712735486606691/562300000000000000000000000000000 : ℝ)*base67 + (2076896422333693309/562300000000000000000000000000000 : ℝ)*base70 + (2263039280353393309/562300000000000000000000000000000 : ℝ)*base72 + (5621127200819/1124600000000000000000000000 : ℝ)*base73 + (1224053662508806691/562300000000000000000000000000000 : ℝ)*base75 + (6356821193906691/562300000000000000000000000000000 : ℝ)*base77 + (3136079316423906691/562300000000000000000000000000000 : ℝ)*base79 + (9243669297587/2811500000000000000000000000 : ℝ)*base81 + (2604197/400000000000000000000 : ℝ)*base89 + (2604197/400000000000000000000 : ℝ)*base91 + (2604197/400000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3073338031784142067069046799/562300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (964697253/100000000000000 : ℝ)*(base19) + (1166339327/100000000000000 : ℝ)*(base23) + (208761/160000000000 : ℝ)*(upper3) + (69964373/100000000000000 : ℝ)*(lower4) + (641353/625000000000 : ℝ)*(upper5) + (652950800882391/20000000000000 : ℝ)*(major0) + (652950800882391/20000000000000 : ℝ)*(major1) + (652950800882391/20000000000000 : ℝ)*(major2) + (15634689171/100000000000000 : ℝ)*(sp1) + (17048211289/100000000000000 : ℝ)*(sp2) + (905072504342731/20000000000000 : ℝ)*(sp4) + (70708530036363/1562500000000 : ℝ)*(sp5) + (4525344307163039/100000000000000 : ℝ)*(sp6) + (400829060984347/20000000000000 : ℝ)*(sp7) + (400829060984347/20000000000000 : ℝ)*(f.failure) + (905072504342731/20000000000000 : ℝ)*(f.sum) + (2737576230349/2811500000000000000000000000 : ℝ)*base65 + (469987099875951067/1124600000000000000000000000000000 : ℝ)*base67 + (3109475637711048933/1124600000000000000000000000000000 : ℝ)*base70 + (525244509808751067/1124600000000000000000000000000000 : ℝ)*base71 + (6058410519729/1124600000000000000000000000 : ℝ)*base73 + (4422414009013648933/1124600000000000000000000000000000 : ℝ)*base76 + (1409116616017351067/1124600000000000000000000000000000 : ℝ)*base77 + (16098482994382351067/1124600000000000000000000000000000 : ℝ)*base79 + (3719766823887/1405750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1943489/400000000000000000000 : ℝ)*base90 + (1943489/400000000000000000000 : ℝ)*base92 + (1943489/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1506_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (801/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (433/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7777/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1506_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1506_s4_0 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-117303319/625000000 : ℝ)*x 0 + (339652877/625000000 : ℝ)*x 1 + (5216939297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (117303319/625000000 : ℝ)^4509 ≤ (11479997465949/100000000000000 : ℝ)^3485 := by
    have hnat : (117303319 : ℕ)^4509*100000000000000^3485 ≤ 11479997465949^3485*625000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117303319 625000000 11479997465949 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339652877/625000000 : ℝ)^4509 ≤ (22714635619157/50000000000000 : ℝ)^3485 := by
    have hnat : (339652877 : ℕ)^4509*50000000000000^3485 ≤ 22714635619157^3485*625000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339652877 625000000 22714635619157 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216939297/10000000000 : ℝ)^4509 ≤ (8618146255113/20000000000000 : ℝ)^3485 := by
    have hnat : (5216939297 : ℕ)^4509*20000000000000^3485 ≤ 8618146255113^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216939297 10000000000 8618146255113 20000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-117303319/625000000 : ℝ), (339652877/625000000 : ℝ), (5216939297/10000000000 : ℝ)] ![(11479997465949/100000000000000 : ℝ), (22714635619157/50000000000000 : ℝ), (8618146255113/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-117303319/625000000 : ℝ)|^4509 ≤ (11479997465949/100000000000000 : ℝ)^3485
        have hw : |(-117303319/625000000 : ℝ)|=(117303319/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339652877/625000000 : ℝ)|^4509 ≤ (22714635619157/50000000000000 : ℝ)^3485
        have hw : |(339652877/625000000 : ℝ)|=(339652877/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216939297/10000000000 : ℝ)|^4509 ≤ (8618146255113/20000000000000 : ℝ)^3485
        have hw : |(5216939297/10000000000 : ℝ)|=(5216939297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s4_1 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352035451/10000000000 : ℝ)*x 0 + (-994137077/5000000000 : ℝ)*x 1 + (2608468919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352035451/10000000000 : ℝ)^4509 ≤ (556749115747/1250000000000 : ℝ)^3485 := by
    have hnat : (5352035451 : ℕ)^4509*1250000000000^3485 ≤ 556749115747^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352035451 10000000000 556749115747 1250000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994137077/5000000000 : ℝ)^4509 ≤ (12369355042729/100000000000000 : ℝ)^3485 := by
    have hnat : (994137077 : ℕ)^4509*100000000000000^3485 ≤ 12369355042729^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994137077 5000000000 12369355042729 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608468919/5000000000 : ℝ)^4509 ≤ (21545357841801/50000000000000 : ℝ)^3485 := by
    have hnat : (2608468919 : ℕ)^4509*50000000000000^3485 ≤ 21545357841801^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608468919 5000000000 21545357841801 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352035451/10000000000 : ℝ), (-994137077/5000000000 : ℝ), (2608468919/5000000000 : ℝ)] ![(556749115747/1250000000000 : ℝ), (12369355042729/100000000000000 : ℝ), (21545357841801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352035451/10000000000 : ℝ)|^4509 ≤ (556749115747/1250000000000 : ℝ)^3485
        have hw : |(5352035451/10000000000 : ℝ)|=(5352035451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-994137077/5000000000 : ℝ)|^4509 ≤ (12369355042729/100000000000000 : ℝ)^3485
        have hw : |(-994137077/5000000000 : ℝ)|=(994137077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608468919/5000000000 : ℝ)|^4509 ≤ (21545357841801/50000000000000 : ℝ)^3485
        have hw : |(2608468919/5000000000 : ℝ)|=(2608468919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s4_2 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676017327/5000000000 : ℝ)*x 0 + (2608469621/5000000000 : ℝ)*x 1 + (-497068339/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676017327/5000000000 : ℝ)^4509 ≤ (22269960339099/50000000000000 : ℝ)^3485 := by
    have hnat : (2676017327 : ℕ)^4509*50000000000000^3485 ≤ 22269960339099^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676017327 5000000000 22269960339099 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608469621/5000000000 : ℝ)^4509 ≤ (21545365343897/50000000000000 : ℝ)^3485 := by
    have hnat : (2608469621 : ℕ)^4509*50000000000000^3485 ≤ 21545365343897^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608469621 5000000000 21545365343897 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497068339/2500000000 : ℝ)^4509 ≤ (6184674309767/50000000000000 : ℝ)^3485 := by
    have hnat : (497068339 : ℕ)^4509*50000000000000^3485 ≤ 6184674309767^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497068339 2500000000 6184674309767 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676017327/5000000000 : ℝ), (2608469621/5000000000 : ℝ), (-497068339/2500000000 : ℝ)] ![(22269960339099/50000000000000 : ℝ), (21545365343897/50000000000000 : ℝ), (6184674309767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676017327/5000000000 : ℝ)|^4509 ≤ (22269960339099/50000000000000 : ℝ)^3485
        have hw : |(2676017327/5000000000 : ℝ)|=(2676017327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608469621/5000000000 : ℝ)|^4509 ≤ (21545365343897/50000000000000 : ℝ)^3485
        have hw : |(2608469621/5000000000 : ℝ)|=(2608469621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-497068339/2500000000 : ℝ)|^4509 ≤ (6184674309767/50000000000000 : ℝ)^3485
        have hw : |(-497068339/2500000000 : ℝ)|=(497068339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s4_3 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66758363/156250000 : ℝ)*x 0 + (4032985817/10000000000 : ℝ)*x 1 + (1131030903/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66758363/156250000 : ℝ)^4509 ≤ (33278960969733/100000000000000 : ℝ)^3485 := by
    have hnat : (66758363 : ℕ)^4509*100000000000000^3485 ≤ 33278960969733^3485*156250000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66758363 156250000 33278960969733 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4032985817/10000000000 : ℝ)^4509 ≤ (6177001471911/20000000000000 : ℝ)^3485 := by
    have hnat : (4032985817 : ℕ)^4509*20000000000000^3485 ≤ 6177001471911^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032985817 10000000000 6177001471911 20000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131030903/2500000000 : ℝ)^4509 ≤ (35836031656367/100000000000000 : ℝ)^3485 := by
    have hnat : (1131030903 : ℕ)^4509*100000000000000^3485 ≤ 35836031656367^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131030903 2500000000 35836031656367 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66758363/156250000 : ℝ), (4032985817/10000000000 : ℝ), (1131030903/2500000000 : ℝ)] ![(33278960969733/100000000000000 : ℝ), (6177001471911/20000000000000 : ℝ), (35836031656367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66758363/156250000 : ℝ)|^4509 ≤ (33278960969733/100000000000000 : ℝ)^3485
        have hw : |(66758363/156250000 : ℝ)|=(66758363/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4032985817/10000000000 : ℝ)|^4509 ≤ (6177001471911/20000000000000 : ℝ)^3485
        have hw : |(4032985817/10000000000 : ℝ)|=(4032985817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131030903/2500000000 : ℝ)|^4509 ≤ (35836031656367/100000000000000 : ℝ)^3485
        have hw : |(1131030903/2500000000 : ℝ)|=(1131030903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s4_4 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-375376389/2000000000 : ℝ)*x 0 + (2609030403/5000000000 : ℝ)*x 1 + (1358329183/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (375376389/2000000000 : ℝ)^4509 ≤ (717514106901/6250000000000 : ℝ)^3485 := by
    have hnat : (375376389 : ℕ)^4509*6250000000000^3485 ≤ 717514106901^3485*2000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375376389 2000000000 717514106901 6250000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609030403/5000000000 : ℝ)^4509 ≤ (21551358468591/50000000000000 : ℝ)^3485 := by
    have hnat : (2609030403 : ℕ)^4509*50000000000000^3485 ≤ 21551358468591^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609030403 5000000000 21551358468591 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358329183/2500000000 : ℝ)^4509 ≤ (45417057348123/100000000000000 : ℝ)^3485 := by
    have hnat : (1358329183 : ℕ)^4509*100000000000000^3485 ≤ 45417057348123^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358329183 2500000000 45417057348123 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-375376389/2000000000 : ℝ), (2609030403/5000000000 : ℝ), (1358329183/2500000000 : ℝ)] ![(717514106901/6250000000000 : ℝ), (21551358468591/50000000000000 : ℝ), (45417057348123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-375376389/2000000000 : ℝ)|^4509 ≤ (717514106901/6250000000000 : ℝ)^3485
        have hw : |(-375376389/2000000000 : ℝ)|=(375376389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609030403/5000000000 : ℝ)|^4509 ≤ (21551358468591/50000000000000 : ℝ)^3485
        have hw : |(2609030403/5000000000 : ℝ)|=(2609030403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358329183/2500000000 : ℝ)|^4509 ≤ (45417057348123/100000000000000 : ℝ)^3485
        have hw : |(1358329183/2500000000 : ℝ)|=(1358329183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s4_5 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323747229/2500000000 : ℝ)*x 0 + (-885947541/5000000000 : ℝ)*x 1 + (271665829/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323747229/2500000000 : ℝ)^4509 ≤ (43926654724177/100000000000000 : ℝ)^3485 := by
    have hnat : (1323747229 : ℕ)^4509*100000000000000^3485 ≤ 43926654724177^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323747229 2500000000 43926654724177 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (885947541/5000000000 : ℝ)^4509 ≤ (2131257910943/20000000000000 : ℝ)^3485 := by
    have hnat : (885947541 : ℕ)^4509*20000000000000^3485 ≤ 2131257910943^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885947541 5000000000 2131257910943 20000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271665829/500000000 : ℝ)^4509 ≤ (1816682228169/4000000000000 : ℝ)^3485 := by
    have hnat : (271665829 : ℕ)^4509*4000000000000^3485 ≤ 1816682228169^3485*500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271665829 500000000 1816682228169 4000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323747229/2500000000 : ℝ), (-885947541/5000000000 : ℝ), (271665829/500000000 : ℝ)] ![(43926654724177/100000000000000 : ℝ), (2131257910943/20000000000000 : ℝ), (1816682228169/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323747229/2500000000 : ℝ)|^4509 ≤ (43926654724177/100000000000000 : ℝ)^3485
        have hw : |(1323747229/2500000000 : ℝ)|=(1323747229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-885947541/5000000000 : ℝ)|^4509 ≤ (2131257910943/20000000000000 : ℝ)^3485
        have hw : |(-885947541/5000000000 : ℝ)|=(885947541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271665829/500000000 : ℝ)|^4509 ≤ (1816682228169/4000000000000 : ℝ)^3485
        have hw : |(271665829/500000000 : ℝ)|=(271665829/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s4_6 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647494259/5000000000 : ℝ)*x 0 + (2716658423/5000000000 : ℝ)*x 1 + (-885947631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647494259/5000000000 : ℝ)^4509 ≤ (10981662613063/25000000000000 : ℝ)^3485 := by
    have hnat : (2647494259 : ℕ)^4509*25000000000000^3485 ≤ 10981662613063^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647494259 5000000000 10981662613063 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716658423/5000000000 : ℝ)^4509 ≤ (45417058581047/100000000000000 : ℝ)^3485 := by
    have hnat : (2716658423 : ℕ)^4509*100000000000000^3485 ≤ 45417058581047^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716658423 5000000000 45417058581047 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (885947631/5000000000 : ℝ)^4509 ≤ (166504546177/1562500000000 : ℝ)^3485 := by
    have hnat : (885947631 : ℕ)^4509*1562500000000^3485 ≤ 166504546177^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885947631 5000000000 166504546177 1562500000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647494259/5000000000 : ℝ), (2716658423/5000000000 : ℝ), (-885947631/5000000000 : ℝ)] ![(10981662613063/25000000000000 : ℝ), (45417058581047/100000000000000 : ℝ), (166504546177/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647494259/5000000000 : ℝ)|^4509 ≤ (10981662613063/25000000000000 : ℝ)^3485
        have hw : |(2647494259/5000000000 : ℝ)|=(2647494259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716658423/5000000000 : ℝ)|^4509 ≤ (45417058581047/100000000000000 : ℝ)^3485
        have hw : |(2716658423/5000000000 : ℝ)|=(2716658423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-885947631/5000000000 : ℝ)|^4509 ≤ (166504546177/1562500000000 : ℝ)^3485
        have hw : |(-885947631/5000000000 : ℝ)|=(885947631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s4_7 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26703753/62500000 : ℝ)*x 0 + (4521588901/10000000000 : ℝ)*x 1 + (4035540759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26703753/62500000 : ℝ)^4509 ≤ (33279618521179/100000000000000 : ℝ)^3485 := by
    have hnat : (26703753 : ℕ)^4509*100000000000000^3485 ≤ 33279618521179^3485*62500000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26703753 62500000 33279618521179 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4521588901/10000000000 : ℝ)^4509 ≤ (8952514163471/25000000000000 : ℝ)^3485 := by
    have hnat : (4521588901 : ℕ)^4509*25000000000000^3485 ≤ 8952514163471^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521588901 10000000000 8952514163471 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4035540759/10000000000 : ℝ)^4509 ≤ (30910324807513/100000000000000 : ℝ)^3485 := by
    have hnat : (4035540759 : ℕ)^4509*100000000000000^3485 ≤ 30910324807513^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035540759 10000000000 30910324807513 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26703753/62500000 : ℝ), (4521588901/10000000000 : ℝ), (4035540759/10000000000 : ℝ)] ![(33279618521179/100000000000000 : ℝ), (8952514163471/25000000000000 : ℝ), (30910324807513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26703753/62500000 : ℝ)|^4509 ≤ (33279618521179/100000000000000 : ℝ)^3485
        have hw : |(26703753/62500000 : ℝ)|=(26703753/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4521588901/10000000000 : ℝ)|^4509 ≤ (8952514163471/25000000000000 : ℝ)^3485
        have hw : |(4521588901/10000000000 : ℝ)|=(4521588901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4035540759/10000000000 : ℝ)|^4509 ≤ (30910324807513/100000000000000 : ℝ)^3485
        have hw : |(4035540759/10000000000 : ℝ)|=(4035540759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1506_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7777/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (433/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (2721/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7777/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (433/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7777/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (433/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7777/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (433/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7777/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (433/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7777/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (433/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7777/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (433/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (433/4000 : ℝ) ^ (4507/1024 : ℝ) ≤ (5625519883074887/100000000000000000000 : ℝ) := by
    have hpowers : (433/4000 : ℝ)^4507 ≤ (5625519883074887/100000000000000000000 : ℝ)^1024 := by
      have hnat : (433 : ℕ)^4507*100000000000000000000^1024 ≤ 5625519883074887^1024*4000^4507 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        433 4000 5625519883074887 100000000000000000000 4507 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (433/4000 : ℝ)) (X := (5625519883074887/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7777/50000 : ℝ) ^ (4507/1024 : ℝ) ≤ (27733221030125067/100000000000000000000 : ℝ) := by
    have hpowers : (7777/50000 : ℝ)^4507 ≤ (27733221030125067/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7777 : ℕ)^4507*100000000000000000000^1024 ≤ 27733221030125067^1024*50000^4507 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7777 50000 27733221030125067 100000000000000000000 4507 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7777/50000 : ℝ)) (X := (27733221030125067/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005625519883074887/50000000000000000000 : ℝ) ≤ (10000255614907661/10000000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (50005625519883074887/50000000000000000000 : ℝ)^1024 ≤ (10000255614907661/10000000000000000 : ℝ)^4507 := by
      have hnat : (50005625519883074887 : ℕ)^1024*10000000000000000^4507 ≤ 10000255614907661^4507*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005625519883074887 50000000000000000000 10000255614907661 10000000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000255614907661/10000000000000000 : ℝ)) (X := (50005625519883074887/50000000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50016679370456599977/50000000000000000000 : ℝ) ≤ (5000378910012171/5000000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (50016679370456599977/50000000000000000000 : ℝ)^1024 ≤ (5000378910012171/5000000000000000 : ℝ)^4507 := by
      have hnat : (50016679370456599977 : ℕ)^1024*5000000000000000^4507 ≤ 5000378910012171^4507*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016679370456599977 50000000000000000000 5000378910012171 5000000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000378910012171/5000000000000000 : ℝ)) (X := (50016679370456599977/50000000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027733221030125067/50000000000000000000 : ℝ) ≤ (10001260025141023/10000000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (50027733221030125067/50000000000000000000 : ℝ)^1024 ≤ (10001260025141023/10000000000000000 : ℝ)^4507 := by
      have hnat : (50027733221030125067 : ℕ)^1024*10000000000000000^4507 ≤ 10001260025141023^4507*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027733221030125067 50000000000000000000 10001260025141023 10000000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001260025141023/10000000000000000 : ℝ)) (X := (50027733221030125067/50000000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5625519883074887/100000000000000000000 : ℝ) ≤ ((47280336062122185219/47290000000000000000 : ℝ)+2*(502205116681/472900000000000 : ℝ)*(433/4000 : ℝ))^(4507/1024 : ℝ) := by
    rw [show (47280336062122185219/47290000000000000000 : ℝ)+2*(502205116681/472900000000000 : ℝ)*(433/4000 : ℝ)=(10000255614907661/10000000000000000 : ℝ) by norm_num, show 1+2*(5625519883074887/100000000000000000000 : ℝ)=(50005625519883074887/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27733221030125067/100000000000000000000 : ℝ)+(5625519883074887/100000000000000000000 : ℝ) ≤ ((47280336062122185219/47290000000000000000 : ℝ)+(502205116681/472900000000000 : ℝ)*((7777/50000 : ℝ)+(433/4000 : ℝ)))^(4507/1024 : ℝ) := by
    rw [show (47280336062122185219/47290000000000000000 : ℝ)+(502205116681/472900000000000 : ℝ)*((7777/50000 : ℝ)+(433/4000 : ℝ))=(5000378910012171/5000000000000000 : ℝ) by norm_num, show 1+(27733221030125067/100000000000000000000 : ℝ)+(5625519883074887/100000000000000000000 : ℝ)=(50016679370456599977/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27733221030125067/100000000000000000000 : ℝ) ≤ ((47280336062122185219/47290000000000000000 : ℝ)+2*(502205116681/472900000000000 : ℝ)*(7777/50000 : ℝ))^(4507/1024 : ℝ) := by
    rw [show (47280336062122185219/47290000000000000000 : ℝ)+2*(502205116681/472900000000000 : ℝ)*(7777/50000 : ℝ)=(10001260025141023/10000000000000000 : ℝ) by norm_num, show 1+2*(27733221030125067/100000000000000000000 : ℝ)=(50027733221030125067/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (47280336062122185219/47290000000000000000 : ℝ)*(X 1 0+X 2 0)+(502205116681/472900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (433/4000 : ℝ)) (hi := (7777/50000 : ℝ)) (c := (47280336062122185219/47290000000000000000 : ℝ)) (alpha := (502205116681/472900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (47280336062122185219/47290000000000000000 : ℝ)*(X 0 1+X 2 1)+(502205116681/472900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (433/4000 : ℝ)) (hi := (7777/50000 : ℝ)) (c := (47280336062122185219/47290000000000000000 : ℝ)) (alpha := (502205116681/472900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (47280336062122185219/47290000000000000000 : ℝ)*(X 0 2+X 1 2)+(502205116681/472900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (433/4000 : ℝ)) (hi := (7777/50000 : ℝ)) (c := (47280336062122185219/47290000000000000000 : ℝ)) (alpha := (502205116681/472900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-117303319/625000000 : ℝ)*X 0 0+(339652877/625000000 : ℝ)*X 0 1+(5216939297/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352035451/10000000000 : ℝ)*X 1 0+(-994137077/5000000000 : ℝ)*X 1 1+(2608468919/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676017327/5000000000 : ℝ)*X 2 0+(2608469621/5000000000 : ℝ)*X 2 1+(-497068339/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((66758363/156250000 : ℝ)*X 0 0+(4032985817/10000000000 : ℝ)*X 0 1+(1131030903/2500000000 : ℝ)*X 0 2+(66758363/156250000 : ℝ)*X 1 0+(4032985817/10000000000 : ℝ)*X 1 1+(1131030903/2500000000 : ℝ)*X 1 2+(66758363/156250000 : ℝ)*X 2 0+(4032985817/10000000000 : ℝ)*X 2 1+(1131030903/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-375376389/2000000000 : ℝ)*X 0 0+(2609030403/5000000000 : ℝ)*X 0 1+(1358329183/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323747229/2500000000 : ℝ)*X 1 0+(-885947541/5000000000 : ℝ)*X 1 1+(271665829/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647494259/5000000000 : ℝ)*X 2 0+(2716658423/5000000000 : ℝ)*X 2 1+(-885947631/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((26703753/62500000 : ℝ)*X 0 0+(4521588901/10000000000 : ℝ)*X 0 1+(4035540759/10000000000 : ℝ)*X 0 2+(26703753/62500000 : ℝ)*X 1 0+(4521588901/10000000000 : ℝ)*X 1 1+(4035540759/10000000000 : ℝ)*X 1 2+(26703753/62500000 : ℝ)*X 2 0+(4521588901/10000000000 : ℝ)*X 2 1+(4035540759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (77220455571260786764449/11822500000000000000000000000 : ℝ) := by norm_num
    linear_combination (612276357/25000000000000 : ℝ)*(base19) + (829348411/50000000000000 : ℝ)*(base23) + (46029941/25000000000000 : ℝ)*(upper3) + (56602993/100000000000000 : ℝ)*(upper4) + (759608421/100000000000000 : ℝ)*(upper5) + (1658424851680007/50000000000000 : ℝ)*(major0) + (1658424851680007/50000000000000 : ℝ)*(major1) + (1658424851680007/50000000000000 : ℝ)*(major2) + (2298779548806859/50000000000000 : ℝ)*(sp0) + (2298785638246473/50000000000000 : ℝ)*(sp1) + (287348254181347/6250000000000 : ℝ)*(sp2) + (509027652926987/25000000000000 : ℝ)*(sp3) + (914249041/6250000000000 : ℝ)*(sp4) + (232057687/1562500000000 : ℝ)*(sp7) + (509031365849979/25000000000000 : ℝ)*(f.failure) + (2298786862799187/50000000000000 : ℝ)*(f.sum) + (10693521815927/11822500000000000000000000000 : ℝ)*base65 + (10239276391507916533/2364500000000000000000000000000000 : ℝ)*base67 + (14114250596977083467/2364500000000000000000000000000000 : ℝ)*base70 + (22119193956430916533/2364500000000000000000000000000000 : ℝ)*base71 + (73317766320733/11822500000000000000000000000 : ℝ)*base74 + (11000086604972083467/2364500000000000000000000000000000 : ℝ)*base76 + (8068269632518083467/2364500000000000000000000000000000 : ℝ)*base78 + (30851464956163916533/2364500000000000000000000000000000 : ℝ)*base79 + (7779377334007/11822500000000000000000000000 : ℝ)*base81 + (1869727/500000000000000000000 : ℝ)*base89 + (1869727/500000000000000000000 : ℝ)*base91 + (1869727/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8330361812287188447982276203/1182250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1656368323/100000000000000 : ℝ)*(base19) + (1315985921/100000000000000 : ℝ)*(base23) + (28742901/100000000000000 : ℝ)*(upper2) + (32137297/20000000000000 : ℝ)*(upper3) + (2554951/1562500000000 : ℝ)*(upper5) + (1675759668884979/50000000000000 : ℝ)*(major0) + (1675759668884979/50000000000000 : ℝ)*(major1) + (1675759668884979/50000000000000 : ℝ)*(major2) + (24268137763/100000000000000 : ℝ)*(sp1) + (801893693/4000000000000 : ℝ)*(sp2) + (4645630214482271/100000000000000 : ℝ)*(sp4) + (929120857995237/20000000000000 : ℝ)*(sp5) + (580701106394253/12500000000000 : ℝ)*(sp6) + (2057408226184537/100000000000000 : ℝ)*(sp7) + (2057408226184537/100000000000000 : ℝ)*(f.failure) + (4645630214482271/100000000000000 : ℝ)*(f.sum) + (6222749854527/23645000000000000000000000000 : ℝ)*base66 + (8197917534748674599/2364500000000000000000000000000000 : ℝ)*base68 + (195285472482674599/2364500000000000000000000000000000 : ℝ)*base70 + (15721721232763674599/2364500000000000000000000000000000 : ℝ)*base72 + (71762160587973/23645000000000000000000000000 : ℝ)*base73 + (10172183223648325401/2364500000000000000000000000000000 : ℝ)*base75 + (4664433512344174599/2364500000000000000000000000000000 : ℝ)*base78 + (425566409295325401/2364500000000000000000000000000000 : ℝ)*base79 + (18360107080623/23645000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (4141019/2000000000000000000000 : ℝ)*base90 + (4141019/2000000000000000000000 : ℝ)*base92 + (4141019/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1506_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7777/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (433/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2721/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1506_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1506_s5_0 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-938455671/5000000000 : ℝ)*x 0 + (5434062647/10000000000 : ℝ)*x 1 + (5217284177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (938455671/5000000000 : ℝ)^4509 ≤ (2296091671213/20000000000000 : ℝ)^3485 := by
    have hnat : (938455671 : ℕ)^4509*20000000000000^3485 ≤ 2296091671213^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938455671 5000000000 2296091671213 20000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434062647/10000000000 : ℝ)^4509 ≤ (22712562336271/50000000000000 : ℝ)^3485 := by
    have hnat : (5434062647 : ℕ)^4509*50000000000000^3485 ≤ 22712562336271^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434062647 10000000000 22712562336271 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217284177/10000000000 : ℝ)^4509 ≤ (10773604239179/25000000000000 : ℝ)^3485 := by
    have hnat : (5217284177 : ℕ)^4509*25000000000000^3485 ≤ 10773604239179^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217284177 10000000000 10773604239179 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-938455671/5000000000 : ℝ), (5434062647/10000000000 : ℝ), (5217284177/10000000000 : ℝ)] ![(2296091671213/20000000000000 : ℝ), (22712562336271/50000000000000 : ℝ), (10773604239179/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-938455671/5000000000 : ℝ)|^4509 ≤ (2296091671213/20000000000000 : ℝ)^3485
        have hw : |(-938455671/5000000000 : ℝ)|=(938455671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434062647/10000000000 : ℝ)|^4509 ≤ (22712562336271/50000000000000 : ℝ)^3485
        have hw : |(5434062647/10000000000 : ℝ)|=(5434062647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217284177/10000000000 : ℝ)|^4509 ≤ (10773604239179/25000000000000 : ℝ)^3485
        have hw : |(5217284177/10000000000 : ℝ)|=(5217284177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s5_1 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351934589/10000000000 : ℝ)*x 0 + (-1987949111/10000000000 : ℝ)*x 1 + (5217284269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351934589/10000000000 : ℝ)^4509 ≤ (44538843248401/100000000000000 : ℝ)^3485 := by
    have hnat : (5351934589 : ℕ)^4509*100000000000000^3485 ≤ 44538843248401^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351934589 10000000000 44538843248401 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1987949111/10000000000 : ℝ)^4509 ≤ (6183369398213/50000000000000 : ℝ)^3485 := by
    have hnat : (1987949111 : ℕ)^4509*50000000000000^3485 ≤ 6183369398213^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987949111 10000000000 6183369398213 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217284269/10000000000 : ℝ)^4509 ≤ (10773604484979/25000000000000 : ℝ)^3485 := by
    have hnat : (5217284269 : ℕ)^4509*25000000000000^3485 ≤ 10773604484979^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217284269 10000000000 10773604484979 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351934589/10000000000 : ℝ), (-1987949111/10000000000 : ℝ), (5217284269/10000000000 : ℝ)] ![(44538843248401/100000000000000 : ℝ), (6183369398213/50000000000000 : ℝ), (10773604484979/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351934589/10000000000 : ℝ)|^4509 ≤ (44538843248401/100000000000000 : ℝ)^3485
        have hw : |(5351934589/10000000000 : ℝ)|=(5351934589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1987949111/10000000000 : ℝ)|^4509 ≤ (6183369398213/50000000000000 : ℝ)^3485
        have hw : |(-1987949111/10000000000 : ℝ)|=(1987949111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217284269/10000000000 : ℝ)|^4509 ≤ (10773604484979/25000000000000 : ℝ)^3485
        have hw : |(5217284269/10000000000 : ℝ)|=(5217284269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s5_2 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66899177/125000000 : ℝ)*x 0 + (1304321227/2500000000 : ℝ)*x 1 + (-1987948837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66899177/125000000 : ℝ)^4509 ≤ (44538838629243/100000000000000 : ℝ)^3485 := by
    have hnat : (66899177 : ℕ)^4509*100000000000000^3485 ≤ 44538838629243^3485*125000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66899177 125000000 44538838629243 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304321227/2500000000 : ℝ)^4509 ≤ (538680309611/1250000000000 : ℝ)^3485 := by
    have hnat : (1304321227 : ℕ)^4509*1250000000000^3485 ≤ 538680309611^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304321227 2500000000 538680309611 1250000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1987948837/10000000000 : ℝ)^4509 ≤ (6183368295537/50000000000000 : ℝ)^3485 := by
    have hnat : (1987948837 : ℕ)^4509*50000000000000^3485 ≤ 6183368295537^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987948837 10000000000 6183368295537 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66899177/125000000 : ℝ), (1304321227/2500000000 : ℝ), (-1987948837/10000000000 : ℝ)] ![(44538838629243/100000000000000 : ℝ), (538680309611/1250000000000 : ℝ), (6183368295537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66899177/125000000 : ℝ)|^4509 ≤ (44538838629243/100000000000000 : ℝ)^3485
        have hw : |(66899177/125000000 : ℝ)|=(66899177/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304321227/2500000000 : ℝ)|^4509 ≤ (538680309611/1250000000000 : ℝ)^3485
        have hw : |(1304321227/2500000000 : ℝ)|=(1304321227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1987948837/10000000000 : ℝ)|^4509 ≤ (6183368295537/50000000000000 : ℝ)^3485
        have hw : |(-1987948837/10000000000 : ℝ)|=(1987948837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s5_3 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26703563/62500000 : ℝ)*x 0 + (100845227/250000000 : ℝ)*x 1 + (452329337/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26703563/62500000 : ℝ)^4509 ≤ (33279312157951/100000000000000 : ℝ)^3485 := by
    have hnat : (26703563 : ℕ)^4509*100000000000000^3485 ≤ 33279312157951^3485*62500000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26703563 62500000 33279312157951 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100845227/250000000 : ℝ)^4509 ≤ (3861645591023/12500000000000 : ℝ)^3485 := by
    have hnat : (100845227 : ℕ)^4509*12500000000000^3485 ≤ 3861645591023^3485*250000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100845227 250000000 3861645591023 12500000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452329337/1000000000 : ℝ)^4509 ≤ (35827523099777/100000000000000 : ℝ)^3485 := by
    have hnat : (452329337 : ℕ)^4509*100000000000000^3485 ≤ 35827523099777^3485*1000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452329337 1000000000 35827523099777 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26703563/62500000 : ℝ), (100845227/250000000 : ℝ), (452329337/1000000000 : ℝ)] ![(33279312157951/100000000000000 : ℝ), (3861645591023/12500000000000 : ℝ), (35827523099777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26703563/62500000 : ℝ)|^4509 ≤ (33279312157951/100000000000000 : ℝ)^3485
        have hw : |(26703563/62500000 : ℝ)|=(26703563/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(100845227/250000000 : ℝ)|^4509 ≤ (3861645591023/12500000000000 : ℝ)^3485
        have hw : |(100845227/250000000 : ℝ)|=(100845227/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(452329337/1000000000 : ℝ)|^4509 ≤ (35827523099777/100000000000000 : ℝ)^3485
        have hw : |(452329337/1000000000 : ℝ)|=(452329337/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s5_4 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1876940217/10000000000 : ℝ)*x 0 + (1043679913/2000000000 : ℝ)*x 1 + (217317573/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1876940217/10000000000 : ℝ)^4509 ≤ (11480686871687/100000000000000 : ℝ)^3485 := by
    have hnat : (1876940217 : ℕ)^4509*100000000000000^3485 ≤ 11480686871687^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876940217 10000000000 11480686871687 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043679913/2000000000 : ℝ)^4509 ≤ (10776584358037/25000000000000 : ℝ)^3485 := by
    have hnat : (1043679913 : ℕ)^4509*25000000000000^3485 ≤ 10776584358037^3485*2000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043679913 2000000000 10776584358037 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217317573/400000000 : ℝ)^4509 ≤ (9082595137407/20000000000000 : ℝ)^3485 := by
    have hnat : (217317573 : ℕ)^4509*20000000000000^3485 ≤ 9082595137407^3485*400000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217317573 400000000 9082595137407 20000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1876940217/10000000000 : ℝ), (1043679913/2000000000 : ℝ), (217317573/400000000 : ℝ)] ![(11480686871687/100000000000000 : ℝ), (10776584358037/25000000000000 : ℝ), (9082595137407/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1876940217/10000000000 : ℝ)|^4509 ≤ (11480686871687/100000000000000 : ℝ)^3485
        have hw : |(-1876940217/10000000000 : ℝ)|=(1876940217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043679913/2000000000 : ℝ)|^4509 ≤ (10776584358037/25000000000000 : ℝ)^3485
        have hw : |(1043679913/2000000000 : ℝ)|=(1043679913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217317573/400000000 : ℝ)|^4509 ≤ (9082595137407/20000000000000 : ℝ)^3485
        have hw : |(217317573/400000000 : ℝ)|=(217317573/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s5_5 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264753989/500000000 : ℝ)*x 0 + (-221536759/1250000000 : ℝ)*x 1 + (2716469663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264753989/500000000 : ℝ)^4509 ≤ (4392763001351/10000000000000 : ℝ)^3485 := by
    have hnat : (264753989 : ℕ)^4509*10000000000000^3485 ≤ 4392763001351^3485*500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264753989 500000000 4392763001351 10000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221536759/1250000000 : ℝ)^4509 ≤ (333106070951/3125000000000 : ℝ)^3485 := by
    have hnat : (221536759 : ℕ)^4509*3125000000000^3485 ≤ 333106070951^3485*1250000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221536759 1250000000 333106070951 3125000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716469663/5000000000 : ℝ)^4509 ≤ (908259513957/2000000000000 : ℝ)^3485 := by
    have hnat : (2716469663 : ℕ)^4509*2000000000000^3485 ≤ 908259513957^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716469663 5000000000 908259513957 2000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264753989/500000000 : ℝ), (-221536759/1250000000 : ℝ), (2716469663/5000000000 : ℝ)] ![(4392763001351/10000000000000 : ℝ), (333106070951/3125000000000 : ℝ), (908259513957/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264753989/500000000 : ℝ)|^4509 ≤ (4392763001351/10000000000000 : ℝ)^3485
        have hw : |(264753989/500000000 : ℝ)|=(264753989/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-221536759/1250000000 : ℝ)|^4509 ≤ (333106070951/3125000000000 : ℝ)^3485
        have hw : |(-221536759/1250000000 : ℝ)|=(221536759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716469663/5000000000 : ℝ)|^4509 ≤ (908259513957/2000000000000 : ℝ)^3485
        have hw : |(2716469663/5000000000 : ℝ)|=(2716469663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s5_6 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264753989/500000000 : ℝ)*x 0 + (2716469663/5000000000 : ℝ)*x 1 + (-221536759/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264753989/500000000 : ℝ)^4509 ≤ (4392763001351/10000000000000 : ℝ)^3485 := by
    have hnat : (264753989 : ℕ)^4509*10000000000000^3485 ≤ 4392763001351^3485*500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264753989 500000000 4392763001351 10000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716469663/5000000000 : ℝ)^4509 ≤ (908259513957/2000000000000 : ℝ)^3485 := by
    have hnat : (2716469663 : ℕ)^4509*2000000000000^3485 ≤ 908259513957^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716469663 5000000000 908259513957 2000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221536759/1250000000 : ℝ)^4509 ≤ (333106070951/3125000000000 : ℝ)^3485 := by
    have hnat : (221536759 : ℕ)^4509*3125000000000^3485 ≤ 333106070951^3485*1250000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221536759 1250000000 333106070951 3125000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264753989/500000000 : ℝ), (2716469663/5000000000 : ℝ), (-221536759/1250000000 : ℝ)] ![(4392763001351/10000000000000 : ℝ), (908259513957/2000000000000 : ℝ), (333106070951/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264753989/500000000 : ℝ)|^4509 ≤ (4392763001351/10000000000000 : ℝ)^3485
        have hw : |(264753989/500000000 : ℝ)|=(264753989/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716469663/5000000000 : ℝ)|^4509 ≤ (908259513957/2000000000000 : ℝ)^3485
        have hw : |(2716469663/5000000000 : ℝ)|=(2716469663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-221536759/1250000000 : ℝ)|^4509 ≤ (333106070951/3125000000000 : ℝ)^3485
        have hw : |(-221536759/1250000000 : ℝ)|=(221536759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s5_7 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4272636103/10000000000 : ℝ)*x 0 + (1130194009/2500000000 : ℝ)*x 1 + (4036344973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4272636103/10000000000 : ℝ)^4509 ≤ (33279977521247/100000000000000 : ℝ)^3485 := by
    have hnat : (4272636103 : ℕ)^4509*100000000000000^3485 ≤ 33279977521247^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4272636103 10000000000 33279977521247 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130194009/2500000000 : ℝ)^4509 ≤ (1432069101953/4000000000000 : ℝ)^3485 := by
    have hnat : (1130194009 : ℕ)^4509*4000000000000^3485 ≤ 1432069101953^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130194009 2500000000 1432069101953 4000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4036344973/10000000000 : ℝ)^4509 ≤ (30918294904881/100000000000000 : ℝ)^3485 := by
    have hnat : (4036344973 : ℕ)^4509*100000000000000^3485 ≤ 30918294904881^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4036344973 10000000000 30918294904881 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4272636103/10000000000 : ℝ), (1130194009/2500000000 : ℝ), (4036344973/10000000000 : ℝ)] ![(33279977521247/100000000000000 : ℝ), (1432069101953/4000000000000 : ℝ), (30918294904881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4272636103/10000000000 : ℝ)|^4509 ≤ (33279977521247/100000000000000 : ℝ)^3485
        have hw : |(4272636103/10000000000 : ℝ)|=(4272636103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130194009/2500000000 : ℝ)|^4509 ≤ (1432069101953/4000000000000 : ℝ)^3485
        have hw : |(1130194009/2500000000 : ℝ)|=(1130194009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4036344973/10000000000 : ℝ)|^4509 ≤ (30918294904881/100000000000000 : ℝ)^3485
        have hw : |(4036344973/10000000000 : ℝ)|=(4036344973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1506_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2721/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2723/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7741/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2721/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2721/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2721/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2721/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2721/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2721/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2721/25000 : ℝ) ^ (4507/1024 : ℝ) ≤ (2880863355018881/50000000000000000000 : ℝ) := by
    have hpowers : (2721/25000 : ℝ)^4507 ≤ (2880863355018881/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2721 : ℕ)^4507*50000000000000000000^1024 ≤ 2880863355018881^1024*25000^4507 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2721 25000 2880863355018881 50000000000000000000 4507 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2721/25000 : ℝ)) (X := (2880863355018881/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4507/1024 : ℝ) ≤ (27234467398611441/100000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4507 ≤ (27234467398611441/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4507*100000000000000000000^1024 ≤ 27234467398611441^1024*10000^4507 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 27234467398611441 100000000000000000000 4507 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (27234467398611441/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002880863355018881/25000000000000000000 : ℝ) ≤ (10000261803659297/10000000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (25002880863355018881/25000000000000000000 : ℝ)^1024 ≤ (10000261803659297/10000000000000000 : ℝ)^4507 := by
      have hnat : (25002880863355018881 : ℕ)^1024*10000000000000000^4507 ≤ 10000261803659297^4507*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002880863355018881 25000000000000000000 10000261803659297 10000000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000261803659297/10000000000000000 : ℝ)) (X := (25002880863355018881/25000000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100032996194108649203/100000000000000000000 : ℝ) ≤ (5000374792497529/5000000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (100032996194108649203/100000000000000000000 : ℝ)^1024 ≤ (5000374792497529/5000000000000000 : ℝ)^4507 := by
      have hnat : (100032996194108649203 : ℕ)^1024*5000000000000000^4507 ≤ 5000374792497529^4507*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100032996194108649203 100000000000000000000 5000374792497529 5000000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000374792497529/5000000000000000 : ℝ)) (X := (100032996194108649203/100000000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027234467398611441/50000000000000000000 : ℝ) ≤ (10001237366330819/10000000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (50027234467398611441/50000000000000000000 : ℝ)^1024 ≤ (10001237366330819/10000000000000000 : ℝ)^4507 := by
      have hnat : (50027234467398611441 : ℕ)^1024*10000000000000000^4507 ≤ 10001237366330819^4507*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027234467398611441 50000000000000000000 10001237366330819 10000000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001237366330819/10000000000000000 : ℝ)) (X := (50027234467398611441/50000000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2880863355018881/50000000000000000000 : ℝ) ≤ ((23025293921768938267/23030000000000000000 : ℝ)+2*(487781335761/460600000000000 : ℝ)*(2721/25000 : ℝ))^(4507/1024 : ℝ) := by
    rw [show (23025293921768938267/23030000000000000000 : ℝ)+2*(487781335761/460600000000000 : ℝ)*(2721/25000 : ℝ)=(10000261803659297/10000000000000000 : ℝ) by norm_num, show 1+2*(2880863355018881/50000000000000000000 : ℝ)=(25002880863355018881/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27234467398611441/100000000000000000000 : ℝ)+(2880863355018881/50000000000000000000 : ℝ) ≤ ((23025293921768938267/23030000000000000000 : ℝ)+(487781335761/460600000000000 : ℝ)*((1549/10000 : ℝ)+(2721/25000 : ℝ)))^(4507/1024 : ℝ) := by
    rw [show (23025293921768938267/23030000000000000000 : ℝ)+(487781335761/460600000000000 : ℝ)*((1549/10000 : ℝ)+(2721/25000 : ℝ))=(5000374792497529/5000000000000000 : ℝ) by norm_num, show 1+(27234467398611441/100000000000000000000 : ℝ)+(2880863355018881/50000000000000000000 : ℝ)=(100032996194108649203/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27234467398611441/100000000000000000000 : ℝ) ≤ ((23025293921768938267/23030000000000000000 : ℝ)+2*(487781335761/460600000000000 : ℝ)*(1549/10000 : ℝ))^(4507/1024 : ℝ) := by
    rw [show (23025293921768938267/23030000000000000000 : ℝ)+2*(487781335761/460600000000000 : ℝ)*(1549/10000 : ℝ)=(10001237366330819/10000000000000000 : ℝ) by norm_num, show 1+2*(27234467398611441/100000000000000000000 : ℝ)=(50027234467398611441/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23025293921768938267/23030000000000000000 : ℝ)*(X 1 0+X 2 0)+(487781335761/460600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (2721/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (23025293921768938267/23030000000000000000 : ℝ)) (alpha := (487781335761/460600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23025293921768938267/23030000000000000000 : ℝ)*(X 0 1+X 2 1)+(487781335761/460600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (2721/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (23025293921768938267/23030000000000000000 : ℝ)) (alpha := (487781335761/460600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23025293921768938267/23030000000000000000 : ℝ)*(X 0 2+X 1 2)+(487781335761/460600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (2721/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (23025293921768938267/23030000000000000000 : ℝ)) (alpha := (487781335761/460600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-938455671/5000000000 : ℝ)*X 0 0+(5434062647/10000000000 : ℝ)*X 0 1+(5217284177/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351934589/10000000000 : ℝ)*X 1 0+(-1987949111/10000000000 : ℝ)*X 1 1+(5217284269/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66899177/125000000 : ℝ)*X 2 0+(1304321227/2500000000 : ℝ)*X 2 1+(-1987948837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((26703563/62500000 : ℝ)*X 0 0+(100845227/250000000 : ℝ)*X 0 1+(452329337/1000000000 : ℝ)*X 0 2+(26703563/62500000 : ℝ)*X 1 0+(100845227/250000000 : ℝ)*X 1 1+(452329337/1000000000 : ℝ)*X 1 2+(26703563/62500000 : ℝ)*X 2 0+(100845227/250000000 : ℝ)*X 2 1+(452329337/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1876940217/10000000000 : ℝ)*X 0 0+(1043679913/2000000000 : ℝ)*X 0 1+(217317573/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((264753989/500000000 : ℝ)*X 1 0+(-221536759/1250000000 : ℝ)*X 1 1+(2716469663/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((264753989/500000000 : ℝ)*X 2 0+(2716469663/5000000000 : ℝ)*X 2 1+(-221536759/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4272636103/10000000000 : ℝ)*X 0 0+(1130194009/2500000000 : ℝ)*X 0 1+(4036344973/10000000000 : ℝ)*X 0 2+(4272636103/10000000000 : ℝ)*X 1 0+(1130194009/2500000000 : ℝ)*X 1 1+(4036344973/10000000000 : ℝ)*X 1 2+(4272636103/10000000000 : ℝ)*X 2 0+(1130194009/2500000000 : ℝ)*X 2 1+(4036344973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2793045099642727616333715849/1151500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (901580209/100000000000000 : ℝ)*(base19) + (61408027/25000000000000 : ℝ)*(base23) + (71387581/50000000000000 : ℝ)*(upper3) + (153159991/100000000000000 : ℝ)*(upper4) + (143691003/100000000000000 : ℝ)*(upper5) + (66560061432929/2000000000000 : ℝ)*(major0) + (66560061432929/2000000000000 : ℝ)*(major1) + (3328003071646451/100000000000000 : ℝ)*(major2) + (922603700352237/20000000000000 : ℝ)*(sp0) + (4613032942496587/100000000000000 : ℝ)*(sp1) + (4613033598444687/100000000000000 : ℝ)*(sp2) + (2042969387915639/100000000000000 : ℝ)*(sp3) + (1534231561/10000000000000 : ℝ)*(sp4) + (1415224043/50000000000000 : ℝ)*(sp7) + (81718888734549/4000000000000 : ℝ)*(f.failure) + (1153258461019199/25000000000000 : ℝ)*(f.sum) + (95648853755619/46060000000000000000000000000 : ℝ)*base66 + (170028454056545043/46060000000000000000000000000000 : ℝ)*base67 + (33518644263582140417/2303000000000000000000000000000000 : ℝ)*base69 + (126670234166945043/46060000000000000000000000000000 : ℝ)*base71 + (194192782915121/46060000000000000000000000000 : ℝ)*base73 + (25049000404458140417/2303000000000000000000000000000000 : ℝ)*base75 + (9826988725509149/6580000000000000000000000000000 : ℝ)*base77 + (133986225275389149/6580000000000000000000000000000 : ℝ)*base79 + (5089943023439/1151500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (30863/80000000000000000000 : ℝ)*base90 + (30863/80000000000000000000 : ℝ)*base92 + (830863/80000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (183797619747459272729337/23030000000000000000000000000 : ℝ) := by norm_num
    linear_combination (326124147/25000000000000 : ℝ)*(base19) + (1414899751/100000000000000 : ℝ)*(base23) + (430735907/100000000000000 : ℝ)*(lower1) + (10343857/6250000000000 : ℝ)*(upper3) + (389067/781250000000 : ℝ)*(lower4) + (164177469/100000000000000 : ℝ)*(upper5) + (3362694019889719/100000000000000 : ℝ)*(major0) + (3362694019889719/100000000000000 : ℝ)*(major1) + (3362694019889719/100000000000000 : ℝ)*(major2) + (380743711/25000000000000 : ℝ)*(sp2) + (2330559854305787/50000000000000 : ℝ)*(sp4) + (4661118404114987/100000000000000 : ℝ)*(sp5) + (233055838536849/5000000000000 : ℝ)*(sp6) + (2064268065141483/100000000000000 : ℝ)*(sp7) + (2064268065141483/100000000000000 : ℝ)*(f.failure) + (2330559854305787/50000000000000 : ℝ)*(f.sum) + (132231415127571/23030000000000000000000000000 : ℝ)*base66 + (4322393399339581861/329000000000000000000000000000000 : ℝ)*base68 + (780562478841418139/329000000000000000000000000000000 : ℝ)*base69 + (302920423058581861/329000000000000000000000000000000 : ℝ)*base72 + (101915628159439/23030000000000000000000000000 : ℝ)*base73 + (266160710093418139/329000000000000000000000000000000 : ℝ)*base75 + (1519123498121418139/329000000000000000000000000000000 : ℝ)*base77 + (701341927077581861/329000000000000000000000000000000 : ℝ)*base80 + (67956683670971/23030000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (17020721/2000000000000000000000 : ℝ)*base90 + (17020721/2000000000000000000000 : ℝ)*base92 + (17020721/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1506_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2721/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2723/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1506_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1506_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (801/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2723/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1506_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1506_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1506_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (801/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2723/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1506_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

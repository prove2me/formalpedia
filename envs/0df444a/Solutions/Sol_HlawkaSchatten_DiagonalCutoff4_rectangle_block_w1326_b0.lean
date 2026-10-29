-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1326_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:45:29.236461+00:00
-- url     : https://prove2.me/submissions/d6927769-0710-44fd-ac3e-8dc7b1954285

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
theorem support_rectangle_w1326_s0_0 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-4546607/25000000 : ℝ)*x 0 + (1200771199/2000000000 : ℝ)*x 1 + (961415431/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4546607/25000000 : ℝ)^2143 ≤ (5325236691641/50000000000000 : ℝ)^1631 := by
    have hnat : (4546607 : ℕ)^2143*50000000000000^1631 ≤ 5325236691641^1631*25000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4546607 25000000 5325236691641 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1200771199/2000000000 : ℝ)^2143 ≤ (25576762980097/50000000000000 : ℝ)^1631 := by
    have hnat : (1200771199 : ℕ)^2143*50000000000000^1631 ≤ 25576762980097^1631*2000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200771199 2000000000 25576762980097 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (961415431/2000000000 : ℝ)^2143 ≤ (38196000638683/100000000000000 : ℝ)^1631 := by
    have hnat : (961415431 : ℕ)^2143*100000000000000^1631 ≤ 38196000638683^1631*2000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961415431 2000000000 38196000638683 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4546607/25000000 : ℝ), (1200771199/2000000000 : ℝ), (961415431/2000000000 : ℝ)] ![(5325236691641/50000000000000 : ℝ), (25576762980097/50000000000000 : ℝ), (38196000638683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4546607/25000000 : ℝ)|^2143 ≤ (5325236691641/50000000000000 : ℝ)^1631
        have hw : |(-4546607/25000000 : ℝ)|=(4546607/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1200771199/2000000000 : ℝ)|^2143 ≤ (25576762980097/50000000000000 : ℝ)^1631
        have hw : |(1200771199/2000000000 : ℝ)|=(1200771199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(961415431/2000000000 : ℝ)|^2143 ≤ (38196000638683/100000000000000 : ℝ)^1631
        have hw : |(961415431/2000000000 : ℝ)|=(961415431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s0_1 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (550360543/1000000000 : ℝ)*x 0 + (-624920323/2500000000 : ℝ)*x 1 + (1201769347/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550360543/1000000000 : ℝ)^2143 ≤ (45628043574381/100000000000000 : ℝ)^1631 := by
    have hnat : (550360543 : ℕ)^2143*100000000000000^1631 ≤ 45628043574381^1631*1000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550360543 1000000000 45628043574381 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (624920323/2500000000 : ℝ)^2143 ≤ (16175953340371/100000000000000 : ℝ)^1631 := by
    have hnat : (624920323 : ℕ)^2143*100000000000000^1631 ≤ 16175953340371^1631*2500000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624920323 2500000000 16175953340371 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1201769347/2500000000 : ℝ)^2143 ≤ (38196003071229/100000000000000 : ℝ)^1631 := by
    have hnat : (1201769347 : ℕ)^2143*100000000000000^1631 ≤ 38196003071229^1631*2500000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201769347 2500000000 38196003071229 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(550360543/1000000000 : ℝ), (-624920323/2500000000 : ℝ), (1201769347/2500000000 : ℝ)] ![(45628043574381/100000000000000 : ℝ), (16175953340371/100000000000000 : ℝ), (38196003071229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(550360543/1000000000 : ℝ)|^2143 ≤ (45628043574381/100000000000000 : ℝ)^1631
        have hw : |(550360543/1000000000 : ℝ)|=(550360543/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-624920323/2500000000 : ℝ)|^2143 ≤ (16175953340371/100000000000000 : ℝ)^1631
        have hw : |(-624920323/2500000000 : ℝ)|=(624920323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1201769347/2500000000 : ℝ)|^2143 ≤ (38196003071229/100000000000000 : ℝ)^1631
        have hw : |(1201769347/2500000000 : ℝ)|=(1201769347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s0_2 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2751802387/5000000000 : ℝ)*x 0 + (240353881/500000000 : ℝ)*x 1 + (-312460231/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2751802387/5000000000 : ℝ)^2143 ≤ (45628036428487/100000000000000 : ℝ)^1631 := by
    have hnat : (2751802387 : ℕ)^2143*100000000000000^1631 ≤ 45628036428487^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751802387 5000000000 45628036428487 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (240353881/500000000 : ℝ)^2143 ≤ (19098002746667/50000000000000 : ℝ)^1631 := by
    have hnat : (240353881 : ℕ)^2143*50000000000000^1631 ≤ 19098002746667^1631*500000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240353881 500000000 19098002746667 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (312460231/1250000000 : ℝ)^2143 ≤ (3235191613567/20000000000000 : ℝ)^1631 := by
    have hnat : (312460231 : ℕ)^2143*20000000000000^1631 ≤ 3235191613567^1631*1250000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312460231 1250000000 3235191613567 20000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2751802387/5000000000 : ℝ), (240353881/500000000 : ℝ), (-312460231/1250000000 : ℝ)] ![(45628036428487/100000000000000 : ℝ), (19098002746667/50000000000000 : ℝ), (3235191613567/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2751802387/5000000000 : ℝ)|^2143 ≤ (45628036428487/100000000000000 : ℝ)^1631
        have hw : |(2751802387/5000000000 : ℝ)|=(2751802387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(240353881/500000000 : ℝ)|^2143 ≤ (19098002746667/50000000000000 : ℝ)^1631
        have hw : |(240353881/500000000 : ℝ)|=(240353881/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-312460231/1250000000 : ℝ)|^2143 ≤ (3235191613567/20000000000000 : ℝ)^1631
        have hw : |(-312460231/1250000000 : ℝ)|=(312460231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s0_3 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (836230371/2000000000 : ℝ)*x 0 + (3107398161/10000000000 : ℝ)*x 1 + (1119810951/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836230371/2000000000 : ℝ)^2143 ≤ (31799037879481/100000000000000 : ℝ)^1631 := by
    have hnat : (836230371 : ℕ)^2143*100000000000000^1631 ≤ 31799037879481^1631*2000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836230371 2000000000 31799037879481 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3107398161/10000000000 : ℝ)^2143 ≤ (21530357251891/100000000000000 : ℝ)^1631 := by
    have hnat : (3107398161 : ℕ)^2143*100000000000000^1631 ≤ 21530357251891^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3107398161 10000000000 21530357251891 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119810951/2000000000 : ℝ)^2143 ≤ (46670604859247/100000000000000 : ℝ)^1631 := by
    have hnat : (1119810951 : ℕ)^2143*100000000000000^1631 ≤ 46670604859247^1631*2000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119810951 2000000000 46670604859247 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(836230371/2000000000 : ℝ), (3107398161/10000000000 : ℝ), (1119810951/2000000000 : ℝ)] ![(31799037879481/100000000000000 : ℝ), (21530357251891/100000000000000 : ℝ), (46670604859247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(836230371/2000000000 : ℝ)|^2143 ≤ (31799037879481/100000000000000 : ℝ)^1631
        have hw : |(836230371/2000000000 : ℝ)|=(836230371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3107398161/10000000000 : ℝ)|^2143 ≤ (21530357251891/100000000000000 : ℝ)^1631
        have hw : |(3107398161/10000000000 : ℝ)|=(3107398161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119810951/2000000000 : ℝ)|^2143 ≤ (46670604859247/100000000000000 : ℝ)^1631
        have hw : |(1119810951/2000000000 : ℝ)|=(1119810951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s0_4 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-911591963/5000000000 : ℝ)*x 0 + (2418953981/5000000000 : ℝ)*x 1 + (2985962651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (911591963/5000000000 : ℝ)^2143 ≤ (10685429513307/100000000000000 : ℝ)^1631 := by
    have hnat : (911591963 : ℕ)^2143*100000000000000^1631 ≤ 10685429513307^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911591963 5000000000 10685429513307 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2418953981/5000000000 : ℝ)^2143 ≤ (38518201158617/100000000000000 : ℝ)^1631 := by
    have hnat : (2418953981 : ℕ)^2143*100000000000000^1631 ≤ 38518201158617^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2418953981 5000000000 38518201158617 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2985962651/5000000000 : ℝ)^2143 ≤ (50796369315421/100000000000000 : ℝ)^1631 := by
    have hnat : (2985962651 : ℕ)^2143*100000000000000^1631 ≤ 50796369315421^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2985962651 5000000000 50796369315421 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-911591963/5000000000 : ℝ), (2418953981/5000000000 : ℝ), (2985962651/5000000000 : ℝ)] ![(10685429513307/100000000000000 : ℝ), (38518201158617/100000000000000 : ℝ), (50796369315421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-911591963/5000000000 : ℝ)|^2143 ≤ (10685429513307/100000000000000 : ℝ)^1631
        have hw : |(-911591963/5000000000 : ℝ)|=(911591963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2418953981/5000000000 : ℝ)|^2143 ≤ (38518201158617/100000000000000 : ℝ)^1631
        have hw : |(2418953981/5000000000 : ℝ)|=(2418953981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2985962651/5000000000 : ℝ)|^2143 ≤ (50796369315421/100000000000000 : ℝ)^1631
        have hw : |(2985962651/5000000000 : ℝ)|=(2985962651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s0_5 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2588774717/5000000000 : ℝ)*x 0 + (-4171357/31250000 : ℝ)*x 1 + (5971925223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2588774717/5000000000 : ℝ)^2143 ≤ (10527439775519/25000000000000 : ℝ)^1631 := by
    have hnat : (2588774717 : ℕ)^2143*25000000000000^1631 ≤ 10527439775519^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588774717 5000000000 10527439775519 25000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171357/31250000 : ℝ)^2143 ≤ (7093872455361/100000000000000 : ℝ)^1631 := by
    have hnat : (4171357 : ℕ)^2143*100000000000000^1631 ≤ 7093872455361^1631*31250000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171357 31250000 7093872455361 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5971925223/10000000000 : ℝ)^2143 ≤ (50796368432517/100000000000000 : ℝ)^1631 := by
    have hnat : (5971925223 : ℕ)^2143*100000000000000^1631 ≤ 50796368432517^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5971925223 10000000000 50796368432517 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2588774717/5000000000 : ℝ), (-4171357/31250000 : ℝ), (5971925223/10000000000 : ℝ)] ![(10527439775519/25000000000000 : ℝ), (7093872455361/100000000000000 : ℝ), (50796368432517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2588774717/5000000000 : ℝ)|^2143 ≤ (10527439775519/25000000000000 : ℝ)^1631
        have hw : |(2588774717/5000000000 : ℝ)|=(2588774717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4171357/31250000 : ℝ)|^2143 ≤ (7093872455361/100000000000000 : ℝ)^1631
        have hw : |(-4171357/31250000 : ℝ)|=(4171357/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5971925223/10000000000 : ℝ)|^2143 ≤ (50796368432517/100000000000000 : ℝ)^1631
        have hw : |(5971925223/10000000000 : ℝ)|=(5971925223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s0_6 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (258877473/500000000 : ℝ)*x 0 + (5971925273/10000000000 : ℝ)*x 1 + (-1334834119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258877473/500000000 : ℝ)^2143 ≤ (42109759379919/100000000000000 : ℝ)^1631 := by
    have hnat : (258877473 : ℕ)^2143*100000000000000^1631 ≤ 42109759379919^1631*500000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258877473 500000000 42109759379919 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5971925273/10000000000 : ℝ)^2143 ≤ (50796368991317/100000000000000 : ℝ)^1631 := by
    have hnat : (5971925273 : ℕ)^2143*100000000000000^1631 ≤ 50796368991317^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5971925273 10000000000 50796368991317 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1334834119/10000000000 : ℝ)^2143 ≤ (1773467902613/25000000000000 : ℝ)^1631 := by
    have hnat : (1334834119 : ℕ)^2143*25000000000000^1631 ≤ 1773467902613^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334834119 10000000000 1773467902613 25000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(258877473/500000000 : ℝ), (5971925273/10000000000 : ℝ), (-1334834119/10000000000 : ℝ)] ![(42109759379919/100000000000000 : ℝ), (50796368991317/100000000000000 : ℝ), (1773467902613/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(258877473/500000000 : ℝ)|^2143 ≤ (42109759379919/100000000000000 : ℝ)^1631
        have hw : |(258877473/500000000 : ℝ)|=(258877473/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5971925273/10000000000 : ℝ)|^2143 ≤ (50796368991317/100000000000000 : ℝ)^1631
        have hw : |(5971925273/10000000000 : ℝ)|=(5971925273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1334834119/10000000000 : ℝ)|^2143 ≤ (1773467902613/25000000000000 : ℝ)^1631
        have hw : |(-1334834119/10000000000 : ℝ)|=(1334834119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s0_7 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (261912847/625000000 : ℝ)*x 0 + (2767433287/5000000000 : ℝ)*x 1 + (1586938057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261912847/625000000 : ℝ)^2143 ≤ (31893540085553/100000000000000 : ℝ)^1631 := by
    have hnat : (261912847 : ℕ)^2143*100000000000000^1631 ≤ 31893540085553^1631*625000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261912847 625000000 31893540085553 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2767433287/5000000000 : ℝ)^2143 ≤ (45968878549271/100000000000000 : ℝ)^1631 := by
    have hnat : (2767433287 : ℕ)^2143*100000000000000^1631 ≤ 45968878549271^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2767433287 5000000000 45968878549271 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1586938057/5000000000 : ℝ)^2143 ≤ (11068790678303/50000000000000 : ℝ)^1631 := by
    have hnat : (1586938057 : ℕ)^2143*50000000000000^1631 ≤ 11068790678303^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1586938057 5000000000 11068790678303 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261912847/625000000 : ℝ), (2767433287/5000000000 : ℝ), (1586938057/5000000000 : ℝ)] ![(31893540085553/100000000000000 : ℝ), (45968878549271/100000000000000 : ℝ), (11068790678303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261912847/625000000 : ℝ)|^2143 ≤ (31893540085553/100000000000000 : ℝ)^1631
        have hw : |(261912847/625000000 : ℝ)|=(261912847/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2767433287/5000000000 : ℝ)|^2143 ≤ (45968878549271/100000000000000 : ℝ)^1631
        have hw : |(2767433287/5000000000 : ℝ)|=(2767433287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1586938057/5000000000 : ℝ)|^2143 ≤ (11068790678303/50000000000000 : ℝ)^1631
        have hw : |(1586938057/5000000000 : ℝ)|=(1586938057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1326_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15409851/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1293/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26987/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4285/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4285 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4285*1^1024 ≤ 0^1024*1^4285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4285 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4285/1024 : ℝ) ≤ (2161683230864786709/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4285 ≤ (2161683230864786709/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4285*100000000000000000000^1024 ≤ 2161683230864786709^1024*5^4285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2161683230864786709 100000000000000000000 4285 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2161683230864786709/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4285/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4285 := by
      have hnat : (1 : ℕ)^1024*1^4285 ≤ 1^4285*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102161683230864786709/100000000000000000000 : ℝ) ≤ (10051238824317259/10000000000000000 : ℝ) ^ (4285/1024 : ℝ) := by
    have hpowers : (102161683230864786709/100000000000000000000 : ℝ)^1024 ≤ (10051238824317259/10000000000000000 : ℝ)^4285 := by
      have hnat : (102161683230864786709 : ℕ)^1024*10000000000000000^4285 ≤ 10051238824317259^4285*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102161683230864786709 100000000000000000000 10051238824317259 10000000000000000 1024 4285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10051238824317259/10000000000000000 : ℝ)) (X := (102161683230864786709/100000000000000000000 : ℝ)) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52161683230864786709/50000000000000000000 : ℝ) ≤ (5051238824317259/5000000000000000 : ℝ) ^ (4285/1024 : ℝ) := by
    have hpowers : (52161683230864786709/50000000000000000000 : ℝ)^1024 ≤ (5051238824317259/5000000000000000 : ℝ)^4285 := by
      have hnat : (52161683230864786709 : ℕ)^1024*5000000000000000^4285 ≤ 5051238824317259^4285*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52161683230864786709 50000000000000000000 5051238824317259 5000000000000000 1024 4285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5051238824317259/5000000000000000 : ℝ)) (X := (52161683230864786709/50000000000000000000 : ℝ)) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(51238824317259/4000000000000000 : ℝ)*(0 : ℝ))^(4285/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(51238824317259/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2161683230864786709/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(51238824317259/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4285/1024 : ℝ) := by
    rw [show (1 : ℝ)+(51238824317259/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10051238824317259/10000000000000000 : ℝ) by norm_num, show 1+(2161683230864786709/100000000000000000000 : ℝ)+(0 : ℝ)=(102161683230864786709/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2161683230864786709/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(51238824317259/4000000000000000 : ℝ)*(2/5 : ℝ))^(4285/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(51238824317259/4000000000000000 : ℝ)*(2/5 : ℝ)=(5051238824317259/5000000000000000 : ℝ) by norm_num, show 1+2*(2161683230864786709/100000000000000000000 : ℝ)=(52161683230864786709/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(51238824317259/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4285/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (51238824317259/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(51238824317259/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4285/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (51238824317259/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(51238824317259/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4285/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (51238824317259/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-4546607/25000000 : ℝ)*X 0 0+(1200771199/2000000000 : ℝ)*X 0 1+(961415431/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((550360543/1000000000 : ℝ)*X 1 0+(-624920323/2500000000 : ℝ)*X 1 1+(1201769347/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2751802387/5000000000 : ℝ)*X 2 0+(240353881/500000000 : ℝ)*X 2 1+(-312460231/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((836230371/2000000000 : ℝ)*X 0 0+(3107398161/10000000000 : ℝ)*X 0 1+(1119810951/2000000000 : ℝ)*X 0 2+(836230371/2000000000 : ℝ)*X 1 0+(3107398161/10000000000 : ℝ)*X 1 1+(1119810951/2000000000 : ℝ)*X 1 2+(836230371/2000000000 : ℝ)*X 2 0+(3107398161/10000000000 : ℝ)*X 2 1+(1119810951/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-911591963/5000000000 : ℝ)*X 0 0+(2418953981/5000000000 : ℝ)*X 0 1+(2985962651/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2588774717/5000000000 : ℝ)*X 1 0+(-4171357/31250000 : ℝ)*X 1 1+(5971925223/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((258877473/500000000 : ℝ)*X 2 0+(5971925273/10000000000 : ℝ)*X 2 1+(-1334834119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((261912847/625000000 : ℝ)*X 0 0+(2767433287/5000000000 : ℝ)*X 0 1+(1586938057/5000000000 : ℝ)*X 0 2+(261912847/625000000 : ℝ)*X 1 0+(2767433287/5000000000 : ℝ)*X 1 1+(1586938057/5000000000 : ℝ)*X 1 2+(261912847/625000000 : ℝ)*X 2 0+(2767433287/5000000000 : ℝ)*X 2 1+(1586938057/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (388756178588467456384329/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (107035901/100000000000000 : ℝ)*(base1) + (1928636707/100000000000000 : ℝ)*(base19) + (457259819/25000000000000 : ℝ)*(base23) + (73220053/25000000000000 : ℝ)*(upper3) + (60032297/50000000000000 : ℝ)*(upper5) + (309233547182423/50000000000000 : ℝ)*(major0) + (309233547182423/50000000000000 : ℝ)*(major1) + (309233547182423/50000000000000 : ℝ)*(major2) + (835582948922539/100000000000000 : ℝ)*(sp0) + (835586722265797/100000000000000 : ℝ)*(sp1) + (835586821863227/100000000000000 : ℝ)*(sp2) + (100335501690237/25000000000000 : ℝ)*(sp3) + (1161803173/20000000000000 : ℝ)*(sp4) + (3164859541/100000000000000 : ℝ)*(sp7) + (40134527865639/10000000000000 : ℝ)*(f.failure) + (104448581362813/12500000000000 : ℝ)*(f.sum) + (10988602138557/100000000000000000000000000000 : ℝ)*base65 + (1893678580938557/200000000000000000000000000000 : ℝ)*base67 + (1714531262538557/200000000000000000000000000000 : ℝ)*base69 + (1722134523938557/200000000000000000000000000000 : ℝ)*base71 + (171596843461443/100000000000000000000000000000 : ℝ)*base74 + (538514170338557/200000000000000000000000000000 : ℝ)*base75 + (1438180926338557/200000000000000000000000000000 : ℝ)*base77 + (2697860319938557/200000000000000000000000000000 : ℝ)*base79 + (138264691461443/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (990211/100000000000000000000 : ℝ)*base90 + (990211/100000000000000000000 : ℝ)*base92 + (990211/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1544748490242132643807329/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1827869127/100000000000000 : ℝ)*(base19) + (1850310821/100000000000000 : ℝ)*(base23) + (74096617/100000000000000 : ℝ)*(base32) + (253834619/100000000000000 : ℝ)*(upper3) + (2349453/1250000000000 : ℝ)*(upper5) + (652685796983423/100000000000000 : ℝ)*(major0) + (652685796983423/100000000000000 : ℝ)*(major1) + (652685796983423/100000000000000 : ℝ)*(major2) + (2040946203/50000000000000 : ℝ)*(sp1) + (436794353/10000000000000 : ℝ)*(sp2) + (440910162773039/50000000000000 : ℝ)*(sp4) + (27556700493267/3125000000000 : ℝ)*(sp5) + (440907053645863/50000000000000 : ℝ)*(sp6) + (21177546843303/5000000000000 : ℝ)*(sp7) + (211775505481339/50000000000000 : ℝ)*(f.failure) + (440910162773039/50000000000000 : ℝ)*(f.sum) + (598395137397557/200000000000000000000000000000 : ℝ)*base65 + (1160019125397557/400000000000000000000000000000 : ℝ)*base67 + (225262842602443/400000000000000000000000000000 : ℝ)*base70 + (4062528597397557/400000000000000000000000000000 : ℝ)*base71 + (370724949802443/200000000000000000000000000000 : ℝ)*base74 + (2733295843797557/400000000000000000000000000000 : ℝ)*base75 + (1865061595797557/400000000000000000000000000000 : ℝ)*base77 + (6033652420597557/400000000000000000000000000000 : ℝ)*base79 + (668729885402443/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2270489/500000000000000000000 : ℝ)*base89 + (2270489/500000000000000000000 : ℝ)*base91 + (2270489/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1326_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15409851/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1293/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26987/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1326_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1326_s1_0 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-401153327/2000000000 : ℝ)*x 0 + (5649397847/10000000000 : ℝ)*x 1 + (2520857119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (401153327/2000000000 : ℝ)^2143 ≤ (6056528663391/50000000000000 : ℝ)^1631 := by
    have hnat : (401153327 : ℕ)^2143*50000000000000^1631 ≤ 6056528663391^1631*2000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401153327 2000000000 6056528663391 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5649397847/10000000000 : ℝ)^2143 ≤ (11805685840431/25000000000000 : ℝ)^1631 := by
    have hnat : (5649397847 : ℕ)^2143*25000000000000^1631 ≤ 11805685840431^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5649397847 10000000000 11805685840431 25000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2520857119/5000000000 : ℝ)^2143 ≤ (1016604982347/2500000000000 : ℝ)^1631 := by
    have hnat : (2520857119 : ℕ)^2143*2500000000000^1631 ≤ 1016604982347^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2520857119 5000000000 1016604982347 2500000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-401153327/2000000000 : ℝ), (5649397847/10000000000 : ℝ), (2520857119/5000000000 : ℝ)] ![(6056528663391/50000000000000 : ℝ), (11805685840431/25000000000000 : ℝ), (1016604982347/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-401153327/2000000000 : ℝ)|^2143 ≤ (6056528663391/50000000000000 : ℝ)^1631
        have hw : |(-401153327/2000000000 : ℝ)|=(401153327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5649397847/10000000000 : ℝ)|^2143 ≤ (11805685840431/25000000000000 : ℝ)^1631
        have hw : |(5649397847/10000000000 : ℝ)|=(5649397847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2520857119/5000000000 : ℝ)|^2143 ≤ (1016604982347/2500000000000 : ℝ)^1631
        have hw : |(2520857119/5000000000 : ℝ)|=(2520857119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s1_1 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (8651831/16000000 : ℝ)*x 0 + (-466098009/2000000000 : ℝ)*x 1 + (1260428577/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8651831/16000000 : ℝ)^2143 ≤ (44582891118459/100000000000000 : ℝ)^1631 := by
    have hnat : (8651831 : ℕ)^2143*100000000000000^1631 ≤ 44582891118459^1631*16000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8651831 16000000 44582891118459 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (466098009/2000000000 : ℝ)^2143 ≤ (3688227208427/25000000000000 : ℝ)^1631 := by
    have hnat : (466098009 : ℕ)^2143*25000000000000^1631 ≤ 3688227208427^1631*2000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466098009 2000000000 3688227208427 25000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1260428577/2500000000 : ℝ)^2143 ≤ (40664200035703/100000000000000 : ℝ)^1631 := by
    have hnat : (1260428577 : ℕ)^2143*100000000000000^1631 ≤ 40664200035703^1631*2500000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1260428577 2500000000 40664200035703 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8651831/16000000 : ℝ), (-466098009/2000000000 : ℝ), (1260428577/2500000000 : ℝ)] ![(44582891118459/100000000000000 : ℝ), (3688227208427/25000000000000 : ℝ), (40664200035703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8651831/16000000 : ℝ)|^2143 ≤ (44582891118459/100000000000000 : ℝ)^1631
        have hw : |(8651831/16000000 : ℝ)|=(8651831/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-466098009/2000000000 : ℝ)|^2143 ≤ (3688227208427/25000000000000 : ℝ)^1631
        have hw : |(-466098009/2000000000 : ℝ)|=(466098009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1260428577/2500000000 : ℝ)|^2143 ≤ (40664200035703/100000000000000 : ℝ)^1631
        have hw : |(1260428577/2500000000 : ℝ)|=(1260428577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s1_2 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5407394611/10000000000 : ℝ)*x 0 + (315107117/625000000 : ℝ)*x 1 + (-2330490293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5407394611/10000000000 : ℝ)^2143 ≤ (8916578735009/20000000000000 : ℝ)^1631 := by
    have hnat : (5407394611 : ℕ)^2143*20000000000000^1631 ≤ 8916578735009^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407394611 10000000000 8916578735009 20000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (315107117/625000000 : ℝ)^2143 ≤ (20332097707603/50000000000000 : ℝ)^1631 := by
    have hnat : (315107117 : ℕ)^2143*50000000000000^1631 ≤ 20332097707603^1631*625000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315107117 625000000 20332097707603 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2330490293/10000000000 : ℝ)^2143 ≤ (3688227724119/25000000000000 : ℝ)^1631 := by
    have hnat : (2330490293 : ℕ)^2143*25000000000000^1631 ≤ 3688227724119^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2330490293 10000000000 3688227724119 25000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5407394611/10000000000 : ℝ), (315107117/625000000 : ℝ), (-2330490293/10000000000 : ℝ)] ![(8916578735009/20000000000000 : ℝ), (20332097707603/50000000000000 : ℝ), (3688227724119/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5407394611/10000000000 : ℝ)|^2143 ≤ (8916578735009/20000000000000 : ℝ)^1631
        have hw : |(5407394611/10000000000 : ℝ)|=(5407394611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(315107117/625000000 : ℝ)|^2143 ≤ (20332097707603/50000000000000 : ℝ)^1631
        have hw : |(315107117/625000000 : ℝ)|=(315107117/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2330490293/10000000000 : ℝ)|^2143 ≤ (3688227724119/25000000000000 : ℝ)^1631
        have hw : |(-2330490293/10000000000 : ℝ)|=(2330490293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s1_3 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4295148561/10000000000 : ℝ)*x 0 + (463254103/1250000000 : ℝ)*x 1 + (1242803063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4295148561/10000000000 : ℝ)^2143 ≤ (16471513237989/50000000000000 : ℝ)^1631 := by
    have hnat : (4295148561 : ℕ)^2143*50000000000000^1631 ≤ 16471513237989^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4295148561 10000000000 16471513237989 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (463254103/1250000000 : ℝ)^2143 ≤ (5427654353491/20000000000000 : ℝ)^1631 := by
    have hnat : (463254103 : ℕ)^2143*20000000000000^1631 ≤ 5427654353491^1631*1250000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463254103 1250000000 5427654353491 20000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1242803063/2500000000 : ℝ)^2143 ≤ (399187017479/1000000000000 : ℝ)^1631 := by
    have hnat : (1242803063 : ℕ)^2143*1000000000000^1631 ≤ 399187017479^1631*2500000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1242803063 2500000000 399187017479 1000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4295148561/10000000000 : ℝ), (463254103/1250000000 : ℝ), (1242803063/2500000000 : ℝ)] ![(16471513237989/50000000000000 : ℝ), (5427654353491/20000000000000 : ℝ), (399187017479/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4295148561/10000000000 : ℝ)|^2143 ≤ (16471513237989/50000000000000 : ℝ)^1631
        have hw : |(4295148561/10000000000 : ℝ)|=(4295148561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(463254103/1250000000 : ℝ)|^2143 ≤ (5427654353491/20000000000000 : ℝ)^1631
        have hw : |(463254103/1250000000 : ℝ)|=(463254103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1242803063/2500000000 : ℝ)|^2143 ≤ (399187017479/1000000000000 : ℝ)^1631
        have hw : |(1242803063/2500000000 : ℝ)|=(1242803063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s1_4 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2006333547/10000000000 : ℝ)*x 0 + (504943323/1000000000 : ℝ)*x 1 + (5641536641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2006333547/10000000000 : ℝ)^2143 ≤ (12117555917623/100000000000000 : ℝ)^1631 := by
    have hnat : (2006333547 : ℕ)^2143*100000000000000^1631 ≤ 12117555917623^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006333547 10000000000 12117555917623 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (504943323/1000000000 : ℝ)^2143 ≤ (1273313147913/3125000000000 : ℝ)^1631 := by
    have hnat : (504943323 : ℕ)^2143*3125000000000^1631 ≤ 1273313147913^1631*1000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504943323 1000000000 1273313147913 3125000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5641536641/10000000000 : ℝ)^2143 ≤ (47136423339133/100000000000000 : ℝ)^1631 := by
    have hnat : (5641536641 : ℕ)^2143*100000000000000^1631 ≤ 47136423339133^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5641536641 10000000000 47136423339133 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2006333547/10000000000 : ℝ), (504943323/1000000000 : ℝ), (5641536641/10000000000 : ℝ)] ![(12117555917623/100000000000000 : ℝ), (1273313147913/3125000000000 : ℝ), (47136423339133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2006333547/10000000000 : ℝ)|^2143 ≤ (12117555917623/100000000000000 : ℝ)^1631
        have hw : |(-2006333547/10000000000 : ℝ)|=(2006333547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(504943323/1000000000 : ℝ)|^2143 ≤ (1273313147913/3125000000000 : ℝ)^1631
        have hw : |(504943323/1000000000 : ℝ)|=(504943323/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5641536641/10000000000 : ℝ)|^2143 ≤ (47136423339133/100000000000000 : ℝ)^1631
        have hw : |(5641536641/10000000000 : ℝ)|=(5641536641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s1_5 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1312480591/2500000000 : ℝ)*x 0 + (-1730667849/10000000000 : ℝ)*x 1 + (5641536181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312480591/2500000000 : ℝ)^2143 ≤ (21442424117297/50000000000000 : ℝ)^1631 := by
    have hnat : (1312480591 : ℕ)^2143*50000000000000^1631 ≤ 21442424117297^1631*2500000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312480591 2500000000 21442424117297 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1730667849/10000000000 : ℝ)^2143 ≤ (9978733464851/100000000000000 : ℝ)^1631 := by
    have hnat : (1730667849 : ℕ)^2143*100000000000000^1631 ≤ 9978733464851^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1730667849 10000000000 9978733464851 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5641536181/10000000000 : ℝ)^2143 ≤ (11784104572301/25000000000000 : ℝ)^1631 := by
    have hnat : (5641536181 : ℕ)^2143*25000000000000^1631 ≤ 11784104572301^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5641536181 10000000000 11784104572301 25000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312480591/2500000000 : ℝ), (-1730667849/10000000000 : ℝ), (5641536181/10000000000 : ℝ)] ![(21442424117297/50000000000000 : ℝ), (9978733464851/100000000000000 : ℝ), (11784104572301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312480591/2500000000 : ℝ)|^2143 ≤ (21442424117297/50000000000000 : ℝ)^1631
        have hw : |(1312480591/2500000000 : ℝ)|=(1312480591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1730667849/10000000000 : ℝ)|^2143 ≤ (9978733464851/100000000000000 : ℝ)^1631
        have hw : |(-1730667849/10000000000 : ℝ)|=(1730667849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5641536181/10000000000 : ℝ)|^2143 ≤ (11784104572301/25000000000000 : ℝ)^1631
        have hw : |(5641536181/10000000000 : ℝ)|=(5641536181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s1_6 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2624961037/5000000000 : ℝ)*x 0 + (1410384003/2500000000 : ℝ)*x 1 + (-216333563/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2624961037/5000000000 : ℝ)^2143 ≤ (21442422561019/50000000000000 : ℝ)^1631 := by
    have hnat : (2624961037 : ℕ)^2143*50000000000000^1631 ≤ 21442422561019^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624961037 5000000000 21442422561019 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1410384003/2500000000 : ℝ)^2143 ≤ (2946026027119/6250000000000 : ℝ)^1631 := by
    have hnat : (1410384003 : ℕ)^2143*6250000000000^1631 ≤ 2946026027119^1631*2500000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1410384003 2500000000 2946026027119 6250000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216333563/1250000000 : ℝ)^2143 ≤ (1247342303377/12500000000000 : ℝ)^1631 := by
    have hnat : (216333563 : ℕ)^2143*12500000000000^1631 ≤ 1247342303377^1631*1250000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216333563 1250000000 1247342303377 12500000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2624961037/5000000000 : ℝ), (1410384003/2500000000 : ℝ), (-216333563/1250000000 : ℝ)] ![(21442422561019/50000000000000 : ℝ), (2946026027119/6250000000000 : ℝ), (1247342303377/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2624961037/5000000000 : ℝ)|^2143 ≤ (21442422561019/50000000000000 : ℝ)^1631
        have hw : |(2624961037/5000000000 : ℝ)|=(2624961037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1410384003/2500000000 : ℝ)|^2143 ≤ (2946026027119/6250000000000 : ℝ)^1631
        have hw : |(1410384003/2500000000 : ℝ)|=(1410384003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-216333563/1250000000 : ℝ)|^2143 ≤ (1247342303377/12500000000000 : ℝ)^1631
        have hw : |(-216333563/1250000000 : ℝ)|=(216333563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s1_7 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2148164027/5000000000 : ℝ)*x 0 + (495514073/1000000000 : ℝ)*x 1 + (3722400829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148164027/5000000000 : ℝ)^2143 ≤ (1647745667419/5000000000000 : ℝ)^1631 := by
    have hnat : (2148164027 : ℕ)^2143*5000000000000^1631 ≤ 1647745667419^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148164027 5000000000 1647745667419 5000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (495514073/1000000000 : ℝ)^2143 ≤ (39749221643107/100000000000000 : ℝ)^1631 := by
    have hnat : (495514073 : ℕ)^2143*100000000000000^1631 ≤ 39749221643107^1631*1000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495514073 1000000000 39749221643107 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3722400829/10000000000 : ℝ)^2143 ≤ (13647932495631/50000000000000 : ℝ)^1631 := by
    have hnat : (3722400829 : ℕ)^2143*50000000000000^1631 ≤ 13647932495631^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3722400829 10000000000 13647932495631 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148164027/5000000000 : ℝ), (495514073/1000000000 : ℝ), (3722400829/10000000000 : ℝ)] ![(1647745667419/5000000000000 : ℝ), (39749221643107/100000000000000 : ℝ), (13647932495631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148164027/5000000000 : ℝ)|^2143 ≤ (1647745667419/5000000000000 : ℝ)^1631
        have hw : |(2148164027/5000000000 : ℝ)|=(2148164027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(495514073/1000000000 : ℝ)|^2143 ≤ (39749221643107/100000000000000 : ℝ)^1631
        have hw : |(495514073/1000000000 : ℝ)|=(495514073/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3722400829/10000000000 : ℝ)|^2143 ≤ (13647932495631/50000000000000 : ℝ)^1631
        have hw : |(3722400829/10000000000 : ℝ)|=(3722400829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1326_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15409851/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1293/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (6739/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19583/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1293/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1293/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1293/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1293/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26987/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1293/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26987/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1293/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1293/100000 : ℝ) ^ (4285/1024 : ℝ) ≤ (62635601657/5000000000000000000 : ℝ) := by
    have hpowers : (1293/100000 : ℝ)^4285 ≤ (62635601657/5000000000000000000 : ℝ)^1024 := by
      have hnat : (1293 : ℕ)^4285*5000000000000000000^1024 ≤ 62635601657^1024*100000^4285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1293 100000 62635601657 5000000000000000000 4285 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1293/100000 : ℝ)) (X := (62635601657/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26987/100000 : ℝ) ^ (4285/1024 : ℝ) ≤ (104127747382726337/25000000000000000000 : ℝ) := by
    have hpowers : (26987/100000 : ℝ)^4285 ≤ (104127747382726337/25000000000000000000 : ℝ)^1024 := by
      have hnat : (26987 : ℕ)^4285*25000000000000000000^1024 ≤ 104127747382726337^1024*100000^4285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26987 100000 104127747382726337 25000000000000000000 4285 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26987/100000 : ℝ)) (X := (104127747382726337/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500000062635601657/2500000000000000000 : ℝ) ≤ (10000000059872911/10000000000000000 : ℝ) ^ (4285/1024 : ℝ) := by
    have hpowers : (2500000062635601657/2500000000000000000 : ℝ)^1024 ≤ (10000000059872911/10000000000000000 : ℝ)^4285 := by
      have hnat : (2500000062635601657 : ℕ)^1024*10000000000000000^4285 ≤ 10000000059872911^4285*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500000062635601657 2500000000000000000 10000000059872911 10000000000000000 1024 4285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000059872911/10000000000000000 : ℝ)) (X := (2500000062635601657/2500000000000000000 : ℝ)) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12552064030280367311/12500000000000000000 : ℝ) ≤ (1000993778802953/1000000000000000 : ℝ) ^ (4285/1024 : ℝ) := by
    have hpowers : (12552064030280367311/12500000000000000000 : ℝ)^1024 ≤ (1000993778802953/1000000000000000 : ℝ)^4285 := by
      have hnat : (12552064030280367311 : ℕ)^1024*1000000000000000^4285 ≤ 1000993778802953^4285*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12552064030280367311 12500000000000000000 1000993778802953 1000000000000000 1024 4285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000993778802953/1000000000000000 : ℝ)) (X := (12552064030280367311/12500000000000000000 : ℝ)) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12604127747382726337/12500000000000000000 : ℝ) ≤ (10019875516186149/10000000000000000 : ℝ) ^ (4285/1024 : ℝ) := by
    have hpowers : (12604127747382726337/12500000000000000000 : ℝ)^1024 ≤ (10019875516186149/10000000000000000 : ℝ)^4285 := by
      have hnat : (12604127747382726337 : ℕ)^1024*10000000000000000^4285 ≤ 10019875516186149^4285*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12604127747382726337 12500000000000000000 10019875516186149 10000000000000000 1024 4285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10019875516186149/10000000000000000 : ℝ)) (X := (12604127747382726337/12500000000000000000 : ℝ)) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(62635601657/5000000000000000000 : ℝ) ≤ ((513828605146723117/513880000000000000 : ℝ)+2*(9937728156619/2569400000000000 : ℝ)*(1293/100000 : ℝ))^(4285/1024 : ℝ) := by
    rw [show (513828605146723117/513880000000000000 : ℝ)+2*(9937728156619/2569400000000000 : ℝ)*(1293/100000 : ℝ)=(10000000059872911/10000000000000000 : ℝ) by norm_num, show 1+2*(62635601657/5000000000000000000 : ℝ)=(2500000062635601657/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(104127747382726337/25000000000000000000 : ℝ)+(62635601657/5000000000000000000 : ℝ) ≤ ((513828605146723117/513880000000000000 : ℝ)+(9937728156619/2569400000000000 : ℝ)*((26987/100000 : ℝ)+(1293/100000 : ℝ)))^(4285/1024 : ℝ) := by
    rw [show (513828605146723117/513880000000000000 : ℝ)+(9937728156619/2569400000000000 : ℝ)*((26987/100000 : ℝ)+(1293/100000 : ℝ))=(1000993778802953/1000000000000000 : ℝ) by norm_num, show 1+(104127747382726337/25000000000000000000 : ℝ)+(62635601657/5000000000000000000 : ℝ)=(12552064030280367311/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(104127747382726337/25000000000000000000 : ℝ) ≤ ((513828605146723117/513880000000000000 : ℝ)+2*(9937728156619/2569400000000000 : ℝ)*(26987/100000 : ℝ))^(4285/1024 : ℝ) := by
    rw [show (513828605146723117/513880000000000000 : ℝ)+2*(9937728156619/2569400000000000 : ℝ)*(26987/100000 : ℝ)=(10019875516186149/10000000000000000 : ℝ) by norm_num, show 1+2*(104127747382726337/25000000000000000000 : ℝ)=(12604127747382726337/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (513828605146723117/513880000000000000 : ℝ)*(X 1 0+X 2 0)+(9937728156619/2569400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4285/1024 : ℝ)) (lo := (1293/100000 : ℝ)) (hi := (26987/100000 : ℝ)) (c := (513828605146723117/513880000000000000 : ℝ)) (alpha := (9937728156619/2569400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (513828605146723117/513880000000000000 : ℝ)*(X 0 1+X 2 1)+(9937728156619/2569400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4285/1024 : ℝ)) (lo := (1293/100000 : ℝ)) (hi := (26987/100000 : ℝ)) (c := (513828605146723117/513880000000000000 : ℝ)) (alpha := (9937728156619/2569400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (513828605146723117/513880000000000000 : ℝ)*(X 0 2+X 1 2)+(9937728156619/2569400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4285/1024 : ℝ)) (lo := (1293/100000 : ℝ)) (hi := (26987/100000 : ℝ)) (c := (513828605146723117/513880000000000000 : ℝ)) (alpha := (9937728156619/2569400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-401153327/2000000000 : ℝ)*X 0 0+(5649397847/10000000000 : ℝ)*X 0 1+(2520857119/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((8651831/16000000 : ℝ)*X 1 0+(-466098009/2000000000 : ℝ)*X 1 1+(1260428577/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5407394611/10000000000 : ℝ)*X 2 0+(315107117/625000000 : ℝ)*X 2 1+(-2330490293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4295148561/10000000000 : ℝ)*X 0 0+(463254103/1250000000 : ℝ)*X 0 1+(1242803063/2500000000 : ℝ)*X 0 2+(4295148561/10000000000 : ℝ)*X 1 0+(463254103/1250000000 : ℝ)*X 1 1+(1242803063/2500000000 : ℝ)*X 1 2+(4295148561/10000000000 : ℝ)*X 2 0+(463254103/1250000000 : ℝ)*X 2 1+(1242803063/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2006333547/10000000000 : ℝ)*X 0 0+(504943323/1000000000 : ℝ)*X 0 1+(5641536641/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1312480591/2500000000 : ℝ)*X 1 0+(-1730667849/10000000000 : ℝ)*X 1 1+(5641536181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2624961037/5000000000 : ℝ)*X 2 0+(1410384003/2500000000 : ℝ)*X 2 1+(-216333563/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2148164027/5000000000 : ℝ)*X 0 0+(495514073/1000000000 : ℝ)*X 0 1+(3722400829/10000000000 : ℝ)*X 0 2+(2148164027/5000000000 : ℝ)*X 1 0+(495514073/1000000000 : ℝ)*X 1 1+(3722400829/10000000000 : ℝ)*X 1 2+(2148164027/5000000000 : ℝ)*X 2 0+(495514073/1000000000 : ℝ)*X 2 1+(3722400829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (216144095789062504523298981/25694000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104449177/100000000000000 : ℝ)*(base1) + (348280253/25000000000000 : ℝ)*(base19) + (4577943/312500000000 : ℝ)*(base23) + (224287893/100000000000000 : ℝ)*(upper3) + (28364367/20000000000000 : ℝ)*(upper5) + (1218008588155869/100000000000000 : ℝ)*(major0) + (1218008588155869/100000000000000 : ℝ)*(major1) + (1218008588155869/100000000000000 : ℝ)*(major2) + (164560084712289/10000000000000 : ℝ)*(sp0) + (411401610080673/25000000000000 : ℝ)*(sp1) + (329121273700389/20000000000000 : ℝ)*(sp2) + (790405059842531/100000000000000 : ℝ)*(sp3) + (886346249/12500000000000 : ℝ)*(sp4) + (1949084159/50000000000000 : ℝ)*(sp7) + (395204531230013/50000000000000 : ℝ)*(f.failure) + (329121566688741/20000000000000 : ℝ)*(f.sum) + (262966784760919/128470000000000000000000000000 : ℝ)*base66 + (432828700472606127/51388000000000000000000000000000 : ℝ)*base68 + (221313383436017873/51388000000000000000000000000000 : ℝ)*base69 + (49359452035461873/51388000000000000000000000000000 : ℝ)*base71 + (1104404721000769/128470000000000000000000000000 : ℝ)*base74 + (438505153723745873/51388000000000000000000000000000 : ℝ)*base75 + (68354466363201873/51388000000000000000000000000000 : ℝ)*base77 + (184286992494006127/51388000000000000000000000000000 : ℝ)*base80 + (276971908166881/128470000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2058063/500000000000000000000 : ℝ)*base89 + (2058063/500000000000000000000 : ℝ)*base91 + (2058063/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1358554922015840055386049/221500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (985205433/100000000000000 : ℝ)*(base19) + (210527343/25000000000000 : ℝ)*(base23) + (567503/4000000000000 : ℝ)*(upper2) + (34674531/50000000000000 : ℝ)*(upper3) + (87503493/50000000000000 : ℝ)*(upper5) + (312511940226071/25000000000000 : ℝ)*(major0) + (312511940226071/25000000000000 : ℝ)*(major1) + (312511940226071/25000000000000 : ℝ)*(major2) + (4707397459/100000000000000 : ℝ)*(sp1) + (1073024137/50000000000000 : ℝ)*(sp2) + (422223724247657/25000000000000 : ℝ)*(sp4) + (211111150548467/12500000000000 : ℝ)*(sp5) + (844445954416491/50000000000000 : ℝ)*(sp6) + (162240084074049/20000000000000 : ℝ)*(sp7) + (162240084074049/20000000000000 : ℝ)*(f.failure) + (422223724247657/25000000000000 : ℝ)*(f.sum) + (47954273613/553750000000000000000000000 : ℝ)*base65 + (515857810691617/443000000000000000000000000000 : ℝ)*base68 + (260196469500617/443000000000000000000000000000 : ℝ)*base70 + (1667898742041383/443000000000000000000000000000 : ℝ)*base71 + (3877863577203/2215000000000000000000000000 : ℝ)*base74 + (519005504220617/443000000000000000000000000000 : ℝ)*base76 + (1306790906437617/443000000000000000000000000000 : ℝ)*base78 + (444550120812383/443000000000000000000000000000 : ℝ)*base79 + (9261413283537/2215000000000000000000000000 : ℝ)*base81 + (56699/200000000000000000000 : ℝ)*base89 + (56699/200000000000000000000 : ℝ)*base91 + (56699/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1326_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15409851/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1293/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6739/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19583/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1326_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1326_s2_0 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2047335907/10000000000 : ℝ)*x 0 + (2742106207/5000000000 : ℝ)*x 1 + (1036059287/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2047335907/10000000000 : ℝ)^2143 ≤ (12443973375131/100000000000000 : ℝ)^1631 := by
    have hnat : (2047335907 : ℕ)^2143*100000000000000^1631 ≤ 12443973375131^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047335907 10000000000 12443973375131 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2742106207/5000000000 : ℝ)^2143 ≤ (11354227455647/25000000000000 : ℝ)^1631 := by
    have hnat : (2742106207 : ℕ)^2143*25000000000000^1631 ≤ 11354227455647^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742106207 5000000000 11354227455647 25000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036059287/2000000000 : ℝ)^2143 ≤ (42139116779269/100000000000000 : ℝ)^1631 := by
    have hnat : (1036059287 : ℕ)^2143*100000000000000^1631 ≤ 42139116779269^1631*2000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036059287 2000000000 42139116779269 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2047335907/10000000000 : ℝ), (2742106207/5000000000 : ℝ), (1036059287/2000000000 : ℝ)] ![(12443973375131/100000000000000 : ℝ), (11354227455647/25000000000000 : ℝ), (42139116779269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2047335907/10000000000 : ℝ)|^2143 ≤ (12443973375131/100000000000000 : ℝ)^1631
        have hw : |(-2047335907/10000000000 : ℝ)|=(2047335907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2742106207/5000000000 : ℝ)|^2143 ≤ (11354227455647/25000000000000 : ℝ)^1631
        have hw : |(2742106207/5000000000 : ℝ)|=(2742106207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036059287/2000000000 : ℝ)|^2143 ≤ (42139116779269/100000000000000 : ℝ)^1631
        have hw : |(1036059287/2000000000 : ℝ)|=(1036059287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s2_1 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1073418307/2000000000 : ℝ)*x 0 + (-440902657/2000000000 : ℝ)*x 1 + (5180295951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073418307/2000000000 : ℝ)^2143 ≤ (11036700609669/25000000000000 : ℝ)^1631 := by
    have hnat : (1073418307 : ℕ)^2143*25000000000000^1631 ≤ 11036700609669^1631*2000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073418307 2000000000 11036700609669 25000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440902657/2000000000 : ℝ)^2143 ≤ (3428521485837/25000000000000 : ℝ)^1631 := by
    have hnat : (440902657 : ℕ)^2143*25000000000000^1631 ≤ 3428521485837^1631*2000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440902657 2000000000 3428521485837 25000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180295951/10000000000 : ℝ)^2143 ≤ (42139111606247/100000000000000 : ℝ)^1631 := by
    have hnat : (5180295951 : ℕ)^2143*100000000000000^1631 ≤ 42139111606247^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180295951 10000000000 42139111606247 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073418307/2000000000 : ℝ), (-440902657/2000000000 : ℝ), (5180295951/10000000000 : ℝ)] ![(11036700609669/25000000000000 : ℝ), (3428521485837/25000000000000 : ℝ), (42139111606247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073418307/2000000000 : ℝ)|^2143 ≤ (11036700609669/25000000000000 : ℝ)^1631
        have hw : |(1073418307/2000000000 : ℝ)|=(1073418307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-440902657/2000000000 : ℝ)|^2143 ≤ (3428521485837/25000000000000 : ℝ)^1631
        have hw : |(-440902657/2000000000 : ℝ)|=(440902657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180295951/10000000000 : ℝ)|^2143 ≤ (42139111606247/100000000000000 : ℝ)^1631
        have hw : |(5180295951/10000000000 : ℝ)|=(5180295951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s2_2 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5367090879/10000000000 : ℝ)*x 0 + (2590148299/5000000000 : ℝ)*x 1 + (-440902661/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367090879/10000000000 : ℝ)^2143 ≤ (5518349418613/12500000000000 : ℝ)^1631 := by
    have hnat : (5367090879 : ℕ)^2143*12500000000000^1631 ≤ 5518349418613^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367090879 10000000000 5518349418613 12500000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590148299/5000000000 : ℝ)^2143 ≤ (2633694907589/6250000000000 : ℝ)^1631 := by
    have hnat : (2590148299 : ℕ)^2143*6250000000000^1631 ≤ 2633694907589^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590148299 5000000000 2633694907589 6250000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440902661/2000000000 : ℝ)^2143 ≤ (13714086106823/100000000000000 : ℝ)^1631 := by
    have hnat : (440902661 : ℕ)^2143*100000000000000^1631 ≤ 13714086106823^1631*2000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440902661 2000000000 13714086106823 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367090879/10000000000 : ℝ), (2590148299/5000000000 : ℝ), (-440902661/2000000000 : ℝ)] ![(5518349418613/12500000000000 : ℝ), (2633694907589/6250000000000 : ℝ), (13714086106823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367090879/10000000000 : ℝ)|^2143 ≤ (5518349418613/12500000000000 : ℝ)^1631
        have hw : |(5367090879/10000000000 : ℝ)|=(5367090879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590148299/5000000000 : ℝ)|^2143 ≤ (2633694907589/6250000000000 : ℝ)^1631
        have hw : |(2590148299/5000000000 : ℝ)|=(2590148299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-440902661/2000000000 : ℝ)|^2143 ≤ (13714086106823/100000000000000 : ℝ)^1631
        have hw : |(-440902661/2000000000 : ℝ)|=(440902661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s2_3 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4324165029/10000000000 : ℝ)*x 0 + (502331203/1250000000 : ℝ)*x 1 + (290712667/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324165029/10000000000 : ℝ)^2143 ≤ (16617874997519/50000000000000 : ℝ)^1631 := by
    have hnat : (4324165029 : ℕ)^2143*50000000000000^1631 ≤ 16617874997519^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324165029 10000000000 16617874997519 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502331203/1250000000 : ℝ)^2143 ≤ (6037036913421/20000000000000 : ℝ)^1631 := by
    have hnat : (502331203 : ℕ)^2143*20000000000000^1631 ≤ 6037036913421^1631*1250000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502331203 1250000000 6037036913421 20000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (290712667/625000000 : ℝ)^2143 ≤ (7315813084329/20000000000000 : ℝ)^1631 := by
    have hnat : (290712667 : ℕ)^2143*20000000000000^1631 ≤ 7315813084329^1631*625000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290712667 625000000 7315813084329 20000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324165029/10000000000 : ℝ), (502331203/1250000000 : ℝ), (290712667/625000000 : ℝ)] ![(16617874997519/50000000000000 : ℝ), (6037036913421/20000000000000 : ℝ), (7315813084329/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324165029/10000000000 : ℝ)|^2143 ≤ (16617874997519/50000000000000 : ℝ)^1631
        have hw : |(4324165029/10000000000 : ℝ)|=(4324165029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(502331203/1250000000 : ℝ)|^2143 ≤ (6037036913421/20000000000000 : ℝ)^1631
        have hw : |(502331203/1250000000 : ℝ)|=(502331203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(290712667/625000000 : ℝ)|^2143 ≤ (7315813084329/20000000000000 : ℝ)^1631
        have hw : |(290712667/625000000 : ℝ)|=(290712667/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s2_4 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-511851607/2500000000 : ℝ)*x 0 + (1295559069/2500000000 : ℝ)*x 1 + (2741127501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (511851607/2500000000 : ℝ)^2143 ≤ (12444536570389/100000000000000 : ℝ)^1631 := by
    have hnat : (511851607 : ℕ)^2143*100000000000000^1631 ≤ 12444536570389^1631*2500000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511851607 2500000000 12444536570389 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295559069/2500000000 : ℝ)^2143 ≤ (8431970228321/20000000000000 : ℝ)^1631 := by
    have hnat : (1295559069 : ℕ)^2143*20000000000000^1631 ≤ 8431970228321^1631*2500000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295559069 2500000000 8431970228321 20000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2741127501/5000000000 : ℝ)^2143 ≤ (22697806141409/50000000000000 : ℝ)^1631 := by
    have hnat : (2741127501 : ℕ)^2143*50000000000000^1631 ≤ 22697806141409^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741127501 5000000000 22697806141409 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-511851607/2500000000 : ℝ), (1295559069/2500000000 : ℝ), (2741127501/5000000000 : ℝ)] ![(12444536570389/100000000000000 : ℝ), (8431970228321/20000000000000 : ℝ), (22697806141409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-511851607/2500000000 : ℝ)|^2143 ≤ (12444536570389/100000000000000 : ℝ)^1631
        have hw : |(-511851607/2500000000 : ℝ)|=(511851607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295559069/2500000000 : ℝ)|^2143 ≤ (8431970228321/20000000000000 : ℝ)^1631
        have hw : |(1295559069/2500000000 : ℝ)|=(1295559069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2741127501/5000000000 : ℝ)|^2143 ≤ (22697806141409/50000000000000 : ℝ)^1631
        have hw : |(2741127501/5000000000 : ℝ)|=(2741127501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s2_5 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5288894441/10000000000 : ℝ)*x 0 + (-951276839/5000000000 : ℝ)*x 1 + (685281881/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288894441/10000000000 : ℝ)^2143 ≤ (866072404617/2000000000000 : ℝ)^1631 := by
    have hnat : (5288894441 : ℕ)^2143*2000000000000^1631 ≤ 866072404617^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288894441 10000000000 866072404617 2000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (951276839/5000000000 : ℝ)^2143 ≤ (11300766968199/100000000000000 : ℝ)^1631 := by
    have hnat : (951276839 : ℕ)^2143*100000000000000^1631 ≤ 11300766968199^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      951276839 5000000000 11300766968199 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685281881/1250000000 : ℝ)^2143 ≤ (45395612783291/100000000000000 : ℝ)^1631 := by
    have hnat : (685281881 : ℕ)^2143*100000000000000^1631 ≤ 45395612783291^1631*1250000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685281881 1250000000 45395612783291 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288894441/10000000000 : ℝ), (-951276839/5000000000 : ℝ), (685281881/1250000000 : ℝ)] ![(866072404617/2000000000000 : ℝ), (11300766968199/100000000000000 : ℝ), (45395612783291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288894441/10000000000 : ℝ)|^2143 ≤ (866072404617/2000000000000 : ℝ)^1631
        have hw : |(5288894441/10000000000 : ℝ)|=(5288894441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-951276839/5000000000 : ℝ)|^2143 ≤ (11300766968199/100000000000000 : ℝ)^1631
        have hw : |(-951276839/5000000000 : ℝ)|=(951276839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(685281881/1250000000 : ℝ)|^2143 ≤ (45395612783291/100000000000000 : ℝ)^1631
        have hw : |(685281881/1250000000 : ℝ)|=(685281881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s2_6 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (528889451/1000000000 : ℝ)*x 0 + (5482255009/10000000000 : ℝ)*x 1 + (-951276819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528889451/1000000000 : ℝ)^2143 ≤ (8660724194629/20000000000000 : ℝ)^1631 := by
    have hnat : (528889451 : ℕ)^2143*20000000000000^1631 ≤ 8660724194629^1631*1000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528889451 1000000000 8660724194629 20000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5482255009/10000000000 : ℝ)^2143 ≤ (45395612358977/100000000000000 : ℝ)^1631 := by
    have hnat : (5482255009 : ℕ)^2143*100000000000000^1631 ≤ 45395612358977^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482255009 10000000000 45395612358977 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (951276819/5000000000 : ℝ)^2143 ≤ (11300766656023/100000000000000 : ℝ)^1631 := by
    have hnat : (951276819 : ℕ)^2143*100000000000000^1631 ≤ 11300766656023^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      951276819 5000000000 11300766656023 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528889451/1000000000 : ℝ), (5482255009/10000000000 : ℝ), (-951276819/5000000000 : ℝ)] ![(8660724194629/20000000000000 : ℝ), (45395612358977/100000000000000 : ℝ), (11300766656023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528889451/1000000000 : ℝ)|^2143 ≤ (8660724194629/20000000000000 : ℝ)^1631
        have hw : |(528889451/1000000000 : ℝ)|=(528889451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5482255009/10000000000 : ℝ)|^2143 ≤ (45395612358977/100000000000000 : ℝ)^1631
        have hw : |(5482255009/10000000000 : ℝ)|=(5482255009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-951276819/5000000000 : ℝ)|^2143 ≤ (11300766656023/100000000000000 : ℝ)^1631
        have hw : |(-951276819/5000000000 : ℝ)|=(951276819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s2_7 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (864862019/2000000000 : ℝ)*x 0 + (4647361587/10000000000 : ℝ)*x 1 + (4022730857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864862019/2000000000 : ℝ)^2143 ≤ (33237215000879/100000000000000 : ℝ)^1631 := by
    have hnat : (864862019 : ℕ)^2143*100000000000000^1631 ≤ 33237215000879^1631*2000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864862019 2000000000 33237215000879 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4647361587/10000000000 : ℝ)^2143 ≤ (4567164437981/12500000000000 : ℝ)^1631 := by
    have hnat : (4647361587 : ℕ)^2143*12500000000000^1631 ≤ 4567164437981^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4647361587 10000000000 4567164437981 12500000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4022730857/10000000000 : ℝ)^2143 ≤ (3778183685811/12500000000000 : ℝ)^1631 := by
    have hnat : (4022730857 : ℕ)^2143*12500000000000^1631 ≤ 3778183685811^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022730857 10000000000 3778183685811 12500000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864862019/2000000000 : ℝ), (4647361587/10000000000 : ℝ), (4022730857/10000000000 : ℝ)] ![(33237215000879/100000000000000 : ℝ), (4567164437981/12500000000000 : ℝ), (3778183685811/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864862019/2000000000 : ℝ)|^2143 ≤ (33237215000879/100000000000000 : ℝ)^1631
        have hw : |(864862019/2000000000 : ℝ)|=(864862019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4647361587/10000000000 : ℝ)|^2143 ≤ (4567164437981/12500000000000 : ℝ)^1631
        have hw : |(4647361587/10000000000 : ℝ)|=(4647361587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4022730857/10000000000 : ℝ)|^2143 ≤ (3778183685811/12500000000000 : ℝ)^1631
        have hw : |(4022730857/10000000000 : ℝ)|=(4022730857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1326_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15409851/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19583/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6739/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1949/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16169/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19583/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6739/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19583/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6739/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19583/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6739/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19583/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6739/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19583/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6739/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19583/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6739/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6739/100000 : ℝ) ^ (4285/1024 : ℝ) ≤ (1253647164744003/100000000000000000000 : ℝ) := by
    have hpowers : (6739/100000 : ℝ)^4285 ≤ (1253647164744003/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6739 : ℕ)^4285*100000000000000000000^1024 ≤ 1253647164744003^1024*100000^4285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6739 100000 1253647164744003 100000000000000000000 4285 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6739/100000 : ℝ)) (X := (1253647164744003/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19583/100000 : ℝ) ^ (4285/1024 : ℝ) ≤ (54423795624262273/50000000000000000000 : ℝ) := by
    have hpowers : (19583/100000 : ℝ)^4285 ≤ (54423795624262273/50000000000000000000 : ℝ)^1024 := by
      have hnat : (19583 : ℕ)^4285*50000000000000000000^1024 ≤ 54423795624262273^1024*100000^4285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19583 100000 54423795624262273 50000000000000000000 4285 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19583/100000 : ℝ)) (X := (54423795624262273/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001253647164744003/50000000000000000000 : ℝ) ≤ (5000029958516903/5000000000000000 : ℝ) ^ (4285/1024 : ℝ) := by
    have hpowers : (50001253647164744003/50000000000000000000 : ℝ)^1024 ≤ (5000029958516903/5000000000000000 : ℝ)^4285 := by
      have hnat : (50001253647164744003 : ℕ)^1024*5000000000000000^4285 ≤ 5000029958516903^4285*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001253647164744003 50000000000000000000 5000029958516903 5000000000000000 1024 4285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000029958516903/5000000000000000 : ℝ)) (X := (50001253647164744003/50000000000000000000 : ℝ)) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100110101238413268549/100000000000000000000 : ℝ) ≤ (5001315011256491/5000000000000000 : ℝ) ^ (4285/1024 : ℝ) := by
    have hpowers : (100110101238413268549/100000000000000000000 : ℝ)^1024 ≤ (5001315011256491/5000000000000000 : ℝ)^4285 := by
      have hnat : (100110101238413268549 : ℕ)^1024*5000000000000000^4285 ≤ 5001315011256491^4285*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100110101238413268549 100000000000000000000 5001315011256491 5000000000000000 1024 4285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001315011256491/5000000000000000 : ℝ)) (X := (100110101238413268549/100000000000000000000 : ℝ)) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25054423795624262273/25000000000000000000 : ℝ) ≤ (5002600063996079/5000000000000000 : ℝ) ^ (4285/1024 : ℝ) := by
    have hpowers : (25054423795624262273/25000000000000000000 : ℝ)^1024 ≤ (5002600063996079/5000000000000000 : ℝ)^4285 := by
      have hnat : (25054423795624262273 : ℕ)^1024*5000000000000000^4285 ≤ 5002600063996079^4285*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25054423795624262273 25000000000000000000 5002600063996079 5000000000000000 1024 4285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002600063996079/5000000000000000 : ℝ)) (X := (25054423795624262273/25000000000000000000 : ℝ)) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1253647164744003/100000000000000000000 : ℝ) ≤ ((16050766211591733767/16055000000000000000 : ℝ)+2*(321263184897/160550000000000 : ℝ)*(6739/100000 : ℝ))^(4285/1024 : ℝ) := by
    rw [show (16050766211591733767/16055000000000000000 : ℝ)+2*(321263184897/160550000000000 : ℝ)*(6739/100000 : ℝ)=(5000029958516903/5000000000000000 : ℝ) by norm_num, show 1+2*(1253647164744003/100000000000000000000 : ℝ)=(50001253647164744003/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(54423795624262273/50000000000000000000 : ℝ)+(1253647164744003/100000000000000000000 : ℝ) ≤ ((16050766211591733767/16055000000000000000 : ℝ)+(321263184897/160550000000000 : ℝ)*((19583/100000 : ℝ)+(6739/100000 : ℝ)))^(4285/1024 : ℝ) := by
    rw [show (16050766211591733767/16055000000000000000 : ℝ)+(321263184897/160550000000000 : ℝ)*((19583/100000 : ℝ)+(6739/100000 : ℝ))=(5001315011256491/5000000000000000 : ℝ) by norm_num, show 1+(54423795624262273/50000000000000000000 : ℝ)+(1253647164744003/100000000000000000000 : ℝ)=(100110101238413268549/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(54423795624262273/50000000000000000000 : ℝ) ≤ ((16050766211591733767/16055000000000000000 : ℝ)+2*(321263184897/160550000000000 : ℝ)*(19583/100000 : ℝ))^(4285/1024 : ℝ) := by
    rw [show (16050766211591733767/16055000000000000000 : ℝ)+2*(321263184897/160550000000000 : ℝ)*(19583/100000 : ℝ)=(5002600063996079/5000000000000000 : ℝ) by norm_num, show 1+2*(54423795624262273/50000000000000000000 : ℝ)=(25054423795624262273/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16050766211591733767/16055000000000000000 : ℝ)*(X 1 0+X 2 0)+(321263184897/160550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4285/1024 : ℝ)) (lo := (6739/100000 : ℝ)) (hi := (19583/100000 : ℝ)) (c := (16050766211591733767/16055000000000000000 : ℝ)) (alpha := (321263184897/160550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16050766211591733767/16055000000000000000 : ℝ)*(X 0 1+X 2 1)+(321263184897/160550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4285/1024 : ℝ)) (lo := (6739/100000 : ℝ)) (hi := (19583/100000 : ℝ)) (c := (16050766211591733767/16055000000000000000 : ℝ)) (alpha := (321263184897/160550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16050766211591733767/16055000000000000000 : ℝ)*(X 0 2+X 1 2)+(321263184897/160550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4285/1024 : ℝ)) (lo := (6739/100000 : ℝ)) (hi := (19583/100000 : ℝ)) (c := (16050766211591733767/16055000000000000000 : ℝ)) (alpha := (321263184897/160550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2047335907/10000000000 : ℝ)*X 0 0+(2742106207/5000000000 : ℝ)*X 0 1+(1036059287/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1073418307/2000000000 : ℝ)*X 1 0+(-440902657/2000000000 : ℝ)*X 1 1+(5180295951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5367090879/10000000000 : ℝ)*X 2 0+(2590148299/5000000000 : ℝ)*X 2 1+(-440902661/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4324165029/10000000000 : ℝ)*X 0 0+(502331203/1250000000 : ℝ)*X 0 1+(290712667/625000000 : ℝ)*X 0 2+(4324165029/10000000000 : ℝ)*X 1 0+(502331203/1250000000 : ℝ)*X 1 1+(290712667/625000000 : ℝ)*X 1 2+(4324165029/10000000000 : ℝ)*X 2 0+(502331203/1250000000 : ℝ)*X 2 1+(290712667/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-511851607/2500000000 : ℝ)*X 0 0+(1295559069/2500000000 : ℝ)*X 0 1+(2741127501/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288894441/10000000000 : ℝ)*X 1 0+(-951276839/5000000000 : ℝ)*X 1 1+(685281881/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((528889451/1000000000 : ℝ)*X 2 0+(5482255009/10000000000 : ℝ)*X 2 1+(-951276819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((864862019/2000000000 : ℝ)*X 0 0+(4647361587/10000000000 : ℝ)*X 0 1+(4022730857/10000000000 : ℝ)*X 0 2+(864862019/2000000000 : ℝ)*X 1 0+(4647361587/10000000000 : ℝ)*X 1 1+(4022730857/10000000000 : ℝ)*X 1 2+(864862019/2000000000 : ℝ)*X 2 0+(4647361587/10000000000 : ℝ)*X 2 1+(4022730857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (330465259931487330004726653/100343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (810568501/50000000000000 : ℝ)*(base19) + (802502837/100000000000000 : ℝ)*(base23) + (277336953/100000000000000 : ℝ)*(lower2) + (38880319/6250000000000 : ℝ)*(upper3) + (2690907/5000000000000 : ℝ)*(lower4) + (182307453/100000000000000 : ℝ)*(upper5) + (304425861924251/12500000000000 : ℝ)*(major0) + (304425861924251/12500000000000 : ℝ)*(major1) + (304425861924251/12500000000000 : ℝ)*(major2) + (41129894863349/1250000000000 : ℝ)*(sp0) + (1645194983965459/50000000000000 : ℝ)*(sp1) + (3290390786565083/100000000000000 : ℝ)*(sp2) + (158040664472393/10000000000000 : ℝ)*(sp3) + (60340697/390625000000 : ℝ)*(sp7) + (1580422091942361/100000000000000 : ℝ)*(f.failure) + (41129894863349/1250000000000 : ℝ)*(f.sum) + (3155006269001/8027500000000000000000000000 : ℝ)*base65 + (1267727279461416483/200687500000000000000000000000000 : ℝ)*base68 + (2761791451061416483/200687500000000000000000000000000 : ℝ)*base70 + (329625874093666483/200687500000000000000000000000000 : ℝ)*base72 + (58696212572359/8027500000000000000000000000 : ℝ)*base74 + (3446988310036291483/200687500000000000000000000000000 : ℝ)*base76 + (2586677676187228983/200687500000000000000000000000000 : ℝ)*base78 + (3278079943779791483/200687500000000000000000000000000 : ℝ)*base80 + (55544384342443/16055000000000000000000000000 : ℝ)*base82 + (3598211/1000000000000000000000 : ℝ)*base89 + (3598211/1000000000000000000000 : ℝ)*base91 + (3598211/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63635214733924523153982681/10562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (611086911/50000000000000 : ℝ)*(base19) + (1456344077/100000000000000 : ℝ)*(base23) + (6767047/4000000000000 : ℝ)*(upper3) + (72352349/100000000000000 : ℝ)*(lower4) + (38386703/50000000000000 : ℝ)*(upper5) + (1233517377514761/50000000000000 : ℝ)*(major0) + (1233517377514761/50000000000000 : ℝ)*(major1) + (1233517377514761/50000000000000 : ℝ)*(major2) + (13190632599/100000000000000 : ℝ)*(sp1) + (16835334637/100000000000000 : ℝ)*(sp2) + (3333122775082829/100000000000000 : ℝ)*(sp4) + (416638545284551/12500000000000 : ℝ)*(sp5) + (666620896680823/20000000000000 : ℝ)*(sp6) + (200118316769377/12500000000000 : ℝ)*(sp7) + (200118316769377/12500000000000 : ℝ)*(f.failure) + (3333122775082829/100000000000000 : ℝ)*(f.sum) + (31040313607/52812500000000000000000000 : ℝ)*base65 + (52035777868280773/42250000000000000000000000000000 : ℝ)*base67 + (142974079016780773/42250000000000000000000000000000 : ℝ)*base69 + (346074284575030773/42250000000000000000000000000000 : ℝ)*base71 + (63169463813/845000000000000000000000000 : ℝ)*base74 + (26366184526969227/42250000000000000000000000000000 : ℝ)*base76 + (205559776220030773/42250000000000000000000000000000 : ℝ)*base77 + (148191616735030773/42250000000000000000000000000000 : ℝ)*base79 + (24383122193/845000000000000000000000000 : ℝ)*base82 + (1567173/125000000000000000000 : ℝ)*base90 + (1567173/125000000000000000000 : ℝ)*base92 + (1567173/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1326_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15409851/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19583/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6739/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1949/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1326_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1326_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15409851/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1949/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1326_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1326_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1326_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15409851/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1949/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1326_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1312_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:40:28.533629+00:00
-- url     : https://prove2.me/submissions/ca77ce87-5792-4190-8239-4a737043c2d3

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
theorem support_rectangle_w1312_s6_0 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1035084743/5000000000 : ℝ)*x 0 + (2707140471/5000000000 : ℝ)*x 1 + (2621807803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035084743/5000000000 : ℝ)^267 ≤ (6299882479053/50000000000000 : ℝ)^203 := by
    have hnat : (1035084743 : ℕ)^267*50000000000000^203 ≤ 6299882479053^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035084743 5000000000 6299882479053 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707140471/5000000000 : ℝ)^267 ≤ (4462044957571/10000000000000 : ℝ)^203 := by
    have hnat : (2707140471 : ℕ)^267*10000000000000^203 ≤ 4462044957571^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707140471 5000000000 4462044957571 10000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621807803/5000000000 : ℝ)^267 ≤ (21389892725167/50000000000000 : ℝ)^203 := by
    have hnat : (2621807803 : ℕ)^267*50000000000000^203 ≤ 21389892725167^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621807803 5000000000 21389892725167 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1035084743/5000000000 : ℝ), (2707140471/5000000000 : ℝ), (2621807803/5000000000 : ℝ)] ![(6299882479053/50000000000000 : ℝ), (4462044957571/10000000000000 : ℝ), (21389892725167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1035084743/5000000000 : ℝ)|^267 ≤ (6299882479053/50000000000000 : ℝ)^203
        have hw : |(-1035084743/5000000000 : ℝ)|=(1035084743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707140471/5000000000 : ℝ)|^267 ≤ (4462044957571/10000000000000 : ℝ)^203
        have hw : |(2707140471/5000000000 : ℝ)|=(2707140471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621807803/5000000000 : ℝ)|^267 ≤ (21389892725167/50000000000000 : ℝ)^203
        have hw : |(2621807803/5000000000 : ℝ)|=(2621807803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s6_1 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1337375077/2500000000 : ℝ)*x 0 + (-539287487/2500000000 : ℝ)*x 1 + (5243615297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337375077/2500000000 : ℝ)^267 ≤ (10979897328947/25000000000000 : ℝ)^203 := by
    have hnat : (1337375077 : ℕ)^267*25000000000000^203 ≤ 10979897328947^203*2500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337375077 2500000000 10979897328947 25000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539287487/2500000000 : ℝ)^267 ≤ (6650314268919/50000000000000 : ℝ)^203 := by
    have hnat : (539287487 : ℕ)^267*50000000000000^203 ≤ 6650314268919^203*2500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539287487 2500000000 6650314268919 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243615297/10000000000 : ℝ)^267 ≤ (21389891067293/50000000000000 : ℝ)^203 := by
    have hnat : (5243615297 : ℕ)^267*50000000000000^203 ≤ 21389891067293^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243615297 10000000000 21389891067293 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337375077/2500000000 : ℝ), (-539287487/2500000000 : ℝ), (5243615297/10000000000 : ℝ)] ![(10979897328947/25000000000000 : ℝ), (6650314268919/50000000000000 : ℝ), (21389891067293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337375077/2500000000 : ℝ)|^267 ≤ (10979897328947/25000000000000 : ℝ)^203
        have hw : |(1337375077/2500000000 : ℝ)|=(1337375077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-539287487/2500000000 : ℝ)|^267 ≤ (6650314268919/50000000000000 : ℝ)^203
        have hw : |(-539287487/2500000000 : ℝ)|=(539287487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243615297/10000000000 : ℝ)|^267 ≤ (21389891067293/50000000000000 : ℝ)^203
        have hw : |(5243615297/10000000000 : ℝ)|=(5243615297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s6_2 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (213979987/400000000 : ℝ)*x 0 + (5243615541/10000000000 : ℝ)*x 1 + (-539287617/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213979987/400000000 : ℝ)^267 ≤ (43919582480387/100000000000000 : ℝ)^203 := by
    have hnat : (213979987 : ℕ)^267*100000000000000^203 ≤ 43919582480387^203*400000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213979987 400000000 43919582480387 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243615541/10000000000 : ℝ)^267 ≤ (21389892376423/50000000000000 : ℝ)^203 := by
    have hnat : (5243615541 : ℕ)^267*50000000000000^203 ≤ 21389892376423^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243615541 10000000000 21389892376423 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539287617/2500000000 : ℝ)^267 ≤ (1662579094363/12500000000000 : ℝ)^203 := by
    have hnat : (539287617 : ℕ)^267*12500000000000^203 ≤ 1662579094363^203*2500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539287617 2500000000 1662579094363 12500000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213979987/400000000 : ℝ), (5243615541/10000000000 : ℝ), (-539287617/2500000000 : ℝ)] ![(43919582480387/100000000000000 : ℝ), (21389892376423/50000000000000 : ℝ), (1662579094363/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213979987/400000000 : ℝ)|^267 ≤ (43919582480387/100000000000000 : ℝ)^203
        have hw : |(213979987/400000000 : ℝ)|=(213979987/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243615541/10000000000 : ℝ)|^267 ≤ (21389892376423/50000000000000 : ℝ)^203
        have hw : |(5243615541/10000000000 : ℝ)|=(5243615541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-539287617/2500000000 : ℝ)|^267 ≤ (1662579094363/12500000000000 : ℝ)^203
        have hw : |(-539287617/2500000000 : ℝ)|=(539287617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s6_3 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (866904349/2000000000 : ℝ)*x 0 + (2080607213/5000000000 : ℝ)*x 1 + (2257327577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866904349/2000000000 : ℝ)^267 ≤ (2081418025261/6250000000000 : ℝ)^203 := by
    have hnat : (866904349 : ℕ)^267*6250000000000^203 ≤ 2081418025261^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866904349 2000000000 2081418025261 6250000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080607213/5000000000 : ℝ)^267 ≤ (31562490046799/100000000000000 : ℝ)^203 := by
    have hnat : (2080607213 : ℕ)^267*100000000000000^203 ≤ 31562490046799^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080607213 5000000000 31562490046799 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257327577/5000000000 : ℝ)^267 ≤ (8783705383519/25000000000000 : ℝ)^203 := by
    have hnat : (2257327577 : ℕ)^267*25000000000000^203 ≤ 8783705383519^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257327577 5000000000 8783705383519 25000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(866904349/2000000000 : ℝ), (2080607213/5000000000 : ℝ), (2257327577/5000000000 : ℝ)] ![(2081418025261/6250000000000 : ℝ), (31562490046799/100000000000000 : ℝ), (8783705383519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(866904349/2000000000 : ℝ)|^267 ≤ (2081418025261/6250000000000 : ℝ)^203
        have hw : |(866904349/2000000000 : ℝ)|=(866904349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2080607213/5000000000 : ℝ)|^267 ≤ (31562490046799/100000000000000 : ℝ)^203
        have hw : |(2080607213/5000000000 : ℝ)|=(2080607213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2257327577/5000000000 : ℝ)|^267 ≤ (8783705383519/25000000000000 : ℝ)^203
        have hw : |(2257327577/5000000000 : ℝ)|=(2257327577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s6_4 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1035091181/5000000000 : ℝ)*x 0 + (1048845031/2000000000 : ℝ)*x 1 + (2706833993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035091181/5000000000 : ℝ)^267 ≤ (6299934016531/50000000000000 : ℝ)^203 := by
    have hnat : (1035091181 : ℕ)^267*50000000000000^203 ≤ 6299934016531^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035091181 5000000000 6299934016531 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048845031/2000000000 : ℝ)^267 ≤ (21393163190603/50000000000000 : ℝ)^203 := by
    have hnat : (1048845031 : ℕ)^267*50000000000000^203 ≤ 21393163190603^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048845031 2000000000 21393163190603 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706833993/5000000000 : ℝ)^267 ≤ (22306902785529/50000000000000 : ℝ)^203 := by
    have hnat : (2706833993 : ℕ)^267*50000000000000^203 ≤ 22306902785529^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706833993 5000000000 22306902785529 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1035091181/5000000000 : ℝ), (1048845031/2000000000 : ℝ), (2706833993/5000000000 : ℝ)] ![(6299934016531/50000000000000 : ℝ), (21393163190603/50000000000000 : ℝ), (22306902785529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1035091181/5000000000 : ℝ)|^267 ≤ (6299934016531/50000000000000 : ℝ)^203
        have hw : |(-1035091181/5000000000 : ℝ)|=(1035091181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048845031/2000000000 : ℝ)|^267 ≤ (21393163190603/50000000000000 : ℝ)^203
        have hw : |(1048845031/2000000000 : ℝ)|=(1048845031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706833993/5000000000 : ℝ)|^267 ≤ (22306902785529/50000000000000 : ℝ)^203
        have hw : |(2706833993/5000000000 : ℝ)|=(2706833993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s6_5 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5305696399/10000000000 : ℝ)*x 0 + (-397419551/2000000000 : ℝ)*x 1 + (5413668073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305696399/10000000000 : ℝ)^267 ≤ (43447187944157/100000000000000 : ℝ)^203 := by
    have hnat : (5305696399 : ℕ)^267*100000000000000^203 ≤ 43447187944157^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305696399 10000000000 43447187944157 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397419551/2000000000 : ℝ)^267 ≤ (1193900552963/10000000000000 : ℝ)^203 := by
    have hnat : (397419551 : ℕ)^267*10000000000000^203 ≤ 1193900552963^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397419551 2000000000 1193900552963 10000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413668073/10000000000 : ℝ)^267 ≤ (44613806514059/100000000000000 : ℝ)^203 := by
    have hnat : (5413668073 : ℕ)^267*100000000000000^203 ≤ 44613806514059^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413668073 10000000000 44613806514059 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305696399/10000000000 : ℝ), (-397419551/2000000000 : ℝ), (5413668073/10000000000 : ℝ)] ![(43447187944157/100000000000000 : ℝ), (1193900552963/10000000000000 : ℝ), (44613806514059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305696399/10000000000 : ℝ)|^267 ≤ (43447187944157/100000000000000 : ℝ)^203
        have hw : |(5305696399/10000000000 : ℝ)|=(5305696399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-397419551/2000000000 : ℝ)|^267 ≤ (1193900552963/10000000000000 : ℝ)^203
        have hw : |(-397419551/2000000000 : ℝ)|=(397419551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413668073/10000000000 : ℝ)|^267 ≤ (44613806514059/100000000000000 : ℝ)^203
        have hw : |(5413668073/10000000000 : ℝ)|=(5413668073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s6_6 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5305696473/10000000000 : ℝ)*x 0 + (5413667953/10000000000 : ℝ)*x 1 + (-1987097819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305696473/10000000000 : ℝ)^267 ≤ (43447188741171/100000000000000 : ℝ)^203 := by
    have hnat : (5305696473 : ℕ)^267*100000000000000^203 ≤ 43447188741171^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305696473 10000000000 43447188741171 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413667953/10000000000 : ℝ)^267 ≤ (5576725651671/12500000000000 : ℝ)^203 := by
    have hnat : (5413667953 : ℕ)^267*12500000000000^203 ≤ 5576725651671^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413667953 10000000000 5576725651671 12500000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1987097819/10000000000 : ℝ)^267 ≤ (11939006035389/100000000000000 : ℝ)^203 := by
    have hnat : (1987097819 : ℕ)^267*100000000000000^203 ≤ 11939006035389^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987097819 10000000000 11939006035389 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305696473/10000000000 : ℝ), (5413667953/10000000000 : ℝ), (-1987097819/10000000000 : ℝ)] ![(43447188741171/100000000000000 : ℝ), (5576725651671/12500000000000 : ℝ), (11939006035389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305696473/10000000000 : ℝ)|^267 ≤ (43447188741171/100000000000000 : ℝ)^203
        have hw : |(5305696473/10000000000 : ℝ)|=(5305696473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413667953/10000000000 : ℝ)|^267 ≤ (5576725651671/12500000000000 : ℝ)^203
        have hw : |(5413667953/10000000000 : ℝ)|=(5413667953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1987097819/10000000000 : ℝ)|^267 ≤ (11939006035389/100000000000000 : ℝ)^203
        have hw : |(-1987097819/10000000000 : ℝ)|=(1987097819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s6_7 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4334548119/10000000000 : ℝ)*x 0 + (902678393/2000000000 : ℝ)*x 1 + (4162483667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334548119/10000000000 : ℝ)^267 ≤ (16651477462071/50000000000000 : ℝ)^203 := by
    have hnat : (4334548119 : ℕ)^267*50000000000000^203 ≤ 16651477462071^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334548119 10000000000 16651477462071 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (902678393/2000000000 : ℝ)^267 ≤ (35121892157911/100000000000000 : ℝ)^203 := by
    have hnat : (902678393 : ℕ)^267*100000000000000^203 ≤ 35121892157911^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902678393 2000000000 35121892157911 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4162483667/10000000000 : ℝ)^267 ≤ (1263006115751/4000000000000 : ℝ)^203 := by
    have hnat : (4162483667 : ℕ)^267*4000000000000^203 ≤ 1263006115751^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162483667 10000000000 1263006115751 4000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334548119/10000000000 : ℝ), (902678393/2000000000 : ℝ), (4162483667/10000000000 : ℝ)] ![(16651477462071/50000000000000 : ℝ), (35121892157911/100000000000000 : ℝ), (1263006115751/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334548119/10000000000 : ℝ)|^267 ≤ (16651477462071/50000000000000 : ℝ)^203
        have hw : |(4334548119/10000000000 : ℝ)|=(4334548119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(902678393/2000000000 : ℝ)|^267 ≤ (35121892157911/100000000000000 : ℝ)^203
        have hw : |(902678393/2000000000 : ℝ)|=(902678393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4162483667/10000000000 : ℝ)|^267 ≤ (1263006115751/4000000000000 : ℝ)^203
        have hw : |(4162483667/10000000000 : ℝ)|=(4162483667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1312_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153547737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7349/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5533/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2769/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (459/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7349/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5533/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7349/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5533/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7349/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5533/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7349/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5533/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7349/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5533/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7349/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5533/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5533/50000 : ℝ) ^ (4271/1024 : ℝ) ≤ (411758102036433/4000000000000000000 : ℝ) := by
    have hpowers : (5533/50000 : ℝ)^4271 ≤ (411758102036433/4000000000000000000 : ℝ)^1024 := by
      have hnat : (5533 : ℕ)^4271*4000000000000000000^1024 ≤ 411758102036433^1024*50000^4271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5533 50000 411758102036433 4000000000000000000 4271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5533/50000 : ℝ)) (X := (411758102036433/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7349/50000 : ℝ) ^ (4271/1024 : ℝ) ≤ (33629368109723703/100000000000000000000 : ℝ) := by
    have hpowers : (7349/50000 : ℝ)^4271 ≤ (33629368109723703/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7349 : ℕ)^4271*100000000000000000000^1024 ≤ 33629368109723703^1024*50000^4271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7349 50000 33629368109723703 100000000000000000000 4271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7349/50000 : ℝ)) (X := (33629368109723703/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000411758102036433/2000000000000000000 : ℝ) ≤ (400019742791069/400000000000000 : ℝ) ^ (4271/1024 : ℝ) := by
    have hpowers : (2000411758102036433/2000000000000000000 : ℝ)^1024 ≤ (400019742791069/400000000000000 : ℝ)^4271 := by
      have hnat : (2000411758102036433 : ℕ)^1024*400000000000000^4271 ≤ 400019742791069^4271*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000411758102036433 2000000000000000000 400019742791069 400000000000000 1024 4271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400019742791069/400000000000000 : ℝ)) (X := (2000411758102036433/2000000000000000000 : ℝ)) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126372603770644829/3125000000000000000 : ℝ) ≤ (2500263228592583/2500000000000000 : ℝ) ^ (4271/1024 : ℝ) := by
    have hpowers : (3126372603770644829/3125000000000000000 : ℝ)^1024 ≤ (2500263228592583/2500000000000000 : ℝ)^4271 := by
      have hnat : (3126372603770644829 : ℕ)^1024*2500000000000000^4271 ≤ 2500263228592583^4271*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126372603770644829 3125000000000000000 2500263228592583 2500000000000000 1024 4271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500263228592583/2500000000000000 : ℝ)) (X := (3126372603770644829/3125000000000000000 : ℝ)) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033629368109723703/50000000000000000000 : ℝ) ≤ (10001612258963939/10000000000000000 : ℝ) ^ (4271/1024 : ℝ) := by
    have hpowers : (50033629368109723703/50000000000000000000 : ℝ)^1024 ≤ (10001612258963939/10000000000000000 : ℝ)^4271 := by
      have hnat : (50033629368109723703 : ℕ)^1024*10000000000000000^4271 ≤ 10001612258963939^4271*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033629368109723703 50000000000000000000 10001612258963939 10000000000000000 1024 4271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001612258963939/10000000000000000 : ℝ)) (X := (50033629368109723703/50000000000000000000 : ℝ)) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(411758102036433/4000000000000000000 : ℝ) ≤ ((9077353307720838769/9080000000000000000 : ℝ)+2*(559344593607/363200000000000 : ℝ)*(5533/50000 : ℝ))^(4271/1024 : ℝ) := by
    rw [show (9077353307720838769/9080000000000000000 : ℝ)+2*(559344593607/363200000000000 : ℝ)*(5533/50000 : ℝ)=(400019742791069/400000000000000 : ℝ) by norm_num, show 1+2*(411758102036433/4000000000000000000 : ℝ)=(2000411758102036433/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33629368109723703/100000000000000000000 : ℝ)+(411758102036433/4000000000000000000 : ℝ) ≤ ((9077353307720838769/9080000000000000000 : ℝ)+(559344593607/363200000000000 : ℝ)*((7349/50000 : ℝ)+(5533/50000 : ℝ)))^(4271/1024 : ℝ) := by
    rw [show (9077353307720838769/9080000000000000000 : ℝ)+(559344593607/363200000000000 : ℝ)*((7349/50000 : ℝ)+(5533/50000 : ℝ))=(2500263228592583/2500000000000000 : ℝ) by norm_num, show 1+(33629368109723703/100000000000000000000 : ℝ)+(411758102036433/4000000000000000000 : ℝ)=(3126372603770644829/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33629368109723703/100000000000000000000 : ℝ) ≤ ((9077353307720838769/9080000000000000000 : ℝ)+2*(559344593607/363200000000000 : ℝ)*(7349/50000 : ℝ))^(4271/1024 : ℝ) := by
    rw [show (9077353307720838769/9080000000000000000 : ℝ)+2*(559344593607/363200000000000 : ℝ)*(7349/50000 : ℝ)=(10001612258963939/10000000000000000 : ℝ) by norm_num, show 1+2*(33629368109723703/100000000000000000000 : ℝ)=(50033629368109723703/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9077353307720838769/9080000000000000000 : ℝ)*(X 1 0+X 2 0)+(559344593607/363200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4271/1024 : ℝ)) (lo := (5533/50000 : ℝ)) (hi := (7349/50000 : ℝ)) (c := (9077353307720838769/9080000000000000000 : ℝ)) (alpha := (559344593607/363200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9077353307720838769/9080000000000000000 : ℝ)*(X 0 1+X 2 1)+(559344593607/363200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4271/1024 : ℝ)) (lo := (5533/50000 : ℝ)) (hi := (7349/50000 : ℝ)) (c := (9077353307720838769/9080000000000000000 : ℝ)) (alpha := (559344593607/363200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9077353307720838769/9080000000000000000 : ℝ)*(X 0 2+X 1 2)+(559344593607/363200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4271/1024 : ℝ)) (lo := (5533/50000 : ℝ)) (hi := (7349/50000 : ℝ)) (c := (9077353307720838769/9080000000000000000 : ℝ)) (alpha := (559344593607/363200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1035084743/5000000000 : ℝ)*X 0 0+(2707140471/5000000000 : ℝ)*X 0 1+(2621807803/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337375077/2500000000 : ℝ)*X 1 0+(-539287487/2500000000 : ℝ)*X 1 1+(5243615297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213979987/400000000 : ℝ)*X 2 0+(5243615541/10000000000 : ℝ)*X 2 1+(-539287617/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((866904349/2000000000 : ℝ)*X 0 0+(2080607213/5000000000 : ℝ)*X 0 1+(2257327577/5000000000 : ℝ)*X 0 2+(866904349/2000000000 : ℝ)*X 1 0+(2080607213/5000000000 : ℝ)*X 1 1+(2257327577/5000000000 : ℝ)*X 1 2+(866904349/2000000000 : ℝ)*X 2 0+(2080607213/5000000000 : ℝ)*X 2 1+(2257327577/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1035091181/5000000000 : ℝ)*X 0 0+(1048845031/2000000000 : ℝ)*X 0 1+(2706833993/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305696399/10000000000 : ℝ)*X 1 0+(-397419551/2000000000 : ℝ)*X 1 1+(5413668073/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305696473/10000000000 : ℝ)*X 2 0+(5413667953/10000000000 : ℝ)*X 2 1+(-1987097819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4334548119/10000000000 : ℝ)*X 0 0+(902678393/2000000000 : ℝ)*X 0 1+(4162483667/10000000000 : ℝ)*X 0 2+(4334548119/10000000000 : ℝ)*X 1 0+(902678393/2000000000 : ℝ)*X 1 1+(4162483667/10000000000 : ℝ)*X 1 2+(4334548119/10000000000 : ℝ)*X 2 0+(902678393/2000000000 : ℝ)*X 2 1+(4162483667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23542551329324240044569/3632000000000000000000000000 : ℝ) := by norm_num
    linear_combination (281363617/25000000000000 : ℝ)*(base19) + (559159641/100000000000000 : ℝ)*(base23) + (137917147/100000000000000 : ℝ)*(lower4) + (28513981/100000000000000 : ℝ)*(lower5) + (868883070594169/20000000000000 : ℝ)*(major0) + (868883070594169/20000000000000 : ℝ)*(major1) + (868883070594169/20000000000000 : ℝ)*(major2) + (585945154571613/10000000000000 : ℝ)*(sp0) + (117189425043619/2000000000000 : ℝ)*(sp1) + (2929727924431633/50000000000000 : ℝ)*(sp2) + (282934515947241/10000000000000 : ℝ)*(sp3) + (2603989911/12500000000000 : ℝ)*(sp4) + (499050391/3125000000000 : ℝ)*(sp6) + (6476383927/50000000000000 : ℝ)*(sp7) + (353669764030033/12500000000000 : ℝ)*(f.failure) + (2929736188817709/50000000000000 : ℝ)*(f.sum) + (14955869305103/3632000000000000000000000000 : ℝ)*base65 + (285924387028112961/181600000000000000000000000000000 : ℝ)*base67 + (1097673365930512961/181600000000000000000000000000000 : ℝ)*base69 + (1114845543341487039/181600000000000000000000000000000 : ℝ)*base72 + (13818782612143/3632000000000000000000000000 : ℝ)*base73 + (1835595268127312961/181600000000000000000000000000000 : ℝ)*base75 + (1656880887823087039/181600000000000000000000000000000 : ℝ)*base78 + (4320098243719087039/181600000000000000000000000000000 : ℝ)*base80 + (15856578784239/3632000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4685321/1250000000000000000000 : ℝ)*base89 + (4685321/1250000000000000000000 : ℝ)*base91 + (4685321/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (253705904626252119178492011/56750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (779963259/100000000000000 : ℝ)*(base19) + (929725033/100000000000000 : ℝ)*(base23) + (24586049/25000000000000 : ℝ)*(upper3) + (8319869/20000000000000 : ℝ)*(lower4) + (8371931/6250000000000 : ℝ)*(upper5) + (546965209791127/12500000000000 : ℝ)*(major0) + (546965209791127/12500000000000 : ℝ)*(major1) + (546965209791127/12500000000000 : ℝ)*(major2) + (9135916751/50000000000000 : ℝ)*(sp1) + (4236273179/25000000000000 : ℝ)*(sp2) + (2950848217919343/50000000000000 : ℝ)*(sp4) + (236067095361677/4000000000000 : ℝ)*(sp5) + (737709820127617/12500000000000 : ℝ)*(sp6) + (1424873385899857/50000000000000 : ℝ)*(sp7) + (1424873385899857/50000000000000 : ℝ)*(f.failure) + (2950848217919343/50000000000000 : ℝ)*(f.sum) + (3563618784091/2270000000000000000000000000 : ℝ)*base66 + (93109042728972337/113500000000000000000000000000000 : ℝ)*base68 + (781347928402027663/113500000000000000000000000000000 : ℝ)*base69 + (854021181291527663/113500000000000000000000000000000 : ℝ)*base71 + (3403964377559/2270000000000000000000000000 : ℝ)*base73 + (1140403905908472337/113500000000000000000000000000000 : ℝ)*base76 + (1502108526542027663/113500000000000000000000000000000 : ℝ)*base77 + (491936123912027663/113500000000000000000000000000000 : ℝ)*base79 + (13167280170269/2270000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (49026391/5000000000000000000000 : ℝ)*base90 + (49026391/5000000000000000000000 : ℝ)*base92 + (49026391/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1312_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153547737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7349/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5533/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2769/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (459/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1312_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1312_s7_0 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1035088993/5000000000 : ℝ)*x 0 + (5414194387/10000000000 : ℝ)*x 1 + (2621848349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035088993/5000000000 : ℝ)^267 ≤ (3149958250571/25000000000000 : ℝ)^203 := by
    have hnat : (1035088993 : ℕ)^267*25000000000000^203 ≤ 3149958250571^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035088993 5000000000 3149958250571 25000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414194387/10000000000 : ℝ)^267 ≤ (8923902273407/20000000000000 : ℝ)^203 := by
    have hnat : (5414194387 : ℕ)^267*20000000000000^203 ≤ 8923902273407^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414194387 10000000000 8923902273407 20000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621848349/5000000000 : ℝ)^267 ≤ (42780655616211/100000000000000 : ℝ)^203 := by
    have hnat : (2621848349 : ℕ)^267*100000000000000^203 ≤ 42780655616211^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621848349 5000000000 42780655616211 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1035088993/5000000000 : ℝ), (5414194387/10000000000 : ℝ), (2621848349/5000000000 : ℝ)] ![(3149958250571/25000000000000 : ℝ), (8923902273407/20000000000000 : ℝ), (42780655616211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1035088993/5000000000 : ℝ)|^267 ≤ (3149958250571/25000000000000 : ℝ)^203
        have hw : |(-1035088993/5000000000 : ℝ)|=(1035088993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414194387/10000000000 : ℝ)|^267 ≤ (8923902273407/20000000000000 : ℝ)^203
        have hw : |(5414194387/10000000000 : ℝ)|=(5414194387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621848349/5000000000 : ℝ)|^267 ≤ (42780655616211/100000000000000 : ℝ)^203
        have hw : |(2621848349/5000000000 : ℝ)|=(2621848349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s7_1 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1069895851/2000000000 : ℝ)*x 0 + (-2157071379/10000000000 : ℝ)*x 1 + (2621847931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069895851/2000000000 : ℝ)^267 ≤ (1097984049419/2500000000000 : ℝ)^203 := by
    have hnat : (1069895851 : ℕ)^267*2500000000000^203 ≤ 1097984049419^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069895851 2000000000 1097984049419 2500000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2157071379/10000000000 : ℝ)^267 ≤ (2659998273431/20000000000000 : ℝ)^203 := by
    have hnat : (2157071379 : ℕ)^267*20000000000000^203 ≤ 2659998273431^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157071379 10000000000 2659998273431 20000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621847931/5000000000 : ℝ)^267 ≤ (42780646645407/100000000000000 : ℝ)^203 := by
    have hnat : (2621847931 : ℕ)^267*100000000000000^203 ≤ 42780646645407^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621847931 5000000000 42780646645407 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069895851/2000000000 : ℝ), (-2157071379/10000000000 : ℝ), (2621847931/5000000000 : ℝ)] ![(1097984049419/2500000000000 : ℝ), (2659998273431/20000000000000 : ℝ), (42780646645407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069895851/2000000000 : ℝ)|^267 ≤ (1097984049419/2500000000000 : ℝ)^203
        have hw : |(1069895851/2000000000 : ℝ)|=(1069895851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2157071379/10000000000 : ℝ)|^267 ≤ (2659998273431/20000000000000 : ℝ)^203
        have hw : |(-2157071379/10000000000 : ℝ)|=(2157071379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621847931/5000000000 : ℝ)|^267 ≤ (42780646645407/100000000000000 : ℝ)^203
        have hw : |(2621847931/5000000000 : ℝ)|=(2621847931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s7_2 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5349478263/10000000000 : ℝ)*x 0 + (5243696661/10000000000 : ℝ)*x 1 + (-2157071643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349478263/10000000000 : ℝ)^267 ≤ (2195967563237/5000000000000 : ℝ)^203 := by
    have hnat : (5349478263 : ℕ)^267*5000000000000^203 ≤ 2195967563237^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349478263 10000000000 2195967563237 5000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243696661/10000000000 : ℝ)^267 ≤ (42780655219177/100000000000000 : ℝ)^203 := by
    have hnat : (5243696661 : ℕ)^267*100000000000000^203 ≤ 42780655219177^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243696661 10000000000 42780655219177 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2157071643/10000000000 : ℝ)^267 ≤ (6649996754051/50000000000000 : ℝ)^203 := by
    have hnat : (2157071643 : ℕ)^267*50000000000000^203 ≤ 6649996754051^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157071643 10000000000 6649996754051 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349478263/10000000000 : ℝ), (5243696661/10000000000 : ℝ), (-2157071643/10000000000 : ℝ)] ![(2195967563237/5000000000000 : ℝ), (42780655219177/100000000000000 : ℝ), (6649996754051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349478263/10000000000 : ℝ)|^267 ≤ (2195967563237/5000000000000 : ℝ)^203
        have hw : |(5349478263/10000000000 : ℝ)|=(5349478263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243696661/10000000000 : ℝ)|^267 ≤ (42780655219177/100000000000000 : ℝ)^203
        have hw : |(5243696661/10000000000 : ℝ)|=(5243696661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2157071643/10000000000 : ℝ)|^267 ≤ (6649996754051/50000000000000 : ℝ)^203
        have hw : |(-2157071643/10000000000 : ℝ)|=(2157071643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s7_3 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (541816109/1250000000 : ℝ)*x 0 + (4161387273/10000000000 : ℝ)*x 1 + (2257239827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541816109/1250000000 : ℝ)^267 ≤ (33302760425351/100000000000000 : ℝ)^203 := by
    have hnat : (541816109 : ℕ)^267*100000000000000^203 ≤ 33302760425351^203*1250000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541816109 1250000000 33302760425351 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4161387273/10000000000 : ℝ)^267 ≤ (7891053604813/25000000000000 : ℝ)^203 := by
    have hnat : (4161387273 : ℕ)^267*25000000000000^203 ≤ 7891053604813^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161387273 10000000000 7891053604813 25000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257239827/5000000000 : ℝ)^267 ≤ (219581407093/625000000000 : ℝ)^203 := by
    have hnat : (2257239827 : ℕ)^267*625000000000^203 ≤ 219581407093^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257239827 5000000000 219581407093 625000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541816109/1250000000 : ℝ), (4161387273/10000000000 : ℝ), (2257239827/5000000000 : ℝ)] ![(33302760425351/100000000000000 : ℝ), (7891053604813/25000000000000 : ℝ), (219581407093/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541816109/1250000000 : ℝ)|^267 ≤ (33302760425351/100000000000000 : ℝ)^203
        have hw : |(541816109/1250000000 : ℝ)|=(541816109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4161387273/10000000000 : ℝ)|^267 ≤ (7891053604813/25000000000000 : ℝ)^203
        have hw : |(4161387273/10000000000 : ℝ)|=(4161387273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2257239827/5000000000 : ℝ)|^267 ≤ (219581407093/625000000000 : ℝ)^203
        have hw : |(2257239827/5000000000 : ℝ)|=(2257239827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s7_4 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-414038147/2000000000 : ℝ)*x 0 + (1048861047/2000000000 : ℝ)*x 1 + (135339563/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414038147/2000000000 : ℝ)^267 ≤ (12599935060711/100000000000000 : ℝ)^203 := by
    have hnat : (414038147 : ℕ)^267*100000000000000^203 ≤ 12599935060711^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414038147 2000000000 12599935060711 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048861047/2000000000 : ℝ)^267 ≤ (2139359285959/5000000000000 : ℝ)^203 := by
    have hnat : (1048861047 : ℕ)^267*5000000000000^203 ≤ 2139359285959^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048861047 2000000000 2139359285959 5000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135339563/250000000 : ℝ)^267 ≤ (44612879199583/100000000000000 : ℝ)^203 := by
    have hnat : (135339563 : ℕ)^267*100000000000000^203 ≤ 44612879199583^203*250000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135339563 250000000 44612879199583 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-414038147/2000000000 : ℝ), (1048861047/2000000000 : ℝ), (135339563/250000000 : ℝ)] ![(12599935060711/100000000000000 : ℝ), (2139359285959/5000000000000 : ℝ), (44612879199583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-414038147/2000000000 : ℝ)|^267 ≤ (12599935060711/100000000000000 : ℝ)^203
        have hw : |(-414038147/2000000000 : ℝ)|=(414038147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048861047/2000000000 : ℝ)|^267 ≤ (2139359285959/5000000000000 : ℝ)^203
        have hw : |(1048861047/2000000000 : ℝ)|=(1048861047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135339563/250000000 : ℝ)|^267 ≤ (44612879199583/100000000000000 : ℝ)^203
        have hw : |(135339563/250000000 : ℝ)|=(135339563/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s7_5 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5305717979/10000000000 : ℝ)*x 0 + (-397437143/2000000000 : ℝ)*x 1 + (5413582499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305717979/10000000000 : ℝ)^267 ≤ (21723710185483/50000000000000 : ℝ)^203 := by
    have hnat : (5305717979 : ℕ)^267*50000000000000^203 ≤ 21723710185483^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305717979 10000000000 21723710185483 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397437143/2000000000 : ℝ)^267 ≤ (11939700637803/100000000000000 : ℝ)^203 := by
    have hnat : (397437143 : ℕ)^267*100000000000000^203 ≤ 11939700637803^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397437143 2000000000 11939700637803 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413582499/10000000000 : ℝ)^267 ≤ (44612878971963/100000000000000 : ℝ)^203 := by
    have hnat : (5413582499 : ℕ)^267*100000000000000^203 ≤ 44612878971963^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413582499 10000000000 44612878971963 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305717979/10000000000 : ℝ), (-397437143/2000000000 : ℝ), (5413582499/10000000000 : ℝ)] ![(21723710185483/50000000000000 : ℝ), (11939700637803/100000000000000 : ℝ), (44612878971963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305717979/10000000000 : ℝ)|^267 ≤ (21723710185483/50000000000000 : ℝ)^203
        have hw : |(5305717979/10000000000 : ℝ)|=(5305717979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-397437143/2000000000 : ℝ)|^267 ≤ (11939700637803/100000000000000 : ℝ)^203
        have hw : |(-397437143/2000000000 : ℝ)|=(397437143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413582499/10000000000 : ℝ)|^267 ≤ (44612878971963/100000000000000 : ℝ)^203
        have hw : |(5413582499/10000000000 : ℝ)|=(5413582499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s7_6 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1326429489/2500000000 : ℝ)*x 0 + (5413582507/10000000000 : ℝ)*x 1 + (-397437147/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326429489/2500000000 : ℝ)^267 ≤ (8689484024649/20000000000000 : ℝ)^203 := by
    have hnat : (1326429489 : ℕ)^267*20000000000000^203 ≤ 8689484024649^203*2500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326429489 2500000000 8689484024649 20000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413582507/10000000000 : ℝ)^267 ≤ (1784515162347/4000000000000 : ℝ)^203 := by
    have hnat : (5413582507 : ℕ)^267*4000000000000^203 ≤ 1784515162347^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413582507 10000000000 1784515162347 4000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397437147/2000000000 : ℝ)^267 ≤ (2387940159171/20000000000000 : ℝ)^203 := by
    have hnat : (397437147 : ℕ)^267*20000000000000^203 ≤ 2387940159171^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397437147 2000000000 2387940159171 20000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326429489/2500000000 : ℝ), (5413582507/10000000000 : ℝ), (-397437147/2000000000 : ℝ)] ![(8689484024649/20000000000000 : ℝ), (1784515162347/4000000000000 : ℝ), (2387940159171/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326429489/2500000000 : ℝ)|^267 ≤ (8689484024649/20000000000000 : ℝ)^203
        have hw : |(1326429489/2500000000 : ℝ)|=(1326429489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413582507/10000000000 : ℝ)|^267 ≤ (1784515162347/4000000000000 : ℝ)^203
        have hw : |(5413582507/10000000000 : ℝ)|=(5413582507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-397437147/2000000000 : ℝ)|^267 ≤ (2387940159171/20000000000000 : ℝ)^203
        have hw : |(-397437147/2000000000 : ℝ)|=(397437147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_s7_7 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (866910787/2000000000 : ℝ)*x 0 + (4513219977/10000000000 : ℝ)*x 1 + (4065092/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866910787/2000000000 : ℝ)^267 ≤ (133212054789/400000000000 : ℝ)^203 := by
    have hnat : (866910787 : ℕ)^267*400000000000^203 ≤ 133212054789^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866910787 2000000000 133212054789 400000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4513219977/10000000000 : ℝ)^267 ≤ (17560065931133/50000000000000 : ℝ)^203 := by
    have hnat : (4513219977 : ℕ)^267*50000000000000^203 ≤ 17560065931133^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513219977 10000000000 17560065931133 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4065092/9765625 : ℝ)^267 ≤ (15788427212167/50000000000000 : ℝ)^203 := by
    have hnat : (4065092 : ℕ)^267*50000000000000^203 ≤ 15788427212167^203*9765625^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4065092 9765625 15788427212167 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(866910787/2000000000 : ℝ), (4513219977/10000000000 : ℝ), (4065092/9765625 : ℝ)] ![(133212054789/400000000000 : ℝ), (17560065931133/50000000000000 : ℝ), (15788427212167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(866910787/2000000000 : ℝ)|^267 ≤ (133212054789/400000000000 : ℝ)^203
        have hw : |(866910787/2000000000 : ℝ)|=(866910787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4513219977/10000000000 : ℝ)|^267 ≤ (17560065931133/50000000000000 : ℝ)^203
        have hw : |(4513219977/10000000000 : ℝ)|=(4513219977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4065092/9765625 : ℝ)|^267 ≤ (15788427212167/50000000000000 : ℝ)^203
        have hw : |(4065092/9765625 : ℝ)|=(4065092/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1312_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153547737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (459/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2769/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5539/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7343/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (459/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2769/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (459/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2769/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (459/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2769/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (459/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2769/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (459/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2769/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (459/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2769/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2769/25000 : ℝ) ^ (4271/1024 : ℝ) ≤ (5166403613595933/50000000000000000000 : ℝ) := by
    have hpowers : (2769/25000 : ℝ)^4271 ≤ (5166403613595933/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2769 : ℕ)^4271*50000000000000000000^1024 ≤ 5166403613595933^1024*25000^4271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2769 25000 5166403613595933 50000000000000000000 4271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2769/25000 : ℝ)) (X := (5166403613595933/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (459/3125 : ℝ) ^ (4271/1024 : ℝ) ≤ (33534039866313689/100000000000000000000 : ℝ) := by
    have hpowers : (459/3125 : ℝ)^4271 ≤ (33534039866313689/100000000000000000000 : ℝ)^1024 := by
      have hnat : (459 : ℕ)^4271*100000000000000000000^1024 ≤ 33534039866313689^1024*3125^4271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        459 3125 33534039866313689 100000000000000000000 4271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (459/3125 : ℝ)) (X := (33534039866313689/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005166403613595933/25000000000000000000 : ℝ) ≤ (78128870567319/78125000000000 : ℝ) ^ (4271/1024 : ℝ) := by
    have hpowers : (25005166403613595933/25000000000000000000 : ℝ)^1024 ≤ (78128870567319/78125000000000 : ℝ)^4271 := by
      have hnat : (25005166403613595933 : ℕ)^1024*78125000000000^4271 ≤ 78128870567319^4271*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005166403613595933 25000000000000000000 78128870567319 78125000000000 1024 4271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78128870567319/78125000000000 : ℝ)) (X := (25005166403613595933/25000000000000000000 : ℝ)) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008773369418701111/20000000000000000000 : ℝ) ≤ (10001051560831533/10000000000000000 : ℝ) ^ (4271/1024 : ℝ) := by
    have hpowers : (20008773369418701111/20000000000000000000 : ℝ)^1024 ≤ (10001051560831533/10000000000000000 : ℝ)^4271 := by
      have hnat : (20008773369418701111 : ℕ)^1024*10000000000000000^4271 ≤ 10001051560831533^4271*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008773369418701111 20000000000000000000 10001051560831533 10000000000000000 1024 4271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001051560831533/10000000000000000 : ℝ)) (X := (20008773369418701111/20000000000000000000 : ℝ)) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033534039866313689/50000000000000000000 : ℝ) ≤ (5000803844523117/5000000000000000 : ℝ) ^ (4271/1024 : ℝ) := by
    have hpowers : (50033534039866313689/50000000000000000000 : ℝ)^1024 ≤ (5000803844523117/5000000000000000 : ℝ)^4271 := by
      have hnat : (50033534039866313689 : ℕ)^1024*5000000000000000^4271 ≤ 5000803844523117^4271*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033534039866313689 50000000000000000000 5000803844523117 5000000000000000 1024 4271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000803844523117/5000000000000000 : ℝ)) (X := (50033534039866313689/50000000000000000000 : ℝ)) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5166403613595933/50000000000000000000 : ℝ) ≤ ((1504561256266664193/1505000000000000000 : ℝ)+2*(185376071567/120400000000000 : ℝ)*(2769/25000 : ℝ))^(4271/1024 : ℝ) := by
    rw [show (1504561256266664193/1505000000000000000 : ℝ)+2*(185376071567/120400000000000 : ℝ)*(2769/25000 : ℝ)=(78128870567319/78125000000000 : ℝ) by norm_num, show 1+2*(5166403613595933/50000000000000000000 : ℝ)=(25005166403613595933/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33534039866313689/100000000000000000000 : ℝ)+(5166403613595933/50000000000000000000 : ℝ) ≤ ((1504561256266664193/1505000000000000000 : ℝ)+(185376071567/120400000000000 : ℝ)*((459/3125 : ℝ)+(2769/25000 : ℝ)))^(4271/1024 : ℝ) := by
    rw [show (1504561256266664193/1505000000000000000 : ℝ)+(185376071567/120400000000000 : ℝ)*((459/3125 : ℝ)+(2769/25000 : ℝ))=(10001051560831533/10000000000000000 : ℝ) by norm_num, show 1+(33534039866313689/100000000000000000000 : ℝ)+(5166403613595933/50000000000000000000 : ℝ)=(20008773369418701111/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33534039866313689/100000000000000000000 : ℝ) ≤ ((1504561256266664193/1505000000000000000 : ℝ)+2*(185376071567/120400000000000 : ℝ)*(459/3125 : ℝ))^(4271/1024 : ℝ) := by
    rw [show (1504561256266664193/1505000000000000000 : ℝ)+2*(185376071567/120400000000000 : ℝ)*(459/3125 : ℝ)=(5000803844523117/5000000000000000 : ℝ) by norm_num, show 1+2*(33534039866313689/100000000000000000000 : ℝ)=(50033534039866313689/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1504561256266664193/1505000000000000000 : ℝ)*(X 1 0+X 2 0)+(185376071567/120400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4271/1024 : ℝ)) (lo := (2769/25000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (1504561256266664193/1505000000000000000 : ℝ)) (alpha := (185376071567/120400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1504561256266664193/1505000000000000000 : ℝ)*(X 0 1+X 2 1)+(185376071567/120400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4271/1024 : ℝ)) (lo := (2769/25000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (1504561256266664193/1505000000000000000 : ℝ)) (alpha := (185376071567/120400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1504561256266664193/1505000000000000000 : ℝ)*(X 0 2+X 1 2)+(185376071567/120400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4271/1024 : ℝ)) (lo := (2769/25000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (1504561256266664193/1505000000000000000 : ℝ)) (alpha := (185376071567/120400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1035088993/5000000000 : ℝ)*X 0 0+(5414194387/10000000000 : ℝ)*X 0 1+(2621848349/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069895851/2000000000 : ℝ)*X 1 0+(-2157071379/10000000000 : ℝ)*X 1 1+(2621847931/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349478263/10000000000 : ℝ)*X 2 0+(5243696661/10000000000 : ℝ)*X 2 1+(-2157071643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((541816109/1250000000 : ℝ)*X 0 0+(4161387273/10000000000 : ℝ)*X 0 1+(2257239827/5000000000 : ℝ)*X 0 2+(541816109/1250000000 : ℝ)*X 1 0+(4161387273/10000000000 : ℝ)*X 1 1+(2257239827/5000000000 : ℝ)*X 1 2+(541816109/1250000000 : ℝ)*X 2 0+(4161387273/10000000000 : ℝ)*X 2 1+(2257239827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-414038147/2000000000 : ℝ)*X 0 0+(1048861047/2000000000 : ℝ)*X 0 1+(135339563/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305717979/10000000000 : ℝ)*X 1 0+(-397437143/2000000000 : ℝ)*X 1 1+(5413582499/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326429489/2500000000 : ℝ)*X 2 0+(5413582507/10000000000 : ℝ)*X 2 1+(-397437147/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((866910787/2000000000 : ℝ)*X 0 0+(4513219977/10000000000 : ℝ)*X 0 1+(4065092/9765625 : ℝ)*X 0 2+(866910787/2000000000 : ℝ)*X 1 0+(4513219977/10000000000 : ℝ)*X 1 1+(4065092/9765625 : ℝ)*X 1 2+(866910787/2000000000 : ℝ)*X 2 0+(4513219977/10000000000 : ℝ)*X 2 1+(4065092/9765625 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85609058883497820591/188125000000000000000000000 : ℝ) := by norm_num
    linear_combination (773735179/50000000000000 : ℝ)*(base19) + (1038843999/100000000000000 : ℝ)*(base23) + (25341947/50000000000000 : ℝ)*(lower2) + (84572209/100000000000000 : ℝ)*(upper3) + (36042493/10000000000000 : ℝ)*(lower4) + (1087169041753047/25000000000000 : ℝ)*(major0) + (1087169041753047/25000000000000 : ℝ)*(major1) + (1087169041753047/25000000000000 : ℝ)*(major2) + (5865209810982901/100000000000000 : ℝ)*(sp0) + (5865217747495563/100000000000000 : ℝ)*(sp1) + (2932609128060961/50000000000000 : ℝ)*(sp2) + (70803226370257/2500000000000 : ℝ)*(sp3) + (474199151/5000000000000 : ℝ)*(sp4) + (793815869/20000000000000 : ℝ)*(sp7) + (22657064191117/800000000000 : ℝ)*(f.failure) + (5865219294965921/100000000000000 : ℝ)*(f.sum) + (12478205363/188125000000000000000000000 : ℝ)*base65 + (204920591419841429/37625000000000000000000000000000 : ℝ)*base68 + (42832854680591429/37625000000000000000000000000000 : ℝ)*base70 + (485900956479158571/37625000000000000000000000000000 : ℝ)*base71 + (97947127991/1505000000000000000000000000 : ℝ)*base74 + (129885121393408571/37625000000000000000000000000000 : ℝ)*base75 + (262267892451533571/37625000000000000000000000000000 : ℝ)*base77 + (250673195489216429/37625000000000000000000000000000 : ℝ)*base80 + (4046117168479/1505000000000000000000000000 : ℝ)*base81 + (452229/80000000000000000000 : ℝ)*base89 + (452229/80000000000000000000 : ℝ)*base91 + (452229/80000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46763241923529291413814783/18812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104705021/20000000000000 : ℝ)*(base19) + (60238213/10000000000000 : ℝ)*(base23) + (79768743/50000000000000 : ℝ)*(lower1) + (2726693/4000000000000 : ℝ)*(upper3) + (45936723/100000000000000 : ℝ)*(lower4) + (3536077/12500000000000 : ℝ)*(upper5) + (2189995661244127/50000000000000 : ℝ)*(major0) + (2189995661244127/50000000000000 : ℝ)*(major1) + (2189995661244127/50000000000000 : ℝ)*(major2) + (271071347/12500000000000 : ℝ)*(sp2) + (2953727563968791/50000000000000 : ℝ)*(sp4) + (5907454604412477/100000000000000 : ℝ)*(sp5) + (1476863089246169/25000000000000 : ℝ)*(sp6) + (356565929272557/12500000000000 : ℝ)*(sp7) + (356565929272557/12500000000000 : ℝ)*(f.failure) + (2953727563968791/50000000000000 : ℝ)*(f.sum) + (14383033751109/3010000000000000000000000000 : ℝ)*base65 + (1485670040005442989/75250000000000000000000000000000 : ℝ)*base68 + (376636609006942989/75250000000000000000000000000000 : ℝ)*base70 + (2597963396345692989/75250000000000000000000000000000 : ℝ)*base72 + (16671200031439/3010000000000000000000000000 : ℝ)*base73 + (3093024156077692989/75250000000000000000000000000000 : ℝ)*base76 + (148040011489057011/75250000000000000000000000000000 : ℝ)*base77 + (167154582329942989/75250000000000000000000000000000 : ℝ)*base80 + (11354469193191/3010000000000000000000000000 : ℝ)*base82 + (8553509/1250000000000000000000 : ℝ)*base89 + (8553509/1250000000000000000000 : ℝ)*base91 + (8553509/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1312_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153547737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (459/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2769/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5539/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1312_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1312_box_0 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-380100001/2000000000 : ℝ)*x 0 + (134779673/250000000 : ℝ)*x 1 + (5391187097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (380100001/2000000000 : ℝ)^267 ≤ (5629708127859/50000000000000 : ℝ)^203 := by
    have hnat : (380100001 : ℕ)^267*50000000000000^203 ≤ 5629708127859^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380100001 2000000000 5629708127859 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134779673/250000000 : ℝ)^267 ≤ (44370290905007/100000000000000 : ℝ)^203 := by
    have hnat : (134779673 : ℕ)^267*100000000000000^203 ≤ 44370290905007^203*250000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134779673 250000000 44370290905007 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391187097/10000000000 : ℝ)^267 ≤ (44370292821011/100000000000000 : ℝ)^203 := by
    have hnat : (5391187097 : ℕ)^267*100000000000000^203 ≤ 44370292821011^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391187097 10000000000 44370292821011 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-380100001/2000000000 : ℝ), (134779673/250000000 : ℝ), (5391187097/10000000000 : ℝ)] ![(5629708127859/50000000000000 : ℝ), (44370290905007/100000000000000 : ℝ), (44370292821011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-380100001/2000000000 : ℝ)|^267 ≤ (5629708127859/50000000000000 : ℝ)^203
        have hw : |(-380100001/2000000000 : ℝ)|=(380100001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134779673/250000000 : ℝ)|^267 ≤ (44370290905007/100000000000000 : ℝ)^203
        have hw : |(134779673/250000000 : ℝ)|=(134779673/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391187097/10000000000 : ℝ)|^267 ≤ (44370292821011/100000000000000 : ℝ)^203
        have hw : |(5391187097/10000000000 : ℝ)|=(5391187097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_box_1 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5284713677/10000000000 : ℝ)*x 0 + (-1023108223/5000000000 : ℝ)*x 1 + (5391187557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284713677/10000000000 : ℝ)^267 ≤ (43221335260773/100000000000000 : ℝ)^203 := by
    have hnat : (5284713677 : ℕ)^267*100000000000000^203 ≤ 43221335260773^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284713677 10000000000 43221335260773 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1023108223/5000000000 : ℝ)^267 ≤ (12408366933563/100000000000000 : ℝ)^203 := by
    have hnat : (1023108223 : ℕ)^267*100000000000000^203 ≤ 12408366933563^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023108223 5000000000 12408366933563 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391187557/10000000000 : ℝ)^267 ≤ (5546287225057/12500000000000 : ℝ)^203 := by
    have hnat : (5391187557 : ℕ)^267*12500000000000^203 ≤ 5546287225057^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391187557 10000000000 5546287225057 12500000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284713677/10000000000 : ℝ), (-1023108223/5000000000 : ℝ), (5391187557/10000000000 : ℝ)] ![(43221335260773/100000000000000 : ℝ), (12408366933563/100000000000000 : ℝ), (5546287225057/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284713677/10000000000 : ℝ)|^267 ≤ (43221335260773/100000000000000 : ℝ)^203
        have hw : |(5284713677/10000000000 : ℝ)|=(5284713677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1023108223/5000000000 : ℝ)|^267 ≤ (12408366933563/100000000000000 : ℝ)^203
        have hw : |(-1023108223/5000000000 : ℝ)|=(1023108223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391187557/10000000000 : ℝ)|^267 ≤ (5546287225057/12500000000000 : ℝ)^203
        have hw : |(5391187557/10000000000 : ℝ)|=(5391187557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_box_2 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (264235711/500000000 : ℝ)*x 0 + (5391187109/10000000000 : ℝ)*x 1 + (-3197213/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264235711/500000000 : ℝ)^267 ≤ (21610670550917/50000000000000 : ℝ)^203 := by
    have hnat : (264235711 : ℕ)^267*50000000000000^203 ≤ 21610670550917^203*500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264235711 500000000 21610670550917 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391187109/10000000000 : ℝ)^267 ≤ (4437029295091/10000000000000 : ℝ)^203 := by
    have hnat : (5391187109 : ℕ)^267*10000000000000^203 ≤ 4437029295091^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391187109 10000000000 4437029295091 10000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3197213/15625000 : ℝ)^267 ≤ (12408365928603/100000000000000 : ℝ)^203 := by
    have hnat : (3197213 : ℕ)^267*100000000000000^203 ≤ 12408365928603^203*15625000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3197213 15625000 12408365928603 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264235711/500000000 : ℝ), (5391187109/10000000000 : ℝ), (-3197213/15625000 : ℝ)] ![(21610670550917/50000000000000 : ℝ), (4437029295091/10000000000000 : ℝ), (12408365928603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264235711/500000000 : ℝ)|^267 ≤ (21610670550917/50000000000000 : ℝ)^203
        have hw : |(264235711/500000000 : ℝ)|=(264235711/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391187109/10000000000 : ℝ)|^267 ≤ (4437029295091/10000000000000 : ℝ)^203
        have hw : |(5391187109/10000000000 : ℝ)|=(5391187109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3197213/15625000 : ℝ)|^267 ≤ (12408365928603/100000000000000 : ℝ)^203
        have hw : |(-3197213/15625000 : ℝ)|=(3197213/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_box_3 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (896688557/2000000000 : ℝ)*x 0 + (4264028401/10000000000 : ℝ)*x 1 + (852805709/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (896688557/2000000000 : ℝ)^267 ≤ (17407840924243/50000000000000 : ℝ)^203 := by
    have hnat : (896688557 : ℕ)^267*50000000000000^203 ≤ 17407840924243^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896688557 2000000000 17407840924243 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4264028401/10000000000 : ℝ)^267 ≤ (407401979267/1250000000000 : ℝ)^203 := by
    have hnat : (4264028401 : ℕ)^267*1250000000000^203 ≤ 407401979267^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4264028401 10000000000 407401979267 1250000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (852805709/2000000000 : ℝ)^267 ≤ (32592159789033/100000000000000 : ℝ)^203 := by
    have hnat : (852805709 : ℕ)^267*100000000000000^203 ≤ 32592159789033^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852805709 2000000000 32592159789033 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(896688557/2000000000 : ℝ), (4264028401/10000000000 : ℝ), (852805709/2000000000 : ℝ)] ![(17407840924243/50000000000000 : ℝ), (407401979267/1250000000000 : ℝ), (32592159789033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(896688557/2000000000 : ℝ)|^267 ≤ (17407840924243/50000000000000 : ℝ)^203
        have hw : |(896688557/2000000000 : ℝ)|=(896688557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4264028401/10000000000 : ℝ)|^267 ≤ (407401979267/1250000000000 : ℝ)^203
        have hw : |(4264028401/10000000000 : ℝ)|=(4264028401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(852805709/2000000000 : ℝ)|^267 ≤ (32592159789033/100000000000000 : ℝ)^203
        have hw : |(852805709/2000000000 : ℝ)|=(852805709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_box_4 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-89704551/400000000 : ℝ)*x 0 + (2632109197/5000000000 : ℝ)*x 1 + (5264217253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (89704551/400000000 : ℝ)^267 ≤ (6999004112827/50000000000000 : ℝ)^203 := by
    have hnat : (89704551 : ℕ)^267*50000000000000^203 ≤ 6999004112827^203*400000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89704551 400000000 6999004112827 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632109197/5000000000 : ℝ)^267 ≤ (10750250502807/25000000000000 : ℝ)^203 := by
    have hnat : (2632109197 : ℕ)^267*25000000000000^203 ≤ 10750250502807^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632109197 5000000000 10750250502807 25000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264217253/10000000000 : ℝ)^267 ≤ (43000989752497/100000000000000 : ℝ)^203 := by
    have hnat : (5264217253 : ℕ)^267*100000000000000^203 ≤ 43000989752497^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264217253 10000000000 43000989752497 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-89704551/400000000 : ℝ), (2632109197/5000000000 : ℝ), (5264217253/10000000000 : ℝ)] ![(6999004112827/50000000000000 : ℝ), (10750250502807/25000000000000 : ℝ), (43000989752497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-89704551/400000000 : ℝ)|^267 ≤ (6999004112827/50000000000000 : ℝ)^203
        have hw : |(-89704551/400000000 : ℝ)|=(89704551/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632109197/5000000000 : ℝ)|^267 ≤ (10750250502807/25000000000000 : ℝ)^203
        have hw : |(2632109197/5000000000 : ℝ)|=(2632109197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264217253/10000000000 : ℝ)|^267 ≤ (43000989752497/100000000000000 : ℝ)^203
        have hw : |(5264217253/10000000000 : ℝ)|=(5264217253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_box_5 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5374008977/10000000000 : ℝ)*x 0 + (-2096948953/10000000000 : ℝ)*x 1 + (5264217201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374008977/10000000000 : ℝ)^267 ≤ (44184435190617/100000000000000 : ℝ)^203 := by
    have hnat : (5374008977 : ℕ)^267*100000000000000^203 ≤ 44184435190617^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374008977 10000000000 44184435190617 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2096948953/10000000000 : ℝ)^267 ≤ (1601821949781/12500000000000 : ℝ)^203 := by
    have hnat : (2096948953 : ℕ)^267*12500000000000^203 ≤ 1601821949781^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096948953 10000000000 1601821949781 12500000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264217201/10000000000 : ℝ)^267 ≤ (43000989193817/100000000000000 : ℝ)^203 := by
    have hnat : (5264217201 : ℕ)^267*100000000000000^203 ≤ 43000989193817^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264217201 10000000000 43000989193817 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374008977/10000000000 : ℝ), (-2096948953/10000000000 : ℝ), (5264217201/10000000000 : ℝ)] ![(44184435190617/100000000000000 : ℝ), (1601821949781/12500000000000 : ℝ), (43000989193817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374008977/10000000000 : ℝ)|^267 ≤ (44184435190617/100000000000000 : ℝ)^203
        have hw : |(5374008977/10000000000 : ℝ)|=(5374008977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2096948953/10000000000 : ℝ)|^267 ≤ (1601821949781/12500000000000 : ℝ)^203
        have hw : |(-2096948953/10000000000 : ℝ)|=(2096948953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264217201/10000000000 : ℝ)|^267 ≤ (43000989193817/100000000000000 : ℝ)^203
        have hw : |(5264217201/10000000000 : ℝ)|=(5264217201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_box_6 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (67175131/125000000 : ℝ)*x 0 + (32901353/62500000 : ℝ)*x 1 + (-419389579/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67175131/125000000 : ℝ)^267 ≤ (11046112861013/25000000000000 : ℝ)^203 := by
    have hnat : (67175131 : ℕ)^267*25000000000000^203 ≤ 11046112861013^203*125000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67175131 125000000 11046112861013 25000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32901353/62500000 : ℝ)^267 ≤ (21500490723751/50000000000000 : ℝ)^203 := by
    have hnat : (32901353 : ℕ)^267*50000000000000^203 ≤ 21500490723751^203*62500000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32901353 62500000 21500490723751 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (419389579/2000000000 : ℝ)^267 ≤ (6407283547183/50000000000000 : ℝ)^203 := by
    have hnat : (419389579 : ℕ)^267*50000000000000^203 ≤ 6407283547183^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419389579 2000000000 6407283547183 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67175131/125000000 : ℝ), (32901353/62500000 : ℝ), (-419389579/2000000000 : ℝ)] ![(11046112861013/25000000000000 : ℝ), (21500490723751/50000000000000 : ℝ), (6407283547183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67175131/125000000 : ℝ)|^267 ≤ (11046112861013/25000000000000 : ℝ)^203
        have hw : |(67175131/125000000 : ℝ)|=(67175131/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32901353/62500000 : ℝ)|^267 ≤ (21500490723751/50000000000000 : ℝ)^203
        have hw : |(32901353/62500000 : ℝ)|=(32901353/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-419389579/2000000000 : ℝ)|^267 ≤ (6407283547183/50000000000000 : ℝ)^203
        have hw : |(-419389579/2000000000 : ℝ)|=(419389579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_box_7 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2092366471/5000000000 : ℝ)*x 0 + (4413327857/10000000000 : ℝ)*x 1 + (441332967/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092366471/5000000000 : ℝ)^267 ≤ (1271892996087/4000000000000 : ℝ)^203 := by
    have hnat : (2092366471 : ℕ)^267*4000000000000^203 ≤ 1271892996087^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092366471 5000000000 1271892996087 4000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4413327857/10000000000 : ℝ)^267 ≤ (426266604161/1250000000000 : ℝ)^203 := by
    have hnat : (4413327857 : ℕ)^267*1250000000000^203 ≤ 426266604161^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4413327857 10000000000 426266604161 1250000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441332967/1000000000 : ℝ)^267 ≤ (8525336689583/25000000000000 : ℝ)^203 := by
    have hnat : (441332967 : ℕ)^267*25000000000000^203 ≤ 8525336689583^203*1000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441332967 1000000000 8525336689583 25000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2092366471/5000000000 : ℝ), (4413327857/10000000000 : ℝ), (441332967/1000000000 : ℝ)] ![(1271892996087/4000000000000 : ℝ), (426266604161/1250000000000 : ℝ), (8525336689583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2092366471/5000000000 : ℝ)|^267 ≤ (1271892996087/4000000000000 : ℝ)^203
        have hw : |(2092366471/5000000000 : ℝ)|=(2092366471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4413327857/10000000000 : ℝ)|^267 ≤ (426266604161/1250000000000 : ℝ)^203
        have hw : |(4413327857/10000000000 : ℝ)|=(4413327857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(441332967/1000000000 : ℝ)|^267 ≤ (8525336689583/25000000000000 : ℝ)^203
        have hw : |(441332967/1000000000 : ℝ)|=(441332967/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_box_8 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-542713359/2500000000 : ℝ)*x 0 + (5176952393/10000000000 : ℝ)*x 1 + (1081043637/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542713359/2500000000 : ℝ)^267 ≤ (3352967854897/25000000000000 : ℝ)^203 := by
    have hnat : (542713359 : ℕ)^267*25000000000000^203 ≤ 3352967854897^203*2500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542713359 2500000000 3352967854897 25000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176952393/10000000000 : ℝ)^267 ≤ (42065888621029/100000000000000 : ℝ)^203 := by
    have hnat : (5176952393 : ℕ)^267*100000000000000^203 ≤ 42065888621029^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176952393 10000000000 42065888621029 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081043637/2000000000 : ℝ)^267 ≤ (556527999359/1250000000000 : ℝ)^203 := by
    have hnat : (1081043637 : ℕ)^267*1250000000000^203 ≤ 556527999359^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081043637 2000000000 556527999359 1250000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-542713359/2500000000 : ℝ), (5176952393/10000000000 : ℝ), (1081043637/2000000000 : ℝ)] ![(3352967854897/25000000000000 : ℝ), (42065888621029/100000000000000 : ℝ), (556527999359/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-542713359/2500000000 : ℝ)|^267 ≤ (3352967854897/25000000000000 : ℝ)^203
        have hw : |(-542713359/2500000000 : ℝ)|=(542713359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176952393/10000000000 : ℝ)|^267 ≤ (42065888621029/100000000000000 : ℝ)^203
        have hw : |(5176952393/10000000000 : ℝ)|=(5176952393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081043637/2000000000 : ℝ)|^267 ≤ (556527999359/1250000000000 : ℝ)^203
        have hw : |(1081043637/2000000000 : ℝ)|=(1081043637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_box_9 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5274840191/10000000000 : ℝ)*x 0 + (-2040475497/10000000000 : ℝ)*x 1 + (2702609307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274840191/10000000000 : ℝ)^267 ≤ (21557578638159/50000000000000 : ℝ)^203 := by
    have hnat : (5274840191 : ℕ)^267*50000000000000^203 ≤ 21557578638159^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274840191 10000000000 21557578638159 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2040475497/10000000000 : ℝ)^267 ≤ (6181299056101/50000000000000 : ℝ)^203 := by
    have hnat : (2040475497 : ℕ)^267*50000000000000^203 ≤ 6181299056101^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040475497 10000000000 6181299056101 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702609307/5000000000 : ℝ)^267 ≤ (44522244596401/100000000000000 : ℝ)^203 := by
    have hnat : (2702609307 : ℕ)^267*100000000000000^203 ≤ 44522244596401^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702609307 5000000000 44522244596401 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274840191/10000000000 : ℝ), (-2040475497/10000000000 : ℝ), (2702609307/5000000000 : ℝ)] ![(21557578638159/50000000000000 : ℝ), (6181299056101/50000000000000 : ℝ), (44522244596401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274840191/10000000000 : ℝ)|^267 ≤ (21557578638159/50000000000000 : ℝ)^203
        have hw : |(5274840191/10000000000 : ℝ)|=(5274840191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2040475497/10000000000 : ℝ)|^267 ≤ (6181299056101/50000000000000 : ℝ)^203
        have hw : |(-2040475497/10000000000 : ℝ)|=(2040475497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702609307/5000000000 : ℝ)|^267 ≤ (44522244596401/100000000000000 : ℝ)^203
        have hw : |(2702609307/5000000000 : ℝ)|=(2702609307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_box_10 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2637420411/5000000000 : ℝ)*x 0 + (5405218213/10000000000 : ℝ)*x 1 + (-2040475191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637420411/5000000000 : ℝ)^267 ≤ (43115164059997/100000000000000 : ℝ)^203 := by
    have hnat : (2637420411 : ℕ)^267*100000000000000^203 ≤ 43115164059997^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637420411 5000000000 43115164059997 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405218213/10000000000 : ℝ)^267 ≤ (8904448050413/20000000000000 : ℝ)^203 := by
    have hnat : (5405218213 : ℕ)^267*20000000000000^203 ≤ 8904448050413^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405218213 10000000000 8904448050413 20000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2040475191/10000000000 : ℝ)^267 ≤ (6181297836873/50000000000000 : ℝ)^203 := by
    have hnat : (2040475191 : ℕ)^267*50000000000000^203 ≤ 6181297836873^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040475191 10000000000 6181297836873 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637420411/5000000000 : ℝ), (5405218213/10000000000 : ℝ), (-2040475191/10000000000 : ℝ)] ![(43115164059997/100000000000000 : ℝ), (8904448050413/20000000000000 : ℝ), (6181297836873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637420411/5000000000 : ℝ)|^267 ≤ (43115164059997/100000000000000 : ℝ)^203
        have hw : |(2637420411/5000000000 : ℝ)|=(2637420411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405218213/10000000000 : ℝ)|^267 ≤ (8904448050413/20000000000000 : ℝ)^203
        have hw : |(5405218213/10000000000 : ℝ)|=(5405218213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2040475191/10000000000 : ℝ)|^267 ≤ (6181297836873/50000000000000 : ℝ)^203
        have hw : |(-2040475191/10000000000 : ℝ)|=(2040475191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_box_11 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2257946457/5000000000 : ℝ)*x 0 + (2123757893/5000000000 : ℝ)*x 1 + (2123757941/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2257946457/5000000000 : ℝ)^267 ≤ (4393436467247/12500000000000 : ℝ)^203 := by
    have hnat : (2257946457 : ℕ)^267*12500000000000^203 ≤ 4393436467247^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257946457 5000000000 4393436467247 12500000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123757893/5000000000 : ℝ)^267 ≤ (6485250728931/20000000000000 : ℝ)^203 := by
    have hnat : (2123757893 : ℕ)^267*20000000000000^203 ≤ 6485250728931^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123757893 5000000000 6485250728931 20000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123757941/5000000000 : ℝ)^267 ≤ (32426254608591/100000000000000 : ℝ)^203 := by
    have hnat : (2123757941 : ℕ)^267*100000000000000^203 ≤ 32426254608591^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123757941 5000000000 32426254608591 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2257946457/5000000000 : ℝ), (2123757893/5000000000 : ℝ), (2123757941/5000000000 : ℝ)] ![(4393436467247/12500000000000 : ℝ), (6485250728931/20000000000000 : ℝ), (32426254608591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2257946457/5000000000 : ℝ)|^267 ≤ (4393436467247/12500000000000 : ℝ)^203
        have hw : |(2257946457/5000000000 : ℝ)|=(2257946457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2123757893/5000000000 : ℝ)|^267 ≤ (6485250728931/20000000000000 : ℝ)^203
        have hw : |(2123757893/5000000000 : ℝ)|=(2123757893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123757941/5000000000 : ℝ)|^267 ≤ (32426254608591/100000000000000 : ℝ)^203
        have hw : |(2123757941/5000000000 : ℝ)|=(2123757941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_box_12 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-394531611/2000000000 : ℝ)*x 0 + (2738088753/5000000000 : ℝ)*x 1 + (2626587429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (394531611/2000000000 : ℝ)^267 ≤ (5912513412229/50000000000000 : ℝ)^203 := by
    have hnat : (394531611 : ℕ)^267*50000000000000^203 ≤ 5912513412229^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394531611 2000000000 5912513412229 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738088753/5000000000 : ℝ)^267 ≤ (22646290986813/50000000000000 : ℝ)^203 := by
    have hnat : (2738088753 : ℕ)^267*50000000000000^203 ≤ 22646290986813^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738088753 5000000000 22646290986813 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626587429/5000000000 : ℝ)^267 ≤ (10720597795633/25000000000000 : ℝ)^203 := by
    have hnat : (2626587429 : ℕ)^267*25000000000000^203 ≤ 10720597795633^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626587429 5000000000 10720597795633 25000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-394531611/2000000000 : ℝ), (2738088753/5000000000 : ℝ), (2626587429/5000000000 : ℝ)] ![(5912513412229/50000000000000 : ℝ), (22646290986813/50000000000000 : ℝ), (10720597795633/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-394531611/2000000000 : ℝ)|^267 ≤ (5912513412229/50000000000000 : ℝ)^203
        have hw : |(-394531611/2000000000 : ℝ)|=(394531611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738088753/5000000000 : ℝ)|^267 ≤ (22646290986813/50000000000000 : ℝ)^203
        have hw : |(2738088753/5000000000 : ℝ)|=(2738088753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626587429/5000000000 : ℝ)|^267 ≤ (10720597795633/25000000000000 : ℝ)^203
        have hw : |(2626587429/5000000000 : ℝ)|=(2626587429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_box_13 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1076354417/2000000000 : ℝ)*x 0 + (-1050627703/5000000000 : ℝ)*x 1 + (1313293797/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076354417/2000000000 : ℝ)^267 ≤ (44268404508101/100000000000000 : ℝ)^203 := by
    have hnat : (1076354417 : ℕ)^267*100000000000000^203 ≤ 44268404508101^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076354417 2000000000 44268404508101 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050627703/5000000000 : ℝ)^267 ≤ (3212300189999/25000000000000 : ℝ)^203 := by
    have hnat : (1050627703 : ℕ)^267*25000000000000^203 ≤ 3212300189999^203*5000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050627703 5000000000 3212300189999 25000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313293797/2500000000 : ℝ)^267 ≤ (5360299340707/12500000000000 : ℝ)^203 := by
    have hnat : (1313293797 : ℕ)^267*12500000000000^203 ≤ 5360299340707^203*2500000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313293797 2500000000 5360299340707 12500000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076354417/2000000000 : ℝ), (-1050627703/5000000000 : ℝ), (1313293797/2500000000 : ℝ)] ![(44268404508101/100000000000000 : ℝ), (3212300189999/25000000000000 : ℝ), (5360299340707/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076354417/2000000000 : ℝ)|^267 ≤ (44268404508101/100000000000000 : ℝ)^203
        have hw : |(1076354417/2000000000 : ℝ)|=(1076354417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1050627703/5000000000 : ℝ)|^267 ≤ (3212300189999/25000000000000 : ℝ)^203
        have hw : |(-1050627703/5000000000 : ℝ)|=(1050627703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313293797/2500000000 : ℝ)|^267 ≤ (5360299340707/12500000000000 : ℝ)^203
        have hw : |(1313293797/2500000000 : ℝ)|=(1313293797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_box_14 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5381772393/10000000000 : ℝ)*x 0 + (1050635001/2000000000 : ℝ)*x 1 + (-420251047/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381772393/10000000000 : ℝ)^267 ≤ (44268407840327/100000000000000 : ℝ)^203 := by
    have hnat : (5381772393 : ℕ)^267*100000000000000^203 ≤ 44268407840327^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381772393 10000000000 44268407840327 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050635001/2000000000 : ℝ)^267 ≤ (42882392760833/100000000000000 : ℝ)^203 := by
    have hnat : (1050635001 : ℕ)^267*100000000000000^203 ≤ 42882392760833^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050635001 2000000000 42882392760833 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420251047/2000000000 : ℝ)^267 ≤ (12849199384661/100000000000000 : ℝ)^203 := by
    have hnat : (420251047 : ℕ)^267*100000000000000^203 ≤ 12849199384661^203*2000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420251047 2000000000 12849199384661 100000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381772393/10000000000 : ℝ), (1050635001/2000000000 : ℝ), (-420251047/2000000000 : ℝ)] ![(44268407840327/100000000000000 : ℝ), (42882392760833/100000000000000 : ℝ), (12849199384661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381772393/10000000000 : ℝ)|^267 ≤ (44268407840327/100000000000000 : ℝ)^203
        have hw : |(5381772393/10000000000 : ℝ)|=(5381772393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1050635001/2000000000 : ℝ)|^267 ≤ (42882392760833/100000000000000 : ℝ)^203
        have hw : |(1050635001/2000000000 : ℝ)|=(1050635001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-420251047/2000000000 : ℝ)|^267 ≤ (12849199384661/100000000000000 : ℝ)^203
        have hw : |(-420251047/2000000000 : ℝ)|=(420251047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1312_box_15 (p : ℝ) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4158305983/10000000000 : ℝ)*x 0 + (4426303921/10000000000 : ℝ)*x 1 + (4426303203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4158305983/10000000000 : ℝ)^267 ≤ (15766738976147/50000000000000 : ℝ)^203 := by
    have hnat : (4158305983 : ℕ)^267*50000000000000^203 ≤ 15766738976147^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158305983 10000000000 15766738976147 50000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4426303921/10000000000 : ℝ)^267 ≤ (1069789520837/3125000000000 : ℝ)^203 := by
    have hnat : (4426303921 : ℕ)^267*3125000000000^203 ≤ 1069789520837^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4426303921 10000000000 1069789520837 3125000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4426303203/10000000000 : ℝ)^267 ≤ (1711662868151/5000000000000 : ℝ)^203 := by
    have hnat : (4426303203 : ℕ)^267*5000000000000^203 ≤ 1711662868151^203*10000000000^267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4426303203 10000000000 1711662868151 5000000000000 267 203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (267/64 : ℝ)) 267 203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4158305983/10000000000 : ℝ), (4426303921/10000000000 : ℝ), (4426303203/10000000000 : ℝ)] ![(15766738976147/50000000000000 : ℝ), (1069789520837/3125000000000 : ℝ), (1711662868151/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4158305983/10000000000 : ℝ)|^267 ≤ (15766738976147/50000000000000 : ℝ)^203
        have hw : |(4158305983/10000000000 : ℝ)|=(4158305983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4426303921/10000000000 : ℝ)|^267 ≤ (1069789520837/3125000000000 : ℝ)^203
        have hw : |(4426303921/10000000000 : ℝ)|=(4426303921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4426303203/10000000000 : ℝ)|^267 ≤ (1711662868151/5000000000000 : ℝ)^203
        have hw : |(4426303203/10000000000 : ℝ)|=(4426303203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1312_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153547737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5539/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12569/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58883/100000 : ℝ) ∧ (79777/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42117/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7343/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5539/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7343/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5539/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7343/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5539/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7343/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5539/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7343/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5539/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7343/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5539/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5539/50000 : ℝ) ^ (4271/1024 : ℝ) ≤ (5170295761411381/50000000000000000000 : ℝ) := by
    have hpowers : (5539/50000 : ℝ)^4271 ≤ (5170295761411381/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5539 : ℕ)^4271*50000000000000000000^1024 ≤ 5170295761411381^1024*50000^4271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5539 50000 5170295761411381 50000000000000000000 4271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5539/50000 : ℝ)) (X := (5170295761411381/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7343/50000 : ℝ) ^ (4271/1024 : ℝ) ≤ (16757499448240731/50000000000000000000 : ℝ) := by
    have hpowers : (7343/50000 : ℝ)^4271 ≤ (16757499448240731/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7343 : ℕ)^4271*50000000000000000000^1024 ≤ 16757499448240731^1024*50000^4271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7343 50000 16757499448240731 50000000000000000000 4271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7343/50000 : ℝ)) (X := (16757499448240731/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005170295761411381/25000000000000000000 : ℝ) ≤ (2500123951456317/2500000000000000 : ℝ) ^ (4271/1024 : ℝ) := by
    have hpowers : (25005170295761411381/25000000000000000000 : ℝ)^1024 ≤ (2500123951456317/2500000000000000 : ℝ)^4271 := by
      have hnat : (25005170295761411381 : ℕ)^1024*2500000000000000^4271 ≤ 2500123951456317^4271*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005170295761411381 25000000000000000000 2500123951456317 2500000000000000 1024 4271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500123951456317/2500000000000000 : ℝ)) (X := (25005170295761411381/25000000000000000000 : ℝ)) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126370487200603257/3125000000000000000 : ℝ) ≤ (5000525645517707/5000000000000000 : ℝ) ^ (4271/1024 : ℝ) := by
    have hpowers : (3126370487200603257/3125000000000000000 : ℝ)^1024 ≤ (5000525645517707/5000000000000000 : ℝ)^4271 := by
      have hnat : (3126370487200603257 : ℕ)^1024*5000000000000000^4271 ≤ 5000525645517707^4271*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126370487200603257 3125000000000000000 5000525645517707 5000000000000000 1024 4271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000525645517707/5000000000000000 : ℝ)) (X := (3126370487200603257/3125000000000000000 : ℝ)) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016757499448240731/25000000000000000000 : ℝ) ≤ (250040169406139/250000000000000 : ℝ) ^ (4271/1024 : ℝ) := by
    have hpowers : (25016757499448240731/25000000000000000000 : ℝ)^1024 ≤ (250040169406139/250000000000000 : ℝ)^4271 := by
      have hnat : (25016757499448240731 : ℕ)^1024*250000000000000^4271 ≤ 250040169406139^4271*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016757499448240731 25000000000000000000 250040169406139 250000000000000 1024 4271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250040169406139/250000000000000 : ℝ)) (X := (25016757499448240731/25000000000000000000 : ℝ)) (by norm_num) 4271 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5170295761411381/50000000000000000000 : ℝ) ≤ ((4508685192137696521/4510000000000000000 : ℝ)+2*(277742605073/180400000000000 : ℝ)*(5539/50000 : ℝ))^(4271/1024 : ℝ) := by
    rw [show (4508685192137696521/4510000000000000000 : ℝ)+2*(277742605073/180400000000000 : ℝ)*(5539/50000 : ℝ)=(2500123951456317/2500000000000000 : ℝ) by norm_num, show 1+2*(5170295761411381/50000000000000000000 : ℝ)=(25005170295761411381/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16757499448240731/50000000000000000000 : ℝ)+(5170295761411381/50000000000000000000 : ℝ) ≤ ((4508685192137696521/4510000000000000000 : ℝ)+(277742605073/180400000000000 : ℝ)*((7343/50000 : ℝ)+(5539/50000 : ℝ)))^(4271/1024 : ℝ) := by
    rw [show (4508685192137696521/4510000000000000000 : ℝ)+(277742605073/180400000000000 : ℝ)*((7343/50000 : ℝ)+(5539/50000 : ℝ))=(5000525645517707/5000000000000000 : ℝ) by norm_num, show 1+(16757499448240731/50000000000000000000 : ℝ)+(5170295761411381/50000000000000000000 : ℝ)=(3126370487200603257/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16757499448240731/50000000000000000000 : ℝ) ≤ ((4508685192137696521/4510000000000000000 : ℝ)+2*(277742605073/180400000000000 : ℝ)*(7343/50000 : ℝ))^(4271/1024 : ℝ) := by
    rw [show (4508685192137696521/4510000000000000000 : ℝ)+2*(277742605073/180400000000000 : ℝ)*(7343/50000 : ℝ)=(250040169406139/250000000000000 : ℝ) by norm_num, show 1+2*(16757499448240731/50000000000000000000 : ℝ)=(25016757499448240731/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4508685192137696521/4510000000000000000 : ℝ)*(X 1 0+X 2 0)+(277742605073/180400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4271/1024 : ℝ)) (lo := (5539/50000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (4508685192137696521/4510000000000000000 : ℝ)) (alpha := (277742605073/180400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4508685192137696521/4510000000000000000 : ℝ)*(X 0 1+X 2 1)+(277742605073/180400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4271/1024 : ℝ)) (lo := (5539/50000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (4508685192137696521/4510000000000000000 : ℝ)) (alpha := (277742605073/180400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4508685192137696521/4510000000000000000 : ℝ)*(X 0 2+X 1 2)+(277742605073/180400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4271/1024 : ℝ)) (lo := (5539/50000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (4508685192137696521/4510000000000000000 : ℝ)) (alpha := (277742605073/180400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-380100001/2000000000 : ℝ)*X 0 0+(134779673/250000000 : ℝ)*X 0 1+(5391187097/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5284713677/10000000000 : ℝ)*X 1 0+(-1023108223/5000000000 : ℝ)*X 1 1+(5391187557/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((264235711/500000000 : ℝ)*X 2 0+(5391187109/10000000000 : ℝ)*X 2 1+(-3197213/15625000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((896688557/2000000000 : ℝ)*X 0 0+(4264028401/10000000000 : ℝ)*X 0 1+(852805709/2000000000 : ℝ)*X 0 2+(896688557/2000000000 : ℝ)*X 1 0+(4264028401/10000000000 : ℝ)*X 1 1+(852805709/2000000000 : ℝ)*X 1 2+(896688557/2000000000 : ℝ)*X 2 0+(4264028401/10000000000 : ℝ)*X 2 1+(852805709/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-89704551/400000000 : ℝ)*X 0 0+(2632109197/5000000000 : ℝ)*X 0 1+(5264217253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5374008977/10000000000 : ℝ)*X 1 0+(-2096948953/10000000000 : ℝ)*X 1 1+(5264217201/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((67175131/125000000 : ℝ)*X 2 0+(32901353/62500000 : ℝ)*X 2 1+(-419389579/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2092366471/5000000000 : ℝ)*X 0 0+(4413327857/10000000000 : ℝ)*X 0 1+(441332967/1000000000 : ℝ)*X 0 2+(2092366471/5000000000 : ℝ)*X 1 0+(4413327857/10000000000 : ℝ)*X 1 1+(441332967/1000000000 : ℝ)*X 1 2+(2092366471/5000000000 : ℝ)*X 2 0+(4413327857/10000000000 : ℝ)*X 2 1+(441332967/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-542713359/2500000000 : ℝ)*X 0 0+(5176952393/10000000000 : ℝ)*X 0 1+(1081043637/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5274840191/10000000000 : ℝ)*X 1 0+(-2040475497/10000000000 : ℝ)*X 1 1+(2702609307/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2637420411/5000000000 : ℝ)*X 2 0+(5405218213/10000000000 : ℝ)*X 2 1+(-2040475191/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2257946457/5000000000 : ℝ)*X 0 0+(2123757893/5000000000 : ℝ)*X 0 1+(2123757941/5000000000 : ℝ)*X 0 2+(2257946457/5000000000 : ℝ)*X 1 0+(2123757893/5000000000 : ℝ)*X 1 1+(2123757941/5000000000 : ℝ)*X 1 2+(2257946457/5000000000 : ℝ)*X 2 0+(2123757893/5000000000 : ℝ)*X 2 1+(2123757941/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-394531611/2000000000 : ℝ)*X 0 0+(2738088753/5000000000 : ℝ)*X 0 1+(2626587429/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1076354417/2000000000 : ℝ)*X 1 0+(-1050627703/5000000000 : ℝ)*X 1 1+(1313293797/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5381772393/10000000000 : ℝ)*X 2 0+(1050635001/2000000000 : ℝ)*X 2 1+(-420251047/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4158305983/10000000000 : ℝ)*X 0 0+(4426303921/10000000000 : ℝ)*X 0 1+(4426303203/10000000000 : ℝ)*X 0 2+(4158305983/10000000000 : ℝ)*X 1 0+(4426303921/10000000000 : ℝ)*X 1 1+(4426303203/10000000000 : ℝ)*X 1 2+(4158305983/10000000000 : ℝ)*X 2 0+(4426303921/10000000000 : ℝ)*X 2 1+(4426303203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1312_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12569/20000 : ℝ) ≤ (-1288266908712909143944555751727/2050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (105019187/25000000000000 : ℝ)*(upper0) + (515040203/100000000000000 : ℝ)*(lower2) + (188298367/50000000000000 : ℝ)*(lower3) + (288684826197119/10000000000000 : ℝ)*(major0) + (288684826197119/10000000000000 : ℝ)*(major1) + (288684826197119/10000000000000 : ℝ)*(major2) + (5400213/2500000000000 : ℝ)*(sp1) + (8426430863/100000000000000 : ℝ)*(sp2) + (19498361/25000000000000 : ℝ)*(sp3) + (391452027903007/10000000000000 : ℝ)*(sp4) + (78290910453893/2000000000000 : ℝ)*(sp5) + (1957268656136153/50000000000000 : ℝ)*(sp6) + (940049068327859/50000000000000 : ℝ)*(sp7) + (25459673099/100000000000000 : ℝ)*(sp8) + (1880098214649161/100000000000000 : ℝ)*(f.failure) + (391454573870317/10000000000000 : ℝ)*(f.sum) + (343464492007/82000000000000000000000000 : ℝ)*base66 + (22166184973908909/4100000000000000000000000000000 : ℝ)*base67 + (22943986921108909/4100000000000000000000000000000 : ℝ)*base69 + (2515122245008909/4100000000000000000000000000000 : ℝ)*base71 + (3101533386483/82000000000000000000000000 : ℝ)*base74 + (18715117865391091/4100000000000000000000000000000 : ℝ)*base76 + (25973937880008909/4100000000000000000000000000000 : ℝ)*base77 + (64504799312091091/4100000000000000000000000000000 : ℝ)*base80 + (983335303/82000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (79501343/10000000000000000000000 : ℝ)*base90 + (79501343/10000000000000000000000 : ℝ)*base92 + (79501343/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (58883/100000 : ℝ) ≤ (33196855147738648624675049067339/56375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28222027/50000000000000 : ℝ)*(lower1) + (539509/2500000000000 : ℝ)*(lower3) + (13069953/10000000000000 : ℝ)*(upper4) + (47720011/100000000000000 : ℝ)*(upper5) + (738635580453553/25000000000000 : ℝ)*(major0) + (738635580453553/25000000000000 : ℝ)*(major1) + (738635580453553/25000000000000 : ℝ)*(major2) + (1982635591706657/50000000000000 : ℝ)*(sp0) + (1982629781737093/50000000000000 : ℝ)*(sp1) + (991317259831437/25000000000000 : ℝ)*(sp2) + (481045959711297/25000000000000 : ℝ)*(sp3) + (11619939127/100000000000000 : ℝ)*(sp5) + (428817513/20000000000000 : ℝ)*(sp6) + (128750489/12500000000000 : ℝ)*(sp7) + (1924184868849101/100000000000000 : ℝ)*(f.failure) + (1982635591706657/50000000000000 : ℝ)*(f.sum) + (9854454812299/2255000000000000000000000000 : ℝ)*base65 + (1461459499103585887/112750000000000000000000000000000 : ℝ)*base68 + (2041191849944914113/112750000000000000000000000000000 : ℝ)*base69 + (39434945024335887/112750000000000000000000000000000 : ℝ)*base72 + (3094870680903/1127500000000000000000000000 : ℝ)*base74 + (3019251007539664113/112750000000000000000000000000000 : ℝ)*base75 + (370156938601585887/112750000000000000000000000000000 : ℝ)*base78 + (504753295166585887/112750000000000000000000000000000 : ℝ)*base80 + (38294962620397/1127500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (53034437/10000000000000000000000 : ℝ)*base89 + (53034437/10000000000000000000000 : ℝ)*base91 + (53034437/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (79777/100000 : ℝ) ≤ (8177394620971911450400493574273/10250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16610301/20000000000000 : ℝ)*(lower1) + (99467551/100000000000000 : ℝ)*(lower3) + (228216453/100000000000000 : ℝ)*(upper4) + (1633922546925119/50000000000000 : ℝ)*(major0) + (1633922546925119/50000000000000 : ℝ)*(major1) + (1633922546925119/50000000000000 : ℝ)*(major2) + (3129509539/50000000000000 : ℝ)*(sp0) + (151904045669/100000000000000 : ℝ)*(sp1) + (12883840647/12500000000000 : ℝ)*(sp2) + (74981447497/100000000000000 : ℝ)*(sp3) + (136901978794659/3125000000000 : ℝ)*(sp8) + (2190358838201249/50000000000000 : ℝ)*(sp9) + (438076650972299/10000000000000 : ℝ)*(sp10) + (532038118141467/25000000000000 : ℝ)*(sp11) + (425645490802673/20000000000000 : ℝ)*(f.failure) + (2190434790224083/50000000000000 : ℝ)*(f.sum) + (2195607869473/410000000000000000000000000 : ℝ)*base66 + (80232979398316909/20500000000000000000000000000000 : ℝ)*base67 + (940993182739316909/20500000000000000000000000000000 : ℝ)*base69 + (152710747701183091/20500000000000000000000000000000 : ℝ)*base72 + (838181420867/410000000000000000000000000 : ℝ)*base73 + (129557333279816909/20500000000000000000000000000000 : ℝ)*base75 + (20342011315683091/20500000000000000000000000000000 : ℝ)*base78 + (67516712343316909/20500000000000000000000000000000 : ℝ)*base79 + (6571672059193/410000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (7298999/2000000000000000000000 : ℝ)*base90 + (7298999/2000000000000000000000 : ℝ)*base92 + (7298999/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-42117/50000 : ℝ) ≤ (-9497130387077059824430131175017/11275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (89430773/100000000000000 : ℝ)*(lower0) + (138114973/100000000000000 : ℝ)*(lower2) + (14233891/50000000000000 : ℝ)*(upper3) + (20047283/50000000000000 : ℝ)*(upper5) + (330396213494159/10000000000000 : ℝ)*(major0) + (330396213494159/10000000000000 : ℝ)*(major1) + (330396213494159/10000000000000 : ℝ)*(major2) + (838138267/10000000000000 : ℝ)*(sp0) + (8600953311/20000000000000 : ℝ)*(sp7) + (252507429/100000000000000 : ℝ)*(sp8) + (8758288538477/195312500000 : ℝ)*(sp12) + (2242126182795161/50000000000000 : ℝ)*(sp13) + (2242126182795161/50000000000000 : ℝ)*(sp14) + (537926537806243/25000000000000 : ℝ)*(sp15) + (2151749155991527/100000000000000 : ℝ)*(f.failure) + (2242126182795161/50000000000000 : ℝ)*(f.sum) + (2397550383337/902000000000000000000000000 : ℝ)*base66 + (434545545115504161/45100000000000000000000000000000 : ℝ)*base68 + (49488287006995839/45100000000000000000000000000000 : ℝ)*base69 + (159361901777695839/45100000000000000000000000000000 : ℝ)*base71 + (5322184849123/902000000000000000000000000 : ℝ)*base74 + (158100046803095839/45100000000000000000000000000000 : ℝ)*base75 + (222419856940095839/45100000000000000000000000000000 : ℝ)*base77 + (243495239152595839/45100000000000000000000000000000 : ℝ)*base79 + (266740530157/180400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (37975601/10000000000000000000000 : ℝ)*base90 + (37975601/10000000000000000000000 : ℝ)*base92 + (37975601/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1312_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153547737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5539/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12569/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58883/100000 : ℝ) else (79777/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42117/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1312_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1312_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153547737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7349/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5533/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12569/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58883/100000 : ℝ) else (79777/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42117/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1312_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1312_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1312_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4271/1024 : ℝ) ≤ p) (hpb : p ≤ (267/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153547737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7349/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5533/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12569/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58883/100000 : ℝ) else (79777/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42117/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1312_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

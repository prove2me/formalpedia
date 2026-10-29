-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1637_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:08:40.56131+00:00
-- url     : https://prove2.me/submissions/980bae96-d8c6-4de7-af69-188253d5d1da

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
theorem support_rectangle_w1637_s3_0 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-819279261/5000000000 : ℝ)*x 0 + (2725767017/5000000000 : ℝ)*x 1 + (5182885067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (819279261/5000000000 : ℝ)^4867 ≤ (10119258065547/100000000000000 : ℝ)^3843 := by
    have hnat : (819279261 : ℕ)^4867*100000000000000^3843 ≤ 10119258065547^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819279261 5000000000 10119258065547 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725767017/5000000000 : ℝ)^4867 ≤ (46377988037221/100000000000000 : ℝ)^3843 := by
    have hnat : (2725767017 : ℕ)^4867*100000000000000^3843 ≤ 46377988037221^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725767017 5000000000 46377988037221 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182885067/10000000000 : ℝ)^4867 ≤ (43502753887071/100000000000000 : ℝ)^3843 := by
    have hnat : (5182885067 : ℕ)^4867*100000000000000^3843 ≤ 43502753887071^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182885067 10000000000 43502753887071 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-819279261/5000000000 : ℝ), (2725767017/5000000000 : ℝ), (5182885067/10000000000 : ℝ)] ![(10119258065547/100000000000000 : ℝ), (46377988037221/100000000000000 : ℝ), (43502753887071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-819279261/5000000000 : ℝ)|^4867 ≤ (10119258065547/100000000000000 : ℝ)^3843
        have hw : |(-819279261/5000000000 : ℝ)|=(819279261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725767017/5000000000 : ℝ)|^4867 ≤ (46377988037221/100000000000000 : ℝ)^3843
        have hw : |(2725767017/5000000000 : ℝ)|=(2725767017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182885067/10000000000 : ℝ)|^4867 ≤ (43502753887071/100000000000000 : ℝ)^3843
        have hw : |(5182885067/10000000000 : ℝ)|=(5182885067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s3_1 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069944361/2000000000 : ℝ)*x 0 + (-1776933141/10000000000 : ℝ)*x 1 + (1036577029/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069944361/2000000000 : ℝ)^4867 ≤ (45283786930749/100000000000000 : ℝ)^3843 := by
    have hnat : (1069944361 : ℕ)^4867*100000000000000^3843 ≤ 45283786930749^3843*2000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069944361 2000000000 45283786930749 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1776933141/10000000000 : ℝ)^4867 ≤ (2803364584079/25000000000000 : ℝ)^3843 := by
    have hnat : (1776933141 : ℕ)^4867*25000000000000^3843 ≤ 2803364584079^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1776933141 10000000000 2803364584079 25000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036577029/2000000000 : ℝ)^4867 ≤ (5437844339527/12500000000000 : ℝ)^3843 := by
    have hnat : (1036577029 : ℕ)^4867*12500000000000^3843 ≤ 5437844339527^3843*2000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036577029 2000000000 5437844339527 12500000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069944361/2000000000 : ℝ), (-1776933141/10000000000 : ℝ), (1036577029/2000000000 : ℝ)] ![(45283786930749/100000000000000 : ℝ), (2803364584079/25000000000000 : ℝ), (5437844339527/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069944361/2000000000 : ℝ)|^4867 ≤ (45283786930749/100000000000000 : ℝ)^3843
        have hw : |(1069944361/2000000000 : ℝ)|=(1069944361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1776933141/10000000000 : ℝ)|^4867 ≤ (2803364584079/25000000000000 : ℝ)^3843
        have hw : |(-1776933141/10000000000 : ℝ)|=(1776933141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036577029/2000000000 : ℝ)|^4867 ≤ (5437844339527/12500000000000 : ℝ)^3843
        have hw : |(1036577029/2000000000 : ℝ)|=(1036577029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s3_2 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674860611/5000000000 : ℝ)*x 0 + (2591442883/5000000000 : ℝ)*x 1 + (-1776933097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674860611/5000000000 : ℝ)^4867 ≤ (22641890340439/50000000000000 : ℝ)^3843 := by
    have hnat : (2674860611 : ℕ)^4867*50000000000000^3843 ≤ 22641890340439^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674860611 5000000000 22641890340439 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591442883/5000000000 : ℝ)^4867 ≤ (4350276131749/10000000000000 : ℝ)^3843 := by
    have hnat : (2591442883 : ℕ)^4867*10000000000000^3843 ≤ 4350276131749^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591442883 5000000000 4350276131749 10000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1776933097/10000000000 : ℝ)^4867 ≤ (2242691596933/20000000000000 : ℝ)^3843 := by
    have hnat : (1776933097 : ℕ)^4867*20000000000000^3843 ≤ 2242691596933^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1776933097 10000000000 2242691596933 20000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674860611/5000000000 : ℝ), (2591442883/5000000000 : ℝ), (-1776933097/10000000000 : ℝ)] ![(22641890340439/50000000000000 : ℝ), (4350276131749/10000000000000 : ℝ), (2242691596933/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674860611/5000000000 : ℝ)|^4867 ≤ (22641890340439/50000000000000 : ℝ)^3843
        have hw : |(2674860611/5000000000 : ℝ)|=(2674860611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591442883/5000000000 : ℝ)|^4867 ≤ (4350276131749/10000000000000 : ℝ)^3843
        have hw : |(2591442883/5000000000 : ℝ)|=(2591442883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1776933097/10000000000 : ℝ)|^4867 ≤ (2242691596933/20000000000000 : ℝ)^3843
        have hw : |(-1776933097/10000000000 : ℝ)|=(1776933097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s3_3 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2095395479/5000000000 : ℝ)*x 0 + (771850801/2000000000 : ℝ)*x 1 + (454294437/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095395479/5000000000 : ℝ)^4867 ≤ (33239429251001/100000000000000 : ℝ)^3843 := by
    have hnat : (2095395479 : ℕ)^4867*100000000000000^3843 ≤ 33239429251001^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095395479 5000000000 33239429251001 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (771850801/2000000000 : ℝ)^4867 ≤ (29944955475917/100000000000000 : ℝ)^3843 := by
    have hnat : (771850801 : ℕ)^4867*100000000000000^3843 ≤ 29944955475917^3843*2000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771850801 2000000000 29944955475917 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (454294437/1000000000 : ℝ)^4867 ≤ (36815615256479/100000000000000 : ℝ)^3843 := by
    have hnat : (454294437 : ℕ)^4867*100000000000000^3843 ≤ 36815615256479^3843*1000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454294437 1000000000 36815615256479 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2095395479/5000000000 : ℝ), (771850801/2000000000 : ℝ), (454294437/1000000000 : ℝ)] ![(33239429251001/100000000000000 : ℝ), (29944955475917/100000000000000 : ℝ), (36815615256479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2095395479/5000000000 : ℝ)|^4867 ≤ (33239429251001/100000000000000 : ℝ)^3843
        have hw : |(2095395479/5000000000 : ℝ)|=(2095395479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(771850801/2000000000 : ℝ)|^4867 ≤ (29944955475917/100000000000000 : ℝ)^3843
        have hw : |(771850801/2000000000 : ℝ)|=(771850801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(454294437/1000000000 : ℝ)|^4867 ≤ (36815615256479/100000000000000 : ℝ)^3843
        have hw : |(454294437/1000000000 : ℝ)|=(454294437/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s3_4 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-51207039/312500000 : ℝ)*x 0 + (5184909079/10000000000 : ℝ)*x 1 + (5449488449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51207039/312500000 : ℝ)^4867 ≤ (5059889975459/50000000000000 : ℝ)^3843 := by
    have hnat : (51207039 : ℕ)^4867*50000000000000^3843 ≤ 5059889975459^3843*312500000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51207039 312500000 5059889975459 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184909079/10000000000 : ℝ)^4867 ≤ (10881067599021/25000000000000 : ℝ)^3843 := by
    have hnat : (5184909079 : ℕ)^4867*25000000000000^3843 ≤ 10881067599021^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184909079 10000000000 10881067599021 25000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5449488449/10000000000 : ℝ)^4867 ≤ (5794493705327/12500000000000 : ℝ)^3843 := by
    have hnat : (5449488449 : ℕ)^4867*12500000000000^3843 ≤ 5794493705327^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449488449 10000000000 5794493705327 12500000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51207039/312500000 : ℝ), (5184909079/10000000000 : ℝ), (5449488449/10000000000 : ℝ)] ![(5059889975459/50000000000000 : ℝ), (10881067599021/25000000000000 : ℝ), (5794493705327/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51207039/312500000 : ℝ)|^4867 ≤ (5059889975459/50000000000000 : ℝ)^3843
        have hw : |(-51207039/312500000 : ℝ)|=(51207039/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184909079/10000000000 : ℝ)|^4867 ≤ (10881067599021/25000000000000 : ℝ)^3843
        have hw : |(5184909079/10000000000 : ℝ)|=(5184909079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5449488449/10000000000 : ℝ)|^4867 ≤ (5794493705327/12500000000000 : ℝ)^3843
        have hw : |(5449488449/10000000000 : ℝ)|=(5449488449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s3_5 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278069823/10000000000 : ℝ)*x 0 + (-30206599/200000000 : ℝ)*x 1 + (1362372127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278069823/10000000000 : ℝ)^4867 ≤ (44517039203777/100000000000000 : ℝ)^3843 := by
    have hnat : (5278069823 : ℕ)^4867*100000000000000^3843 ≤ 44517039203777^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278069823 10000000000 44517039203777 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30206599/200000000 : ℝ)^4867 ≤ (9127010503689/100000000000000 : ℝ)^3843 := by
    have hnat : (30206599 : ℕ)^4867*100000000000000^3843 ≤ 9127010503689^3843*200000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30206599 200000000 9127010503689 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1362372127/2500000000 : ℝ)^4867 ≤ (46355950278229/100000000000000 : ℝ)^3843 := by
    have hnat : (1362372127 : ℕ)^4867*100000000000000^3843 ≤ 46355950278229^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362372127 2500000000 46355950278229 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278069823/10000000000 : ℝ), (-30206599/200000000 : ℝ), (1362372127/2500000000 : ℝ)] ![(44517039203777/100000000000000 : ℝ), (9127010503689/100000000000000 : ℝ), (46355950278229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278069823/10000000000 : ℝ)|^4867 ≤ (44517039203777/100000000000000 : ℝ)^3843
        have hw : |(5278069823/10000000000 : ℝ)|=(5278069823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30206599/200000000 : ℝ)|^4867 ≤ (9127010503689/100000000000000 : ℝ)^3843
        have hw : |(-30206599/200000000 : ℝ)|=(30206599/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1362372127/2500000000 : ℝ)|^4867 ≤ (46355950278229/100000000000000 : ℝ)^3843
        have hw : |(1362372127/2500000000 : ℝ)|=(1362372127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s3_6 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319517479/2500000000 : ℝ)*x 0 + (544948853/1000000000 : ℝ)*x 1 + (-1510329789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319517479/2500000000 : ℝ)^4867 ≤ (44517040197179/100000000000000 : ℝ)^3843 := by
    have hnat : (1319517479 : ℕ)^4867*100000000000000^3843 ≤ 44517040197179^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319517479 2500000000 44517040197179 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544948853/1000000000 : ℝ)^4867 ≤ (23177975257619/50000000000000 : ℝ)^3843 := by
    have hnat : (544948853 : ℕ)^4867*50000000000000^3843 ≤ 23177975257619^3843*1000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544948853 1000000000 23177975257619 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1510329789/10000000000 : ℝ)^4867 ≤ (9127009271511/100000000000000 : ℝ)^3843 := by
    have hnat : (1510329789 : ℕ)^4867*100000000000000^3843 ≤ 9127009271511^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510329789 10000000000 9127009271511 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319517479/2500000000 : ℝ), (544948853/1000000000 : ℝ), (-1510329789/10000000000 : ℝ)] ![(44517040197179/100000000000000 : ℝ), (23177975257619/50000000000000 : ℝ), (9127009271511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319517479/2500000000 : ℝ)|^4867 ≤ (44517040197179/100000000000000 : ℝ)^3843
        have hw : |(1319517479/2500000000 : ℝ)|=(1319517479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(544948853/1000000000 : ℝ)|^4867 ≤ (23177975257619/50000000000000 : ℝ)^3843
        have hw : |(544948853/1000000000 : ℝ)|=(544948853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1510329789/10000000000 : ℝ)|^4867 ≤ (9127009271511/100000000000000 : ℝ)^3843
        have hw : |(-1510329789/10000000000 : ℝ)|=(1510329789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s3_7 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (838192147/2000000000 : ℝ)*x 0 + (4537793773/10000000000 : ℝ)*x 1 + (3864458087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838192147/2000000000 : ℝ)^4867 ≤ (8310283666149/25000000000000 : ℝ)^3843 := by
    have hnat : (838192147 : ℕ)^4867*25000000000000^3843 ≤ 8310283666149^3843*2000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838192147 2000000000 8310283666149 25000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4537793773/10000000000 : ℝ)^4867 ≤ (36762761293871/100000000000000 : ℝ)^3843 := by
    have hnat : (4537793773 : ℕ)^4867*100000000000000^3843 ≤ 36762761293871^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4537793773 10000000000 36762761293871 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3864458087/10000000000 : ℝ)^4867 ≤ (2999610403359/10000000000000 : ℝ)^3843 := by
    have hnat : (3864458087 : ℕ)^4867*10000000000000^3843 ≤ 2999610403359^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3864458087 10000000000 2999610403359 10000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(838192147/2000000000 : ℝ), (4537793773/10000000000 : ℝ), (3864458087/10000000000 : ℝ)] ![(8310283666149/25000000000000 : ℝ), (36762761293871/100000000000000 : ℝ), (2999610403359/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(838192147/2000000000 : ℝ)|^4867 ≤ (8310283666149/25000000000000 : ℝ)^3843
        have hw : |(838192147/2000000000 : ℝ)|=(838192147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4537793773/10000000000 : ℝ)|^4867 ≤ (36762761293871/100000000000000 : ℝ)^3843
        have hw : |(4537793773/10000000000 : ℝ)|=(4537793773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3864458087/10000000000 : ℝ)|^4867 ≤ (2999610403359/10000000000000 : ℝ)^3843
        have hw : |(3864458087/10000000000 : ℝ)|=(3864458087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1637_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11077897/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1639/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10513/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5297/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16299/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1639/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10513/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1639/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10513/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1639/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10513/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1639/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10513/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1639/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10513/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1639/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10513/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10513/100000 : ℝ) ^ (4863/1024 : ℝ) ≤ (452050544491009/20000000000000000000 : ℝ) := by
    have hpowers : (10513/100000 : ℝ)^4863 ≤ (452050544491009/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10513 : ℕ)^4863*20000000000000000000^1024 ≤ 452050544491009^1024*100000^4863 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10513 100000 452050544491009 20000000000000000000 4863 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10513/100000 : ℝ)) (X := (452050544491009/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1639/10000 : ℝ) ^ (4863/1024 : ℝ) ≤ (18621602084755373/100000000000000000000 : ℝ) := by
    have hpowers : (1639/10000 : ℝ)^4863 ≤ (18621602084755373/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1639 : ℕ)^4863*100000000000000000000^1024 ≤ 18621602084755373^1024*10000^4863 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1639 10000 18621602084755373 100000000000000000000 4863 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1639/10000 : ℝ)) (X := (18621602084755373/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000452050544491009/10000000000000000000 : ℝ) ≤ (10000095186407199/10000000000000000 : ℝ) ^ (4863/1024 : ℝ) := by
    have hpowers : (10000452050544491009/10000000000000000000 : ℝ)^1024 ≤ (10000095186407199/10000000000000000 : ℝ)^4863 := by
      have hnat : (10000452050544491009 : ℕ)^1024*10000000000000000^4863 ≤ 10000095186407199^4863*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000452050544491009 10000000000000000000 10000095186407199 10000000000000000 1024 4863 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000095186407199/10000000000000000 : ℝ)) (X := (10000452050544491009/10000000000000000000 : ℝ)) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50010440927403605209/50000000000000000000 : ℝ) ≤ (10000439672158569/10000000000000000 : ℝ) ^ (4863/1024 : ℝ) := by
    have hpowers : (50010440927403605209/50000000000000000000 : ℝ)^1024 ≤ (10000439672158569/10000000000000000 : ℝ)^4863 := by
      have hnat : (50010440927403605209 : ℕ)^1024*10000000000000000^4863 ≤ 10000439672158569^4863*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010440927403605209 50000000000000000000 10000439672158569 10000000000000000 1024 4863 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000439672158569/10000000000000000 : ℝ)) (X := (50010440927403605209/50000000000000000000 : ℝ)) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018621602084755373/50000000000000000000 : ℝ) ≤ (10000784157909939/10000000000000000 : ℝ) ^ (4863/1024 : ℝ) := by
    have hpowers : (50018621602084755373/50000000000000000000 : ℝ)^1024 ≤ (10000784157909939/10000000000000000 : ℝ)^4863 := by
      have hnat : (50018621602084755373 : ℕ)^1024*10000000000000000^4863 ≤ 10000784157909939^4863*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018621602084755373 50000000000000000000 10000784157909939 10000000000000000 1024 4863 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000784157909939/10000000000000000 : ℝ)) (X := (50018621602084755373/50000000000000000000 : ℝ)) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(452050544491009/20000000000000000000 : ℝ) ≤ ((19587772084368934301/19590000000000000000 : ℝ)+2*(11482858379/19590000000000 : ℝ)*(10513/100000 : ℝ))^(4863/1024 : ℝ) := by
    rw [show (19587772084368934301/19590000000000000000 : ℝ)+2*(11482858379/19590000000000 : ℝ)*(10513/100000 : ℝ)=(10000095186407199/10000000000000000 : ℝ) by norm_num, show 1+2*(452050544491009/20000000000000000000 : ℝ)=(10000452050544491009/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18621602084755373/100000000000000000000 : ℝ)+(452050544491009/20000000000000000000 : ℝ) ≤ ((19587772084368934301/19590000000000000000 : ℝ)+(11482858379/19590000000000 : ℝ)*((1639/10000 : ℝ)+(10513/100000 : ℝ)))^(4863/1024 : ℝ) := by
    rw [show (19587772084368934301/19590000000000000000 : ℝ)+(11482858379/19590000000000 : ℝ)*((1639/10000 : ℝ)+(10513/100000 : ℝ))=(10000439672158569/10000000000000000 : ℝ) by norm_num, show 1+(18621602084755373/100000000000000000000 : ℝ)+(452050544491009/20000000000000000000 : ℝ)=(50010440927403605209/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18621602084755373/100000000000000000000 : ℝ) ≤ ((19587772084368934301/19590000000000000000 : ℝ)+2*(11482858379/19590000000000 : ℝ)*(1639/10000 : ℝ))^(4863/1024 : ℝ) := by
    rw [show (19587772084368934301/19590000000000000000 : ℝ)+2*(11482858379/19590000000000 : ℝ)*(1639/10000 : ℝ)=(10000784157909939/10000000000000000 : ℝ) by norm_num, show 1+2*(18621602084755373/100000000000000000000 : ℝ)=(50018621602084755373/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19587772084368934301/19590000000000000000 : ℝ)*(X 1 0+X 2 0)+(11482858379/19590000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4863/1024 : ℝ)) (lo := (10513/100000 : ℝ)) (hi := (1639/10000 : ℝ)) (c := (19587772084368934301/19590000000000000000 : ℝ)) (alpha := (11482858379/19590000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19587772084368934301/19590000000000000000 : ℝ)*(X 0 1+X 2 1)+(11482858379/19590000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4863/1024 : ℝ)) (lo := (10513/100000 : ℝ)) (hi := (1639/10000 : ℝ)) (c := (19587772084368934301/19590000000000000000 : ℝ)) (alpha := (11482858379/19590000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19587772084368934301/19590000000000000000 : ℝ)*(X 0 2+X 1 2)+(11482858379/19590000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4863/1024 : ℝ)) (lo := (10513/100000 : ℝ)) (hi := (1639/10000 : ℝ)) (c := (19587772084368934301/19590000000000000000 : ℝ)) (alpha := (11482858379/19590000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-819279261/5000000000 : ℝ)*X 0 0+(2725767017/5000000000 : ℝ)*X 0 1+(5182885067/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069944361/2000000000 : ℝ)*X 1 0+(-1776933141/10000000000 : ℝ)*X 1 1+(1036577029/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674860611/5000000000 : ℝ)*X 2 0+(2591442883/5000000000 : ℝ)*X 2 1+(-1776933097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2095395479/5000000000 : ℝ)*X 0 0+(771850801/2000000000 : ℝ)*X 0 1+(454294437/1000000000 : ℝ)*X 0 2+(2095395479/5000000000 : ℝ)*X 1 0+(771850801/2000000000 : ℝ)*X 1 1+(454294437/1000000000 : ℝ)*X 1 2+(2095395479/5000000000 : ℝ)*X 2 0+(771850801/2000000000 : ℝ)*X 2 1+(454294437/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-51207039/312500000 : ℝ)*X 0 0+(5184909079/10000000000 : ℝ)*X 0 1+(5449488449/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278069823/10000000000 : ℝ)*X 1 0+(-30206599/200000000 : ℝ)*X 1 1+(1362372127/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319517479/2500000000 : ℝ)*X 2 0+(544948853/1000000000 : ℝ)*X 2 1+(-1510329789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((838192147/2000000000 : ℝ)*X 0 0+(4537793773/10000000000 : ℝ)*X 0 1+(3864458087/10000000000 : ℝ)*X 0 2+(838192147/2000000000 : ℝ)*X 1 0+(4537793773/10000000000 : ℝ)*X 1 1+(3864458087/10000000000 : ℝ)*X 1 2+(838192147/2000000000 : ℝ)*X 2 0+(4537793773/10000000000 : ℝ)*X 2 1+(3864458087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1311934157601124360782281567/163250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25013807/3125000000000 : ℝ)*(base19) + (289727503/100000000000000 : ℝ)*(base23) + (2450371/4000000000000 : ℝ)*(lower2) + (49827781/50000000000000 : ℝ)*(upper3) + (315917/6250000000000 : ℝ)*(lower4) + (1296253476186533/50000000000000 : ℝ)*(major0) + (1296253476186533/50000000000000 : ℝ)*(major1) + (1296253476186533/50000000000000 : ℝ)*(major2) + (1861172192160571/50000000000000 : ℝ)*(sp0) + (744471079542859/20000000000000 : ℝ)*(sp1) + (465294488553577/12500000000000 : ℝ)*(sp2) + (365663429154729/25000000000000 : ℝ)*(sp3) + (5906917489/50000000000000 : ℝ)*(sp4) + (232630797/6250000000000 : ℝ)*(sp7) + (1462657438711667/100000000000000 : ℝ)*(f.failure) + (3722356198156119/100000000000000 : ℝ)*(f.sum) + (1131641669899/244875000000000000000000000 : ℝ)*base66 + (3985140403992031567/979500000000000000000000000000000 : ℝ)*base68 + (2210059952294968433/979500000000000000000000000000000 : ℝ)*base69 + (7208240070526468433/979500000000000000000000000000000 : ℝ)*base71 + (10329194029451/1959000000000000000000000000 : ℝ)*base74 + (2501664802144468433/979500000000000000000000000000000 : ℝ)*base75 + (7058751687795031567/979500000000000000000000000000000 : ℝ)*base78 + (9282414569210968433/979500000000000000000000000000000 : ℝ)*base79 + (11798461243/19590000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2775701/625000000000000000000 : ℝ)*base90 + (2775701/625000000000000000000 : ℝ)*base92 + (2775701/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (398288939818512331294082099/163250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (72297373/25000000000000 : ℝ)*(base19) + (472366907/100000000000000 : ℝ)*(base23) + (3537763/4000000000000 : ℝ)*(upper3) + (246321/800000000000 : ℝ)*(lower4) + (6615411/25000000000000 : ℝ)*(upper5) + (1316181658667867/50000000000000 : ℝ)*(major0) + (1316181658667867/50000000000000 : ℝ)*(major1) + (1316181658667867/50000000000000 : ℝ)*(major2) + (491002607/20000000000000 : ℝ)*(sp1) + (1349109659/20000000000000 : ℝ)*(sp2) + (1889791345676409/50000000000000 : ℝ)*(sp4) + (944894986787573/25000000000000 : ℝ)*(sp5) + (236223467089851/6250000000000 : ℝ)*(sp6) + (371285965498423/25000000000000 : ℝ)*(sp7) + (371285965498423/25000000000000 : ℝ)*(f.failure) + (1889791345676409/50000000000000 : ℝ)*(f.sum) + (454882855421/244875000000000000000000000 : ℝ)*base65 + (6198084395724805967/979500000000000000000000000000000 : ℝ)*base67 + (12148378472658805967/979500000000000000000000000000000 : ℝ)*base69 + (7078718001971305967/979500000000000000000000000000000 : ℝ)*base71 + (10361139926807/1959000000000000000000000000 : ℝ)*base74 + (2734296101303305967/979500000000000000000000000000000 : ℝ)*base75 + (7127487057198805967/979500000000000000000000000000000 : ℝ)*base77 + (6939390733698805967/979500000000000000000000000000000 : ℝ)*base79 + (4857384907537/1959000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (718569/156250000000000000000 : ℝ)*base90 + (718569/156250000000000000000 : ℝ)*base92 + (718569/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1637_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11077897/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1639/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10513/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16299/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1637_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1637_s4_0 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-819310777/5000000000 : ℝ)*x 0 + (5451220773/10000000000 : ℝ)*x 1 + (5183156193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (819310777/5000000000 : ℝ)^4867 ≤ (79060555147/781250000000 : ℝ)^3843 := by
    have hnat : (819310777 : ℕ)^4867*781250000000^3843 ≤ 79060555147^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819310777 5000000000 79060555147 781250000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5451220773/10000000000 : ℝ)^4867 ≤ (11593653233337/25000000000000 : ℝ)^3843 := by
    have hnat : (5451220773 : ℕ)^4867*25000000000000^3843 ≤ 11593653233337^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451220773 10000000000 11593653233337 25000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183156193/10000000000 : ℝ)^4867 ≤ (21752817997789/50000000000000 : ℝ)^3843 := by
    have hnat : (5183156193 : ℕ)^4867*50000000000000^3843 ≤ 21752817997789^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183156193 10000000000 21752817997789 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-819310777/5000000000 : ℝ), (5451220773/10000000000 : ℝ), (5183156193/10000000000 : ℝ)] ![(79060555147/781250000000 : ℝ), (11593653233337/25000000000000 : ℝ), (21752817997789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-819310777/5000000000 : ℝ)|^4867 ≤ (79060555147/781250000000 : ℝ)^3843
        have hw : |(-819310777/5000000000 : ℝ)|=(819310777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5451220773/10000000000 : ℝ)|^4867 ≤ (11593653233337/25000000000000 : ℝ)^3843
        have hw : |(5451220773/10000000000 : ℝ)|=(5451220773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183156193/10000000000 : ℝ)|^4867 ≤ (21752817997789/50000000000000 : ℝ)^3843
        have hw : |(5183156193/10000000000 : ℝ)|=(5183156193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s4_1 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349637029/10000000000 : ℝ)*x 0 + (-1110429/6250000 : ℝ)*x 1 + (323947259/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349637029/10000000000 : ℝ)^4867 ≤ (45282878117801/100000000000000 : ℝ)^3843 := by
    have hnat : (5349637029 : ℕ)^4867*100000000000000^3843 ≤ 45282878117801^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349637029 10000000000 45282878117801 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1110429/6250000 : ℝ)^4867 ≤ (11211486400687/100000000000000 : ℝ)^3843 := by
    have hnat : (1110429 : ℕ)^4867*100000000000000^3843 ≤ 11211486400687^3843*6250000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110429 6250000 11211486400687 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323947259/625000000 : ℝ)^4867 ≤ (43505635474697/100000000000000 : ℝ)^3843 := by
    have hnat : (323947259 : ℕ)^4867*100000000000000^3843 ≤ 43505635474697^3843*625000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323947259 625000000 43505635474697 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349637029/10000000000 : ℝ), (-1110429/6250000 : ℝ), (323947259/625000000 : ℝ)] ![(45282878117801/100000000000000 : ℝ), (11211486400687/100000000000000 : ℝ), (43505635474697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349637029/10000000000 : ℝ)|^4867 ≤ (45282878117801/100000000000000 : ℝ)^3843
        have hw : |(5349637029/10000000000 : ℝ)|=(5349637029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1110429/6250000 : ℝ)|^4867 ≤ (11211486400687/100000000000000 : ℝ)^3843
        have hw : |(-1110429/6250000 : ℝ)|=(1110429/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323947259/625000000 : ℝ)|^4867 ≤ (43505635474697/100000000000000 : ℝ)^3843
        have hw : |(323947259/625000000 : ℝ)|=(323947259/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s4_2 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668704623/1250000000 : ℝ)*x 0 + (5183156191/10000000000 : ℝ)*x 1 + (-1776686397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668704623/1250000000 : ℝ)^4867 ≤ (9056575527079/20000000000000 : ℝ)^3843 := by
    have hnat : (668704623 : ℕ)^4867*20000000000000^3843 ≤ 9056575527079^3843*1250000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668704623 1250000000 9056575527079 20000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183156191/10000000000 : ℝ)^4867 ≤ (21752817987159/50000000000000 : ℝ)^3843 := by
    have hnat : (5183156191 : ℕ)^4867*50000000000000^3843 ≤ 21752817987159^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183156191 10000000000 21752817987159 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1776686397/10000000000 : ℝ)^4867 ≤ (11211486376711/100000000000000 : ℝ)^3843 := by
    have hnat : (1776686397 : ℕ)^4867*100000000000000^3843 ≤ 11211486376711^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1776686397 10000000000 11211486376711 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668704623/1250000000 : ℝ), (5183156191/10000000000 : ℝ), (-1776686397/10000000000 : ℝ)] ![(9056575527079/20000000000000 : ℝ), (21752817987159/50000000000000 : ℝ), (11211486376711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668704623/1250000000 : ℝ)|^4867 ≤ (9056575527079/20000000000000 : ℝ)^3843
        have hw : |(668704623/1250000000 : ℝ)|=(668704623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183156191/10000000000 : ℝ)|^4867 ≤ (21752817987159/50000000000000 : ℝ)^3843
        have hw : |(5183156191/10000000000 : ℝ)|=(5183156191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1776686397/10000000000 : ℝ)|^4867 ≤ (11211486376711/100000000000000 : ℝ)^3843
        have hw : |(-1776686397/10000000000 : ℝ)|=(1776686397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s4_3 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4190832213/10000000000 : ℝ)*x 0 + (3859992177/10000000000 : ℝ)*x 1 + (227109859/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4190832213/10000000000 : ℝ)^4867 ≤ (6647968731333/20000000000000 : ℝ)^3843 := by
    have hnat : (4190832213 : ℕ)^4867*20000000000000^3843 ≤ 6647968731333^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4190832213 10000000000 6647968731333 20000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3859992177/10000000000 : ℝ)^4867 ≤ (14976104757609/50000000000000 : ℝ)^3843 := by
    have hnat : (3859992177 : ℕ)^4867*50000000000000^3843 ≤ 14976104757609^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3859992177 10000000000 14976104757609 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (227109859/500000000 : ℝ)^4867 ≤ (7361589362887/20000000000000 : ℝ)^3843 := by
    have hnat : (227109859 : ℕ)^4867*20000000000000^3843 ≤ 7361589362887^3843*500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227109859 500000000 7361589362887 20000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4190832213/10000000000 : ℝ), (3859992177/10000000000 : ℝ), (227109859/500000000 : ℝ)] ![(6647968731333/20000000000000 : ℝ), (14976104757609/50000000000000 : ℝ), (7361589362887/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4190832213/10000000000 : ℝ)|^4867 ≤ (6647968731333/20000000000000 : ℝ)^3843
        have hw : |(4190832213/10000000000 : ℝ)|=(4190832213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3859992177/10000000000 : ℝ)|^4867 ≤ (14976104757609/50000000000000 : ℝ)^3843
        have hw : |(3859992177/10000000000 : ℝ)|=(3859992177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(227109859/500000000 : ℝ)|^4867 ≤ (7361589362887/20000000000000 : ℝ)^3843
        have hw : |(227109859/500000000 : ℝ)|=(227109859/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s4_4 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-819343761/5000000000 : ℝ)*x 0 + (2592585579/5000000000 : ℝ)*x 1 + (5449184607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (819343761/5000000000 : ℝ)^4867 ≤ (2530066755221/25000000000000 : ℝ)^3843 := by
    have hnat : (819343761 : ℕ)^4867*25000000000000^3843 ≤ 2530066755221^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819343761 5000000000 2530066755221 25000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592585579/5000000000 : ℝ)^4867 ≤ (348216452983/800000000000 : ℝ)^3843 := by
    have hnat : (2592585579 : ℕ)^4867*800000000000^3843 ≤ 348216452983^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592585579 5000000000 348216452983 800000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5449184607/10000000000 : ℝ)^4867 ≤ (11588169086639/25000000000000 : ℝ)^3843 := by
    have hnat : (5449184607 : ℕ)^4867*25000000000000^3843 ≤ 11588169086639^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449184607 10000000000 11588169086639 25000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-819343761/5000000000 : ℝ), (2592585579/5000000000 : ℝ), (5449184607/10000000000 : ℝ)] ![(2530066755221/25000000000000 : ℝ), (348216452983/800000000000 : ℝ), (11588169086639/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-819343761/5000000000 : ℝ)|^4867 ≤ (2530066755221/25000000000000 : ℝ)^3843
        have hw : |(-819343761/5000000000 : ℝ)|=(819343761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592585579/5000000000 : ℝ)|^4867 ≤ (348216452983/800000000000 : ℝ)^3843
        have hw : |(2592585579/5000000000 : ℝ)|=(2592585579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5449184607/10000000000 : ℝ)|^4867 ≤ (11588169086639/25000000000000 : ℝ)^3843
        have hw : |(5449184607/10000000000 : ℝ)|=(5449184607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s4_5 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527814131/1000000000 : ℝ)*x 0 + (-377664487/2500000000 : ℝ)*x 1 + (2724592303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527814131/1000000000 : ℝ)^4867 ≤ (22258901405439/50000000000000 : ℝ)^3843 := by
    have hnat : (527814131 : ℕ)^4867*50000000000000^3843 ≤ 22258901405439^3843*1000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527814131 1000000000 22258901405439 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (377664487/2500000000 : ℝ)^4867 ≤ (4564760418641/50000000000000 : ℝ)^3843 := by
    have hnat : (377664487 : ℕ)^4867*50000000000000^3843 ≤ 4564760418641^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377664487 2500000000 4564760418641 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2724592303/5000000000 : ℝ)^4867 ≤ (46352676335783/100000000000000 : ℝ)^3843 := by
    have hnat : (2724592303 : ℕ)^4867*100000000000000^3843 ≤ 46352676335783^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724592303 5000000000 46352676335783 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527814131/1000000000 : ℝ), (-377664487/2500000000 : ℝ), (2724592303/5000000000 : ℝ)] ![(22258901405439/50000000000000 : ℝ), (4564760418641/50000000000000 : ℝ), (46352676335783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527814131/1000000000 : ℝ)|^4867 ≤ (22258901405439/50000000000000 : ℝ)^3843
        have hw : |(527814131/1000000000 : ℝ)|=(527814131/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-377664487/2500000000 : ℝ)|^4867 ≤ (4564760418641/50000000000000 : ℝ)^3843
        have hw : |(-377664487/2500000000 : ℝ)|=(377664487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2724592303/5000000000 : ℝ)|^4867 ≤ (46352676335783/100000000000000 : ℝ)^3843
        have hw : |(2724592303/5000000000 : ℝ)|=(2724592303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s4_6 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278141309/10000000000 : ℝ)*x 0 + (2724592303/5000000000 : ℝ)*x 1 + (-1510657949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278141309/10000000000 : ℝ)^4867 ≤ (11129450700049/25000000000000 : ℝ)^3843 := by
    have hnat : (5278141309 : ℕ)^4867*25000000000000^3843 ≤ 11129450700049^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278141309 10000000000 11129450700049 25000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2724592303/5000000000 : ℝ)^4867 ≤ (46352676335783/100000000000000 : ℝ)^3843 := by
    have hnat : (2724592303 : ℕ)^4867*100000000000000^3843 ≤ 46352676335783^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724592303 5000000000 46352676335783 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1510657949/10000000000 : ℝ)^4867 ≤ (1141190105617/12500000000000 : ℝ)^3843 := by
    have hnat : (1510657949 : ℕ)^4867*12500000000000^3843 ≤ 1141190105617^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510657949 10000000000 1141190105617 12500000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278141309/10000000000 : ℝ), (2724592303/5000000000 : ℝ), (-1510657949/10000000000 : ℝ)] ![(11129450700049/25000000000000 : ℝ), (46352676335783/100000000000000 : ℝ), (1141190105617/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278141309/10000000000 : ℝ)|^4867 ≤ (11129450700049/25000000000000 : ℝ)^3843
        have hw : |(5278141309/10000000000 : ℝ)|=(5278141309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2724592303/5000000000 : ℝ)|^4867 ≤ (46352676335783/100000000000000 : ℝ)^3843
        have hw : |(2724592303/5000000000 : ℝ)|=(2724592303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1510657949/10000000000 : ℝ)|^4867 ≤ (1141190105617/12500000000000 : ℝ)^3843
        have hw : |(-1510657949/10000000000 : ℝ)|=(1510657949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_s4_7 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (419100009/1000000000 : ℝ)*x 0 + (4537069133/10000000000 : ℝ)*x 1 + (966293541/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419100009/1000000000 : ℝ)^4867 ≤ (33241529989041/100000000000000 : ℝ)^3843 := by
    have hnat : (419100009 : ℕ)^4867*100000000000000^3843 ≤ 33241529989041^3843*1000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419100009 1000000000 33241529989041 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4537069133/10000000000 : ℝ)^4867 ≤ (36755326526327/100000000000000 : ℝ)^3843 := by
    have hnat : (4537069133 : ℕ)^4867*100000000000000^3843 ≤ 36755326526327^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4537069133 10000000000 36755326526327 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (966293541/2500000000 : ℝ)^4867 ≤ (15001571733111/50000000000000 : ℝ)^3843 := by
    have hnat : (966293541 : ℕ)^4867*50000000000000^3843 ≤ 15001571733111^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966293541 2500000000 15001571733111 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419100009/1000000000 : ℝ), (4537069133/10000000000 : ℝ), (966293541/2500000000 : ℝ)] ![(33241529989041/100000000000000 : ℝ), (36755326526327/100000000000000 : ℝ), (15001571733111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419100009/1000000000 : ℝ)|^4867 ≤ (33241529989041/100000000000000 : ℝ)^3843
        have hw : |(419100009/1000000000 : ℝ)|=(419100009/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4537069133/10000000000 : ℝ)|^4867 ≤ (36755326526327/100000000000000 : ℝ)^3843
        have hw : |(4537069133/10000000000 : ℝ)|=(4537069133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(966293541/2500000000 : ℝ)|^4867 ≤ (15001571733111/50000000000000 : ℝ)^3843
        have hw : |(966293541/2500000000 : ℝ)|=(966293541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1637_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11077897/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16299/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (53/500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16293/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16299/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5297/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16299/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5297/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16299/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5297/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16299/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5297/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16299/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5297/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16299/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5297/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5297/50000 : ℝ) ^ (4863/1024 : ℝ) ≤ (2344158325189787/100000000000000000000 : ℝ) := by
    have hpowers : (5297/50000 : ℝ)^4863 ≤ (2344158325189787/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5297 : ℕ)^4863*100000000000000000000^1024 ≤ 2344158325189787^1024*50000^4863 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5297 50000 2344158325189787 100000000000000000000 4863 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5297/50000 : ℝ)) (X := (2344158325189787/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16299/100000 : ℝ) ^ (4863/1024 : ℝ) ≤ (18135683705431543/100000000000000000000 : ℝ) := by
    have hpowers : (16299/100000 : ℝ)^4863 ≤ (18135683705431543/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16299 : ℕ)^4863*100000000000000000000^1024 ≤ 18135683705431543^1024*100000^4863 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16299 100000 18135683705431543 100000000000000000000 4863 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16299/100000 : ℝ)) (X := (18135683705431543/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002344158325189787/50000000000000000000 : ℝ) ≤ (400003948794909/400000000000000 : ℝ) ^ (4863/1024 : ℝ) := by
    have hpowers : (50002344158325189787/50000000000000000000 : ℝ)^1024 ≤ (400003948794909/400000000000000 : ℝ)^4863 := by
      have hnat : (50002344158325189787 : ℕ)^1024*400000000000000^4863 ≤ 400003948794909^4863*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002344158325189787 50000000000000000000 400003948794909 400000000000000 1024 4863 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400003948794909/400000000000000 : ℝ)) (X := (50002344158325189787/50000000000000000000 : ℝ)) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10002047984203062133/10000000000000000000 : ℝ) ≤ (5000215604186549/5000000000000000 : ℝ) ^ (4863/1024 : ℝ) := by
    have hpowers : (10002047984203062133/10000000000000000000 : ℝ)^1024 ≤ (5000215604186549/5000000000000000 : ℝ)^4863 := by
      have hnat : (10002047984203062133 : ℕ)^1024*5000000000000000^4863 ≤ 5000215604186549^4863*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002047984203062133 10000000000000000000 5000215604186549 5000000000000000 1024 4863 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000215604186549/5000000000000000 : ℝ)) (X := (10002047984203062133/10000000000000000000 : ℝ)) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018135683705431543/50000000000000000000 : ℝ) ≤ (10000763696873471/10000000000000000 : ℝ) ^ (4863/1024 : ℝ) := by
    have hpowers : (50018135683705431543/50000000000000000000 : ℝ)^1024 ≤ (10000763696873471/10000000000000000 : ℝ)^4863 := by
      have hnat : (50018135683705431543 : ℕ)^1024*10000000000000000^4863 ≤ 10000763696873471^4863*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018135683705431543 50000000000000000000 10000763696873471 10000000000000000 1024 4863 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000763696873471/10000000000000000 : ℝ)) (X := (50018135683705431543/50000000000000000000 : ℝ)) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2344158325189787/100000000000000000000 : ℝ) ≤ ((57043518430527993001/57050000000000000000 : ℝ)+2*(332488500373/570500000000000 : ℝ)*(5297/50000 : ℝ))^(4863/1024 : ℝ) := by
    rw [show (57043518430527993001/57050000000000000000 : ℝ)+2*(332488500373/570500000000000 : ℝ)*(5297/50000 : ℝ)=(400003948794909/400000000000000 : ℝ) by norm_num, show 1+2*(2344158325189787/100000000000000000000 : ℝ)=(50002344158325189787/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18135683705431543/100000000000000000000 : ℝ)+(2344158325189787/100000000000000000000 : ℝ) ≤ ((57043518430527993001/57050000000000000000 : ℝ)+(332488500373/570500000000000 : ℝ)*((16299/100000 : ℝ)+(5297/50000 : ℝ)))^(4863/1024 : ℝ) := by
    rw [show (57043518430527993001/57050000000000000000 : ℝ)+(332488500373/570500000000000 : ℝ)*((16299/100000 : ℝ)+(5297/50000 : ℝ))=(5000215604186549/5000000000000000 : ℝ) by norm_num, show 1+(18135683705431543/100000000000000000000 : ℝ)+(2344158325189787/100000000000000000000 : ℝ)=(10002047984203062133/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18135683705431543/100000000000000000000 : ℝ) ≤ ((57043518430527993001/57050000000000000000 : ℝ)+2*(332488500373/570500000000000 : ℝ)*(16299/100000 : ℝ))^(4863/1024 : ℝ) := by
    rw [show (57043518430527993001/57050000000000000000 : ℝ)+2*(332488500373/570500000000000 : ℝ)*(16299/100000 : ℝ)=(10000763696873471/10000000000000000 : ℝ) by norm_num, show 1+2*(18135683705431543/100000000000000000000 : ℝ)=(50018135683705431543/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (57043518430527993001/57050000000000000000 : ℝ)*(X 1 0+X 2 0)+(332488500373/570500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4863/1024 : ℝ)) (lo := (5297/50000 : ℝ)) (hi := (16299/100000 : ℝ)) (c := (57043518430527993001/57050000000000000000 : ℝ)) (alpha := (332488500373/570500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (57043518430527993001/57050000000000000000 : ℝ)*(X 0 1+X 2 1)+(332488500373/570500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4863/1024 : ℝ)) (lo := (5297/50000 : ℝ)) (hi := (16299/100000 : ℝ)) (c := (57043518430527993001/57050000000000000000 : ℝ)) (alpha := (332488500373/570500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (57043518430527993001/57050000000000000000 : ℝ)*(X 0 2+X 1 2)+(332488500373/570500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4863/1024 : ℝ)) (lo := (5297/50000 : ℝ)) (hi := (16299/100000 : ℝ)) (c := (57043518430527993001/57050000000000000000 : ℝ)) (alpha := (332488500373/570500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-819310777/5000000000 : ℝ)*X 0 0+(5451220773/10000000000 : ℝ)*X 0 1+(5183156193/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349637029/10000000000 : ℝ)*X 1 0+(-1110429/6250000 : ℝ)*X 1 1+(323947259/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668704623/1250000000 : ℝ)*X 2 0+(5183156191/10000000000 : ℝ)*X 2 1+(-1776686397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4190832213/10000000000 : ℝ)*X 0 0+(3859992177/10000000000 : ℝ)*X 0 1+(227109859/500000000 : ℝ)*X 0 2+(4190832213/10000000000 : ℝ)*X 1 0+(3859992177/10000000000 : ℝ)*X 1 1+(227109859/500000000 : ℝ)*X 1 2+(4190832213/10000000000 : ℝ)*X 2 0+(3859992177/10000000000 : ℝ)*X 2 1+(227109859/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-819343761/5000000000 : ℝ)*X 0 0+(2592585579/5000000000 : ℝ)*X 0 1+(5449184607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((527814131/1000000000 : ℝ)*X 1 0+(-377664487/2500000000 : ℝ)*X 1 1+(2724592303/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278141309/10000000000 : ℝ)*X 2 0+(2724592303/5000000000 : ℝ)*X 2 1+(-1510657949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((419100009/1000000000 : ℝ)*X 0 0+(4537069133/10000000000 : ℝ)*X 0 1+(966293541/2500000000 : ℝ)*X 0 2+(419100009/1000000000 : ℝ)*X 1 0+(4537069133/10000000000 : ℝ)*X 1 1+(966293541/2500000000 : ℝ)*X 1 2+(419100009/1000000000 : ℝ)*X 2 0+(4537069133/10000000000 : ℝ)*X 2 1+(966293541/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27199777239825880253073/5705000000000000000000000000 : ℝ) := by norm_num
    linear_combination (190844819/25000000000000 : ℝ)*(base19) + (680908901/100000000000000 : ℝ)*(base23) + (1366579/5000000000000 : ℝ)*(lower2) + (58818881/50000000000000 : ℝ)*(upper3) + (245049/312500000000 : ℝ)*(upper5) + (519630503751837/20000000000000 : ℝ)*(major0) + (519630503751837/20000000000000 : ℝ)*(major1) + (519630503751837/20000000000000 : ℝ)*(major2) + (1865226787249727/50000000000000 : ℝ)*(sp0) + (1865230762065589/50000000000000 : ℝ)*(sp1) + (1865230803300777/50000000000000 : ℝ)*(sp2) + (1465838598663853/100000000000000 : ℝ)*(sp3) + (8713011001/100000000000000 : ℝ)*(sp4) + (3992420439/100000000000000 : ℝ)*(sp7) + (366460647771073/25000000000000 : ℝ)*(f.failure) + (1865231143755227/50000000000000 : ℝ)*(f.sum) + (178070919661/89140625000000000000000000 : ℝ)*base66 + (11331167670291007163/1141000000000000000000000000000000 : ℝ)*base68 + (1405817272831992837/1141000000000000000000000000000000 : ℝ)*base69 + (1253866199795992837/1141000000000000000000000000000000 : ℝ)*base71 + (26254829163239/5705000000000000000000000000 : ℝ)*base74 + (987552456008992837/1141000000000000000000000000000000 : ℝ)*base75 + (4391896473538007163/1141000000000000000000000000000000 : ℝ)*base78 + (2935066357965007163/1141000000000000000000000000000000 : ℝ)*base80 + (19883197768611/5705000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (289019/156250000000000000000 : ℝ)*base90 + (289019/156250000000000000000 : ℝ)*base92 + (289019/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24119119675558128534059018313/2852500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (631154173/50000000000000 : ℝ)*(base19) + (682331749/50000000000000 : ℝ)*(base23) + (15861381/4000000000000 : ℝ)*(lower1) + (177539927/100000000000000 : ℝ)*(upper3) + (1859279/4000000000000 : ℝ)*(lower4) + (174900217/100000000000000 : ℝ)*(upper5) + (2637996063469771/100000000000000 : ℝ)*(major0) + (2637996063469771/100000000000000 : ℝ)*(major1) + (2637996063469771/100000000000000 : ℝ)*(major2) + (55396997/5000000000000 : ℝ)*(sp2) + (236729378983669/6250000000000 : ℝ)*(sp4) + (1893834400715179/50000000000000 : ℝ)*(sp5) + (1893833795567633/50000000000000 : ℝ)*(sp6) + (372080445338273/25000000000000 : ℝ)*(sp7) + (372080445338273/25000000000000 : ℝ)*(f.failure) + (236729378983669/6250000000000 : ℝ)*(f.sum) + (129457719017217/28525000000000000000000000000 : ℝ)*base66 + (43581824083381372771/5705000000000000000000000000000000 : ℝ)*base67 + (25987432999958627229/5705000000000000000000000000000000 : ℝ)*base70 + (197459601175021372771/5705000000000000000000000000000000 : ℝ)*base71 + (23847124846283/28525000000000000000000000000 : ℝ)*base73 + (384761987532058627229/5705000000000000000000000000000000 : ℝ)*base76 + (25652424092648627229/5705000000000000000000000000000000 : ℝ)*base78 + (31661332511938627229/5705000000000000000000000000000000 : ℝ)*base80 + (31652987021267/28525000000000000000000000000 : ℝ)*base82 + (1264381/156250000000000000000 : ℝ)*base89 + (1264381/156250000000000000000 : ℝ)*base91 + (1264381/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1637_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11077897/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16299/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (53/500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16293/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1637_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1637_box_0 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-343970211/2500000000 : ℝ)*x 0 + (338205183/625000000 : ℝ)*x 1 + (5411282977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343970211/2500000000 : ℝ)^4867 ≤ (2027628443263/25000000000000 : ℝ)^3843 := by
    have hnat : (343970211 : ℕ)^4867*25000000000000^3843 ≤ 2027628443263^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343970211 2500000000 2027628443263 25000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338205183/625000000 : ℝ)^4867 ≤ (11486185709217/25000000000000 : ℝ)^3843 := by
    have hnat : (338205183 : ℕ)^4867*25000000000000^3843 ≤ 11486185709217^3843*625000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338205183 625000000 11486185709217 25000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411282977/10000000000 : ℝ)^4867 ≤ (45944743363761/100000000000000 : ℝ)^3843 := by
    have hnat : (5411282977 : ℕ)^4867*100000000000000^3843 ≤ 45944743363761^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411282977 10000000000 45944743363761 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-343970211/2500000000 : ℝ), (338205183/625000000 : ℝ), (5411282977/10000000000 : ℝ)] ![(2027628443263/25000000000000 : ℝ), (11486185709217/25000000000000 : ℝ), (45944743363761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-343970211/2500000000 : ℝ)|^4867 ≤ (2027628443263/25000000000000 : ℝ)^3843
        have hw : |(-343970211/2500000000 : ℝ)|=(343970211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338205183/625000000 : ℝ)|^4867 ≤ (11486185709217/25000000000000 : ℝ)^3843
        have hw : |(338205183/625000000 : ℝ)|=(338205183/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411282977/10000000000 : ℝ)|^4867 ≤ (45944743363761/100000000000000 : ℝ)^3843
        have hw : |(5411282977/10000000000 : ℝ)|=(5411282977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_box_1 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251218853/10000000000 : ℝ)*x 0 + (-1600798721/10000000000 : ℝ)*x 1 + (5411282777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251218853/10000000000 : ℝ)^4867 ≤ (22115209347759/50000000000000 : ℝ)^3843 := by
    have hnat : (5251218853 : ℕ)^4867*50000000000000^3843 ≤ 22115209347759^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251218853 10000000000 22115209347759 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1600798721/10000000000 : ℝ)^4867 ≤ (9824840080183/100000000000000 : ℝ)^3843 := by
    have hnat : (1600798721 : ℕ)^4867*100000000000000^3843 ≤ 9824840080183^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1600798721 10000000000 9824840080183 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411282777/10000000000 : ℝ)^4867 ≤ (5743092651647/12500000000000 : ℝ)^3843 := by
    have hnat : (5411282777 : ℕ)^4867*12500000000000^3843 ≤ 5743092651647^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411282777 10000000000 5743092651647 12500000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251218853/10000000000 : ℝ), (-1600798721/10000000000 : ℝ), (5411282777/10000000000 : ℝ)] ![(22115209347759/50000000000000 : ℝ), (9824840080183/100000000000000 : ℝ), (5743092651647/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251218853/10000000000 : ℝ)|^4867 ≤ (22115209347759/50000000000000 : ℝ)^3843
        have hw : |(5251218853/10000000000 : ℝ)|=(5251218853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1600798721/10000000000 : ℝ)|^4867 ≤ (9824840080183/100000000000000 : ℝ)^3843
        have hw : |(-1600798721/10000000000 : ℝ)|=(1600798721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411282777/10000000000 : ℝ)|^4867 ≤ (5743092651647/12500000000000 : ℝ)^3843
        have hw : |(5411282777/10000000000 : ℝ)|=(5411282777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_box_2 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1312804729/2500000000 : ℝ)*x 0 + (1082256531/2000000000 : ℝ)*x 1 + (-1600798803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312804729/2500000000 : ℝ)^4867 ≤ (22115209683777/50000000000000 : ℝ)^3843 := by
    have hnat : (1312804729 : ℕ)^4867*50000000000000^3843 ≤ 22115209683777^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312804729 2500000000 22115209683777 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082256531/2000000000 : ℝ)^4867 ≤ (45944739901319/100000000000000 : ℝ)^3843 := by
    have hnat : (1082256531 : ℕ)^4867*100000000000000^3843 ≤ 45944739901319^3843*2000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082256531 2000000000 45944739901319 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1600798803/10000000000 : ℝ)^4867 ≤ (2456210179389/25000000000000 : ℝ)^3843 := by
    have hnat : (1600798803 : ℕ)^4867*25000000000000^3843 ≤ 2456210179389^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1600798803 10000000000 2456210179389 25000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312804729/2500000000 : ℝ), (1082256531/2000000000 : ℝ), (-1600798803/10000000000 : ℝ)] ![(22115209683777/50000000000000 : ℝ), (45944739901319/100000000000000 : ℝ), (2456210179389/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312804729/2500000000 : ℝ)|^4867 ≤ (22115209683777/50000000000000 : ℝ)^3843
        have hw : |(1312804729/2500000000 : ℝ)|=(1312804729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082256531/2000000000 : ℝ)|^4867 ≤ (45944739901319/100000000000000 : ℝ)^3843
        have hw : |(1082256531/2000000000 : ℝ)|=(1082256531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1600798803/10000000000 : ℝ)|^4867 ≤ (2456210179389/25000000000000 : ℝ)^3843
        have hw : |(-1600798803/10000000000 : ℝ)|=(1600798803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_box_3 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4468539139/10000000000 : ℝ)*x 0 + (812843863/2000000000 : ℝ)*x 1 + (4064219463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4468539139/10000000000 : ℝ)^4867 ≤ (4506705946123/12500000000000 : ℝ)^3843 := by
    have hnat : (4468539139 : ℕ)^4867*12500000000000^3843 ≤ 4506705946123^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4468539139 10000000000 4506705946123 12500000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (812843863/2000000000 : ℝ)^4867 ≤ (31973175470279/100000000000000 : ℝ)^3843 := by
    have hnat : (812843863 : ℕ)^4867*100000000000000^3843 ≤ 31973175470279^3843*2000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      812843863 2000000000 31973175470279 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4064219463/10000000000 : ℝ)^4867 ≤ (6394635388967/20000000000000 : ℝ)^3843 := by
    have hnat : (4064219463 : ℕ)^4867*20000000000000^3843 ≤ 6394635388967^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4064219463 10000000000 6394635388967 20000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4468539139/10000000000 : ℝ), (812843863/2000000000 : ℝ), (4064219463/10000000000 : ℝ)] ![(4506705946123/12500000000000 : ℝ), (31973175470279/100000000000000 : ℝ), (6394635388967/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4468539139/10000000000 : ℝ)|^4867 ≤ (4506705946123/12500000000000 : ℝ)^3843
        have hw : |(4468539139/10000000000 : ℝ)|=(4468539139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(812843863/2000000000 : ℝ)|^4867 ≤ (31973175470279/100000000000000 : ℝ)^3843
        have hw : |(812843863/2000000000 : ℝ)|=(812843863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4064219463/10000000000 : ℝ)|^4867 ≤ (6394635388967/20000000000000 : ℝ)^3843
        have hw : |(4064219463/10000000000 : ℝ)|=(4064219463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_box_4 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-956007067/5000000000 : ℝ)*x 0 + (521534699/1000000000 : ℝ)*x 1 + (1043069389/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (956007067/5000000000 : ℝ)^4867 ≤ (6151886317429/50000000000000 : ℝ)^3843 := by
    have hnat : (956007067 : ℕ)^4867*50000000000000^3843 ≤ 6151886317429^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956007067 5000000000 6151886317429 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521534699/1000000000 : ℝ)^4867 ≤ (43848113915627/100000000000000 : ℝ)^3843 := by
    have hnat : (521534699 : ℕ)^4867*100000000000000^3843 ≤ 43848113915627^3843*1000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521534699 1000000000 43848113915627 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043069389/2000000000 : ℝ)^4867 ≤ (43848113436477/100000000000000 : ℝ)^3843 := by
    have hnat : (1043069389 : ℕ)^4867*100000000000000^3843 ≤ 43848113436477^3843*2000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043069389 2000000000 43848113436477 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-956007067/5000000000 : ℝ), (521534699/1000000000 : ℝ), (1043069389/2000000000 : ℝ)] ![(6151886317429/50000000000000 : ℝ), (43848113915627/100000000000000 : ℝ), (43848113436477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-956007067/5000000000 : ℝ)|^4867 ≤ (6151886317429/50000000000000 : ℝ)^3843
        have hw : |(-956007067/5000000000 : ℝ)|=(956007067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521534699/1000000000 : ℝ)|^4867 ≤ (43848113915627/100000000000000 : ℝ)^3843
        have hw : |(521534699/1000000000 : ℝ)|=(521534699/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043069389/2000000000 : ℝ)|^4867 ≤ (43848113436477/100000000000000 : ℝ)^3843
        have hw : |(1043069389/2000000000 : ℝ)|=(1043069389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_box_5 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215437673/400000000 : ℝ)*x 0 + (-1684443033/10000000000 : ℝ)*x 1 + (1303836761/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215437673/400000000 : ℝ)^4867 ≤ (22836211053861/50000000000000 : ℝ)^3843 := by
    have hnat : (215437673 : ℕ)^4867*50000000000000^3843 ≤ 22836211053861^3843*400000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215437673 400000000 22836211053861 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1684443033/10000000000 : ℝ)^4867 ≤ (2095892676733/20000000000000 : ℝ)^3843 := by
    have hnat : (1684443033 : ℕ)^4867*20000000000000^3843 ≤ 2095892676733^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684443033 10000000000 2095892676733 20000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303836761/2500000000 : ℝ)^4867 ≤ (43848114490607/100000000000000 : ℝ)^3843 := by
    have hnat : (1303836761 : ℕ)^4867*100000000000000^3843 ≤ 43848114490607^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303836761 2500000000 43848114490607 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215437673/400000000 : ℝ), (-1684443033/10000000000 : ℝ), (1303836761/2500000000 : ℝ)] ![(22836211053861/50000000000000 : ℝ), (2095892676733/20000000000000 : ℝ), (43848114490607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215437673/400000000 : ℝ)|^4867 ≤ (22836211053861/50000000000000 : ℝ)^3843
        have hw : |(215437673/400000000 : ℝ)|=(215437673/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1684443033/10000000000 : ℝ)|^4867 ≤ (2095892676733/20000000000000 : ℝ)^3843
        have hw : |(-1684443033/10000000000 : ℝ)|=(1684443033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303836761/2500000000 : ℝ)|^4867 ≤ (43848114490607/100000000000000 : ℝ)^3843
        have hw : |(1303836761/2500000000 : ℝ)|=(1303836761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_box_6 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692970979/5000000000 : ℝ)*x 0 + (20372449/39062500 : ℝ)*x 1 + (-1684442987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692970979/5000000000 : ℝ)^4867 ≤ (45672423536073/100000000000000 : ℝ)^3843 := by
    have hnat : (2692970979 : ℕ)^4867*100000000000000^3843 ≤ 45672423536073^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692970979 5000000000 45672423536073 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20372449/39062500 : ℝ)^4867 ≤ (4384811342583/10000000000000 : ℝ)^3843 := by
    have hnat : (20372449 : ℕ)^4867*10000000000000^3843 ≤ 4384811342583^3843*39062500^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20372449 39062500 4384811342583 10000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1684442987/10000000000 : ℝ)^4867 ≤ (10479463021229/100000000000000 : ℝ)^3843 := by
    have hnat : (1684442987 : ℕ)^4867*100000000000000^3843 ≤ 10479463021229^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684442987 10000000000 10479463021229 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692970979/5000000000 : ℝ), (20372449/39062500 : ℝ), (-1684442987/10000000000 : ℝ)] ![(45672423536073/100000000000000 : ℝ), (4384811342583/10000000000000 : ℝ), (10479463021229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692970979/5000000000 : ℝ)|^4867 ≤ (45672423536073/100000000000000 : ℝ)^3843
        have hw : |(2692970979/5000000000 : ℝ)|=(2692970979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20372449/39062500 : ℝ)|^4867 ≤ (4384811342583/10000000000000 : ℝ)^3843
        have hw : |(20372449/39062500 : ℝ)|=(20372449/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1684442987/10000000000 : ℝ)|^4867 ≤ (10479463021229/100000000000000 : ℝ)^3843
        have hw : |(-1684442987/10000000000 : ℝ)|=(1684442987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_box_7 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3906818563/10000000000 : ℝ)*x 0 + (2172374513/5000000000 : ℝ)*x 1 + (434474923/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3906818563/10000000000 : ℝ)^4867 ≤ (6082625431/20000000000 : ℝ)^3843 := by
    have hnat : (3906818563 : ℕ)^4867*20000000000^3843 ≤ 6082625431^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3906818563 10000000000 6082625431 20000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2172374513/5000000000 : ℝ)^4867 ≤ (34793435379419/100000000000000 : ℝ)^3843 := by
    have hnat : (2172374513 : ℕ)^4867*100000000000000^3843 ≤ 34793435379419^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172374513 5000000000 34793435379419 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434474923/1000000000 : ℝ)^4867 ≤ (34793437448387/100000000000000 : ℝ)^3843 := by
    have hnat : (434474923 : ℕ)^4867*100000000000000^3843 ≤ 34793437448387^3843*1000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434474923 1000000000 34793437448387 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3906818563/10000000000 : ℝ), (2172374513/5000000000 : ℝ), (434474923/1000000000 : ℝ)] ![(6082625431/20000000000 : ℝ), (34793435379419/100000000000000 : ℝ), (34793437448387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3906818563/10000000000 : ℝ)|^4867 ≤ (6082625431/20000000000 : ℝ)^3843
        have hw : |(3906818563/10000000000 : ℝ)|=(3906818563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2172374513/5000000000 : ℝ)|^4867 ≤ (34793435379419/100000000000000 : ℝ)^3843
        have hw : |(2172374513/5000000000 : ℝ)|=(2172374513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(434474923/1000000000 : ℝ)|^4867 ≤ (34793437448387/100000000000000 : ℝ)^3843
        have hw : |(434474923/1000000000 : ℝ)|=(434474923/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_box_8 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1797762283/10000000000 : ℝ)*x 0 + (5074739879/10000000000 : ℝ)*x 1 + (217635979/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1797762283/10000000000 : ℝ)^4867 ≤ (227603711903/2000000000000 : ℝ)^3843 := by
    have hnat : (1797762283 : ℕ)^4867*2000000000000^3843 ≤ 227603711903^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797762283 10000000000 227603711903 2000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5074739879/10000000000 : ℝ)^4867 ≤ (42356375189777/100000000000000 : ℝ)^3843 := by
    have hnat : (5074739879 : ℕ)^4867*100000000000000^3843 ≤ 42356375189777^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5074739879 10000000000 42356375189777 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217635979/400000000 : ℝ)^4867 ≤ (5782929900063/12500000000000 : ℝ)^3843 := by
    have hnat : (217635979 : ℕ)^4867*12500000000000^3843 ≤ 5782929900063^3843*400000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217635979 400000000 5782929900063 12500000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1797762283/10000000000 : ℝ), (5074739879/10000000000 : ℝ), (217635979/400000000 : ℝ)] ![(227603711903/2000000000000 : ℝ), (42356375189777/100000000000000 : ℝ), (5782929900063/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1797762283/10000000000 : ℝ)|^4867 ≤ (227603711903/2000000000000 : ℝ)^3843
        have hw : |(-1797762283/10000000000 : ℝ)|=(1797762283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5074739879/10000000000 : ℝ)|^4867 ≤ (42356375189777/100000000000000 : ℝ)^3843
        have hw : |(5074739879/10000000000 : ℝ)|=(5074739879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217635979/400000000 : ℝ)|^4867 ≤ (5782929900063/12500000000000 : ℝ)^3843
        have hw : |(217635979/400000000 : ℝ)|=(217635979/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_box_9 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8173209/15625000 : ℝ)*x 0 + (-49616151/312500000 : ℝ)*x 1 + (2720449803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8173209/15625000 : ℝ)^4867 ≤ (5501661474759/12500000000000 : ℝ)^3843 := by
    have hnat : (8173209 : ℕ)^4867*12500000000000^3843 ≤ 5501661474759^3843*15625000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8173209 15625000 5501661474759 12500000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49616151/312500000 : ℝ)^4867 ≤ (9723267582377/100000000000000 : ℝ)^3843 := by
    have hnat : (49616151 : ℕ)^4867*100000000000000^3843 ≤ 9723267582377^3843*312500000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49616151 312500000 9723267582377 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2720449803/5000000000 : ℝ)^4867 ≤ (46263440611187/100000000000000 : ℝ)^3843 := by
    have hnat : (2720449803 : ℕ)^4867*100000000000000^3843 ≤ 46263440611187^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720449803 5000000000 46263440611187 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8173209/15625000 : ℝ), (-49616151/312500000 : ℝ), (2720449803/5000000000 : ℝ)] ![(5501661474759/12500000000000 : ℝ), (9723267582377/100000000000000 : ℝ), (46263440611187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8173209/15625000 : ℝ)|^4867 ≤ (5501661474759/12500000000000 : ℝ)^3843
        have hw : |(8173209/15625000 : ℝ)|=(8173209/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-49616151/312500000 : ℝ)|^4867 ≤ (9723267582377/100000000000000 : ℝ)^3843
        have hw : |(-49616151/312500000 : ℝ)|=(49616151/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2720449803/5000000000 : ℝ)|^4867 ≤ (46263440611187/100000000000000 : ℝ)^3843
        have hw : |(2720449803/5000000000 : ℝ)|=(2720449803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_box_10 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230853799/10000000000 : ℝ)*x 0 + (1360225109/2500000000 : ℝ)*x 1 + (-793857813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230853799/10000000000 : ℝ)^4867 ≤ (1375415381677/3125000000000 : ℝ)^3843 := by
    have hnat : (5230853799 : ℕ)^4867*3125000000000^3843 ≤ 1375415381677^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230853799 10000000000 1375415381677 3125000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360225109/2500000000 : ℝ)^4867 ≤ (46263449549103/100000000000000 : ℝ)^3843 := by
    have hnat : (1360225109 : ℕ)^4867*100000000000000^3843 ≤ 46263449549103^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360225109 2500000000 46263449549103 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (793857813/5000000000 : ℝ)^4867 ≤ (4861629114403/50000000000000 : ℝ)^3843 := by
    have hnat : (793857813 : ℕ)^4867*50000000000000^3843 ≤ 4861629114403^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793857813 5000000000 4861629114403 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230853799/10000000000 : ℝ), (1360225109/2500000000 : ℝ), (-793857813/5000000000 : ℝ)] ![(1375415381677/3125000000000 : ℝ), (46263449549103/100000000000000 : ℝ), (4861629114403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230853799/10000000000 : ℝ)|^4867 ≤ (1375415381677/3125000000000 : ℝ)^3843
        have hw : |(5230853799/10000000000 : ℝ)|=(5230853799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360225109/2500000000 : ℝ)|^4867 ≤ (46263449549103/100000000000000 : ℝ)^3843
        have hw : |(1360225109/2500000000 : ℝ)|=(1360225109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-793857813/5000000000 : ℝ)|^4867 ≤ (4861629114403/50000000000000 : ℝ)^3843
        have hw : |(-793857813/5000000000 : ℝ)|=(793857813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_box_11 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4551059229/10000000000 : ℝ)*x 0 + (2010870399/5000000000 : ℝ)*x 1 + (125679377/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4551059229/10000000000 : ℝ)^4867 ≤ (9224730007141/25000000000000 : ℝ)^3843 := by
    have hnat : (4551059229 : ℕ)^4867*25000000000000^3843 ≤ 9224730007141^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4551059229 10000000000 9224730007141 25000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010870399/5000000000 : ℝ)^4867 ≤ (31550543625699/100000000000000 : ℝ)^3843 := by
    have hnat : (2010870399 : ℕ)^4867*100000000000000^3843 ≤ 31550543625699^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010870399 5000000000 31550543625699 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125679377/312500000 : ℝ)^4867 ≤ (31550536333143/100000000000000 : ℝ)^3843 := by
    have hnat : (125679377 : ℕ)^4867*100000000000000^3843 ≤ 31550536333143^3843*312500000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125679377 312500000 31550536333143 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4551059229/10000000000 : ℝ), (2010870399/5000000000 : ℝ), (125679377/312500000 : ℝ)] ![(9224730007141/25000000000000 : ℝ), (31550543625699/100000000000000 : ℝ), (31550536333143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4551059229/10000000000 : ℝ)|^4867 ≤ (9224730007141/25000000000000 : ℝ)^3843
        have hw : |(4551059229/10000000000 : ℝ)|=(4551059229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2010870399/5000000000 : ℝ)|^4867 ≤ (31550543625699/100000000000000 : ℝ)^3843
        have hw : |(2010870399/5000000000 : ℝ)|=(2010870399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(125679377/312500000 : ℝ)|^4867 ≤ (31550536333143/100000000000000 : ℝ)^3843
        have hw : |(125679377/312500000 : ℝ)|=(125679377/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_box_12 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1488532003/10000000000 : ℝ)*x 0 + (5546411439/10000000000 : ℝ)*x 1 + (1298875567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1488532003/10000000000 : ℝ)^4867 ≤ (35001978913/390625000000 : ℝ)^3843 := by
    have hnat : (1488532003 : ℕ)^4867*390625000000^3843 ≤ 35001978913^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1488532003 10000000000 35001978913 390625000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5546411439/10000000000 : ℝ)^4867 ≤ (9480514857499/20000000000000 : ℝ)^3843 := by
    have hnat : (5546411439 : ℕ)^4867*20000000000000^3843 ≤ 9480514857499^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5546411439 10000000000 9480514857499 20000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298875567/2500000000 : ℝ)^4867 ≤ (21818459547019/50000000000000 : ℝ)^3843 := by
    have hnat : (1298875567 : ℕ)^4867*50000000000000^3843 ≤ 21818459547019^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298875567 2500000000 21818459547019 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1488532003/10000000000 : ℝ), (5546411439/10000000000 : ℝ), (1298875567/2500000000 : ℝ)] ![(35001978913/390625000000 : ℝ), (9480514857499/20000000000000 : ℝ), (21818459547019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1488532003/10000000000 : ℝ)|^4867 ≤ (35001978913/390625000000 : ℝ)^3843
        have hw : |(-1488532003/10000000000 : ℝ)|=(1488532003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5546411439/10000000000 : ℝ)|^4867 ≤ (9480514857499/20000000000000 : ℝ)^3843
        have hw : |(5546411439/10000000000 : ℝ)|=(5546411439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1298875567/2500000000 : ℝ)|^4867 ≤ (21818459547019/50000000000000 : ℝ)^3843
        have hw : |(1298875567/2500000000 : ℝ)|=(1298875567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_box_13 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079919121/2000000000 : ℝ)*x 0 + (-1692625233/10000000000 : ℝ)*x 1 + (1039100487/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079919121/2000000000 : ℝ)^4867 ≤ (5727388266409/12500000000000 : ℝ)^3843 := by
    have hnat : (1079919121 : ℕ)^4867*12500000000000^3843 ≤ 5727388266409^3843*2000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079919121 2000000000 5727388266409 12500000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1692625233/10000000000 : ℝ)^4867 ≤ (10543972991913/100000000000000 : ℝ)^3843 := by
    have hnat : (1692625233 : ℕ)^4867*100000000000000^3843 ≤ 10543972991913^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1692625233 10000000000 10543972991913 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039100487/2000000000 : ℝ)^4867 ≤ (4363692087041/10000000000000 : ℝ)^3843 := by
    have hnat : (1039100487 : ℕ)^4867*10000000000000^3843 ≤ 4363692087041^3843*2000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039100487 2000000000 4363692087041 10000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079919121/2000000000 : ℝ), (-1692625233/10000000000 : ℝ), (1039100487/2000000000 : ℝ)] ![(5727388266409/12500000000000 : ℝ), (10543972991913/100000000000000 : ℝ), (4363692087041/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079919121/2000000000 : ℝ)|^4867 ≤ (5727388266409/12500000000000 : ℝ)^3843
        have hw : |(1079919121/2000000000 : ℝ)|=(1079919121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1692625233/10000000000 : ℝ)|^4867 ≤ (10543972991913/100000000000000 : ℝ)^3843
        have hw : |(-1692625233/10000000000 : ℝ)|=(1692625233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1039100487/2000000000 : ℝ)|^4867 ≤ (4363692087041/10000000000000 : ℝ)^3843
        have hw : |(1039100487/2000000000 : ℝ)|=(1039100487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_box_14 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (674949483/1250000000 : ℝ)*x 0 + (1298875523/2500000000 : ℝ)*x 1 + (-846312671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (674949483/1250000000 : ℝ)^4867 ≤ (1832764356587/4000000000000 : ℝ)^3843 := by
    have hnat : (674949483 : ℕ)^4867*4000000000000^3843 ≤ 1832764356587^3843*1250000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674949483 1250000000 1832764356587 4000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1298875523/2500000000 : ℝ)^4867 ≤ (43636917221933/100000000000000 : ℝ)^3843 := by
    have hnat : (1298875523 : ℕ)^4867*100000000000000^3843 ≤ 43636917221933^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298875523 2500000000 43636917221933 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846312671/5000000000 : ℝ)^4867 ≤ (10543973851839/100000000000000 : ℝ)^3843 := by
    have hnat : (846312671 : ℕ)^4867*100000000000000^3843 ≤ 10543973851839^3843*5000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846312671 5000000000 10543973851839 100000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(674949483/1250000000 : ℝ), (1298875523/2500000000 : ℝ), (-846312671/5000000000 : ℝ)] ![(1832764356587/4000000000000 : ℝ), (43636917221933/100000000000000 : ℝ), (10543973851839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(674949483/1250000000 : ℝ)|^4867 ≤ (1832764356587/4000000000000 : ℝ)^3843
        have hw : |(674949483/1250000000 : ℝ)|=(674949483/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1298875523/2500000000 : ℝ)|^4867 ≤ (43636917221933/100000000000000 : ℝ)^3843
        have hw : |(1298875523/2500000000 : ℝ)|=(1298875523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-846312671/5000000000 : ℝ)|^4867 ≤ (10543973851839/100000000000000 : ℝ)^3843
        have hw : |(-846312671/5000000000 : ℝ)|=(846312671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1637_box_15 (p : ℝ) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3848299849/10000000000 : ℝ)*x 0 + (1093277551/2500000000 : ℝ)*x 1 + (874622031/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3848299849/10000000000 : ℝ)^4867 ≤ (14918676060331/50000000000000 : ℝ)^3843 := by
    have hnat : (3848299849 : ℕ)^4867*50000000000000^3843 ≤ 14918676060331^3843*10000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3848299849 10000000000 14918676060331 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093277551/2500000000 : ℝ)^4867 ≤ (17540662092063/50000000000000 : ℝ)^3843 := by
    have hnat : (1093277551 : ℕ)^4867*50000000000000^3843 ≤ 17540662092063^3843*2500000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093277551 2500000000 17540662092063 50000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (874622031/2000000000 : ℝ)^4867 ≤ (7016264737261/20000000000000 : ℝ)^3843 := by
    have hnat : (874622031 : ℕ)^4867*20000000000000^3843 ≤ 7016264737261^3843*2000000000^4867 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874622031 2000000000 7016264737261 20000000000000 4867 3843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4867/1024 : ℝ)) 4867 3843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3848299849/10000000000 : ℝ), (1093277551/2500000000 : ℝ), (874622031/2000000000 : ℝ)] ![(14918676060331/50000000000000 : ℝ), (17540662092063/50000000000000 : ℝ), (7016264737261/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3848299849/10000000000 : ℝ)|^4867 ≤ (14918676060331/50000000000000 : ℝ)^3843
        have hw : |(3848299849/10000000000 : ℝ)|=(3848299849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093277551/2500000000 : ℝ)|^4867 ≤ (17540662092063/50000000000000 : ℝ)^3843
        have hw : |(1093277551/2500000000 : ℝ)|=(1093277551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(874622031/2000000000 : ℝ)|^4867 ≤ (7016264737261/20000000000000 : ℝ)^3843
        have hw : |(874622031/2000000000 : ℝ)|=(874622031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1637_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11077897/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16293/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (53/500 : ℝ)*pair X i i ≤ pair X i h) :
    -(13003/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29243/50000 : ℝ) ∧ (20239/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (2753/3125 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16293/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (53/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16293/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (53/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16293/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (53/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16293/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (53/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16293/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (53/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16293/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (53/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (53/500 : ℝ) ^ (4863/1024 : ℝ) ≤ (2350469985198973/100000000000000000000 : ℝ) := by
    have hpowers : (53/500 : ℝ)^4863 ≤ (2350469985198973/100000000000000000000 : ℝ)^1024 := by
      have hnat : (53 : ℕ)^4863*100000000000000000000^1024 ≤ 2350469985198973^1024*500^4863 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53 500 2350469985198973 100000000000000000000 4863 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (53/500 : ℝ)) (X := (2350469985198973/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16293/100000 : ℝ) ^ (4863/1024 : ℝ) ≤ (4526000129789139/25000000000000000000 : ℝ) := by
    have hpowers : (16293/100000 : ℝ)^4863 ≤ (4526000129789139/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16293 : ℕ)^4863*25000000000000000000^1024 ≤ 4526000129789139^1024*100000^4863 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16293 100000 4526000129789139 25000000000000000000 4863 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16293/100000 : ℝ)) (X := (4526000129789139/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002350469985198973/50000000000000000000 : ℝ) ≤ (2500024746417907/2500000000000000 : ℝ) ^ (4863/1024 : ℝ) := by
    have hpowers : (50002350469985198973/50000000000000000000 : ℝ)^1024 ≤ (2500024746417907/2500000000000000 : ℝ)^4863 := by
      have hnat : (50002350469985198973 : ℕ)^1024*2500000000000000^4863 ≤ 2500024746417907^4863*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002350469985198973 50000000000000000000 2500024746417907 2500000000000000 1024 4863 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500024746417907/2500000000000000 : ℝ)) (X := (50002350469985198973/50000000000000000000 : ℝ)) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100020454470504355529/100000000000000000000 : ℝ) ≤ (1000043067421217/1000000000000000 : ℝ) ^ (4863/1024 : ℝ) := by
    have hpowers : (100020454470504355529/100000000000000000000 : ℝ)^1024 ≤ (1000043067421217/1000000000000000 : ℝ)^4863 := by
      have hnat : (100020454470504355529 : ℕ)^1024*1000000000000000^4863 ≤ 1000043067421217^4863*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100020454470504355529 100000000000000000000 1000043067421217 1000000000000000 1024 4863 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000043067421217/1000000000000000 : ℝ)) (X := (100020454470504355529/100000000000000000000 : ℝ)) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12504526000129789139/12500000000000000000 : ℝ) ≤ (1250095295344089/1250000000000000 : ℝ) ^ (4863/1024 : ℝ) := by
    have hpowers : (12504526000129789139/12500000000000000000 : ℝ)^1024 ≤ (1250095295344089/1250000000000000 : ℝ)^4863 := by
      have hnat : (12504526000129789139 : ℕ)^1024*1250000000000000^4863 ≤ 1250095295344089^4863*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504526000129789139 12500000000000000000 1250095295344089 1250000000000000 1024 4863 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250095295344089/1250000000000000 : ℝ)) (X := (12504526000129789139/12500000000000000000 : ℝ)) (by norm_num) 4863 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2350469985198973/100000000000000000000 : ℝ) ≤ ((14230882932092271951/14232500000000000000 : ℝ)+2*(165844270271/284650000000000 : ℝ)*(53/500 : ℝ))^(4863/1024 : ℝ) := by
    rw [show (14230882932092271951/14232500000000000000 : ℝ)+2*(165844270271/284650000000000 : ℝ)*(53/500 : ℝ)=(2500024746417907/2500000000000000 : ℝ) by norm_num, show 1+2*(2350469985198973/100000000000000000000 : ℝ)=(50002350469985198973/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4526000129789139/25000000000000000000 : ℝ)+(2350469985198973/100000000000000000000 : ℝ) ≤ ((14230882932092271951/14232500000000000000 : ℝ)+(165844270271/284650000000000 : ℝ)*((16293/100000 : ℝ)+(53/500 : ℝ)))^(4863/1024 : ℝ) := by
    rw [show (14230882932092271951/14232500000000000000 : ℝ)+(165844270271/284650000000000 : ℝ)*((16293/100000 : ℝ)+(53/500 : ℝ))=(1000043067421217/1000000000000000 : ℝ) by norm_num, show 1+(4526000129789139/25000000000000000000 : ℝ)+(2350469985198973/100000000000000000000 : ℝ)=(100020454470504355529/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4526000129789139/25000000000000000000 : ℝ) ≤ ((14230882932092271951/14232500000000000000 : ℝ)+2*(165844270271/284650000000000 : ℝ)*(16293/100000 : ℝ))^(4863/1024 : ℝ) := by
    rw [show (14230882932092271951/14232500000000000000 : ℝ)+2*(165844270271/284650000000000 : ℝ)*(16293/100000 : ℝ)=(1250095295344089/1250000000000000 : ℝ) by norm_num, show 1+2*(4526000129789139/25000000000000000000 : ℝ)=(12504526000129789139/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14230882932092271951/14232500000000000000 : ℝ)*(X 1 0+X 2 0)+(165844270271/284650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4863/1024 : ℝ)) (lo := (53/500 : ℝ)) (hi := (16293/100000 : ℝ)) (c := (14230882932092271951/14232500000000000000 : ℝ)) (alpha := (165844270271/284650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14230882932092271951/14232500000000000000 : ℝ)*(X 0 1+X 2 1)+(165844270271/284650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4863/1024 : ℝ)) (lo := (53/500 : ℝ)) (hi := (16293/100000 : ℝ)) (c := (14230882932092271951/14232500000000000000 : ℝ)) (alpha := (165844270271/284650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14230882932092271951/14232500000000000000 : ℝ)*(X 0 2+X 1 2)+(165844270271/284650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4863/1024 : ℝ)) (lo := (53/500 : ℝ)) (hi := (16293/100000 : ℝ)) (c := (14230882932092271951/14232500000000000000 : ℝ)) (alpha := (165844270271/284650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-343970211/2500000000 : ℝ)*X 0 0+(338205183/625000000 : ℝ)*X 0 1+(5411282977/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5251218853/10000000000 : ℝ)*X 1 0+(-1600798721/10000000000 : ℝ)*X 1 1+(5411282777/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1312804729/2500000000 : ℝ)*X 2 0+(1082256531/2000000000 : ℝ)*X 2 1+(-1600798803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4468539139/10000000000 : ℝ)*X 0 0+(812843863/2000000000 : ℝ)*X 0 1+(4064219463/10000000000 : ℝ)*X 0 2+(4468539139/10000000000 : ℝ)*X 1 0+(812843863/2000000000 : ℝ)*X 1 1+(4064219463/10000000000 : ℝ)*X 1 2+(4468539139/10000000000 : ℝ)*X 2 0+(812843863/2000000000 : ℝ)*X 2 1+(4064219463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-956007067/5000000000 : ℝ)*X 0 0+(521534699/1000000000 : ℝ)*X 0 1+(1043069389/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((215437673/400000000 : ℝ)*X 1 0+(-1684443033/10000000000 : ℝ)*X 1 1+(1303836761/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2692970979/5000000000 : ℝ)*X 2 0+(20372449/39062500 : ℝ)*X 2 1+(-1684442987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3906818563/10000000000 : ℝ)*X 0 0+(2172374513/5000000000 : ℝ)*X 0 1+(434474923/1000000000 : ℝ)*X 0 2+(3906818563/10000000000 : ℝ)*X 1 0+(2172374513/5000000000 : ℝ)*X 1 1+(434474923/1000000000 : ℝ)*X 1 2+(3906818563/10000000000 : ℝ)*X 2 0+(2172374513/5000000000 : ℝ)*X 2 1+(434474923/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1797762283/10000000000 : ℝ)*X 0 0+(5074739879/10000000000 : ℝ)*X 0 1+(217635979/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((8173209/15625000 : ℝ)*X 1 0+(-49616151/312500000 : ℝ)*X 1 1+(2720449803/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230853799/10000000000 : ℝ)*X 2 0+(1360225109/2500000000 : ℝ)*X 2 1+(-793857813/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4551059229/10000000000 : ℝ)*X 0 0+(2010870399/5000000000 : ℝ)*X 0 1+(125679377/312500000 : ℝ)*X 0 2+(4551059229/10000000000 : ℝ)*X 1 0+(2010870399/5000000000 : ℝ)*X 1 1+(125679377/312500000 : ℝ)*X 1 2+(4551059229/10000000000 : ℝ)*X 2 0+(2010870399/5000000000 : ℝ)*X 2 1+(125679377/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1488532003/10000000000 : ℝ)*X 0 0+(5546411439/10000000000 : ℝ)*X 0 1+(1298875567/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1079919121/2000000000 : ℝ)*X 1 0+(-1692625233/10000000000 : ℝ)*X 1 1+(1039100487/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((674949483/1250000000 : ℝ)*X 2 0+(1298875523/2500000000 : ℝ)*X 2 1+(-846312671/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3848299849/10000000000 : ℝ)*X 0 0+(1093277551/2500000000 : ℝ)*X 0 1+(874622031/2000000000 : ℝ)*X 0 2+(3848299849/10000000000 : ℝ)*X 1 0+(1093277551/2500000000 : ℝ)*X 1 1+(874622031/2000000000 : ℝ)*X 1 2+(3848299849/10000000000 : ℝ)*X 2 0+(1093277551/2500000000 : ℝ)*X 2 1+(874622031/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1637_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-13003/20000 : ℝ) ≤ (-46264629597544275746636127950607/71162500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13742969/50000000000000 : ℝ)*(upper0) + (4827259/20000000000000 : ℝ)*(lower2) + (59867/625000000000 : ℝ)*(upper5) + (346819910427319/20000000000000 : ℝ)*(major0) + (346819910427319/20000000000000 : ℝ)*(major1) + (346819910427319/20000000000000 : ℝ)*(major2) + (187088817/50000000000000 : ℝ)*(sp3) + (1255757142048411/50000000000000 : ℝ)*(sp4) + (2511503457262669/100000000000000 : ℝ)*(sp5) + (251151024432059/10000000000000 : ℝ)*(sp6) + (489177596422517/50000000000000 : ℝ)*(sp7) + (137677393/100000000000000 : ℝ)*(sp8) + (5482255773/50000000000000 : ℝ)*(sp13) + (522181703/12500000000000 : ℝ)*(sp14) + (244588891755667/25000000000000 : ℝ)*(f.failure) + (502302884354843/20000000000000 : ℝ)*(f.sum) + (7448345132301/1138600000000000000000000000 : ℝ)*base65 + (2959722759757370631/284650000000000000000000000000000 : ℝ)*base68 + (75348470084729369/284650000000000000000000000000000 : ℝ)*base69 + (1263113873918329369/284650000000000000000000000000000 : ℝ)*base71 + (105435728098691/5693000000000000000000000000 : ℝ)*base73 + (378689306118079369/284650000000000000000000000000000 : ℝ)*base75 + (3154630174168679369/284650000000000000000000000000000 : ℝ)*base77 + (1891385828056979369/284650000000000000000000000000000 : ℝ)*base79 + (2537455459233/2846500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1495201/156250000000000000000 : ℝ)*base90 + (1495201/156250000000000000000 : ℝ)*base92 + (1495201/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29243/50000 : ℝ) ≤ (41621574262102946568291469743117/71162500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5064583/20000000000000 : ℝ)*(lower1) + (13588397/100000000000000 : ℝ)*(lower3) + (34477351/100000000000000 : ℝ)*(lower5) + (364534828459989/20000000000000 : ℝ)*(major0) + (364534828459989/20000000000000 : ℝ)*(major1) + (364534828459989/20000000000000 : ℝ)*(major2) + (1298761325118643/50000000000000 : ℝ)*(sp0) + (259751320137713/10000000000000 : ℝ)*(sp1) + (1298752582942041/50000000000000 : ℝ)*(sp2) + (1028324469856813/100000000000000 : ℝ)*(sp3) + (737138489/20000000000000 : ℝ)*(sp7) + (5451830869/50000000000000 : ℝ)*(sp9) + (3787830957/20000000000000 : ℝ)*(sp10) + (1454801581/100000000000000 : ℝ)*(sp12) + (514164077774629/50000000000000 : ℝ)*(f.failure) + (649381026259717/25000000000000 : ℝ)*(f.sum) + (5283330790557/5693000000000000000000000000 : ℝ)*base66 + (1242094725212381461/284650000000000000000000000000000 : ℝ)*base68 + (605473510638931461/284650000000000000000000000000000 : ℝ)*base70 + (1097730828499381461/284650000000000000000000000000000 : ℝ)*base72 + (10811278324171/5693000000000000000000000000 : ℝ)*base73 + (2362959286731131461/284650000000000000000000000000000 : ℝ)*base76 + (148038030050568539/284650000000000000000000000000000 : ℝ)*base77 + (283007967641331461/284650000000000000000000000000000 : ℝ)*base80 + (46916695788471/5693000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1150213/312500000000000000000 : ℝ)*base89 + (1150213/312500000000000000000 : ℝ)*base91 + (1150213/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (20239/25000 : ℝ) ≤ (36007705469703698943319862906823/44476562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (30278959/100000000000000 : ℝ)*(lower1) + (3044403/6250000000000 : ℝ)*(lower3) + (276560911/100000000000000 : ℝ)*(upper4) + (480223192604857/25000000000000 : ℝ)*(major0) + (480223192604857/25000000000000 : ℝ)*(major1) + (480223192604857/25000000000000 : ℝ)*(major2) + (382341331/12500000000000 : ℝ)*(sp0) + (2670239911/12500000000000 : ℝ)*(sp1) + (37983274823/25000000000000 : ℝ)*(sp2) + (21067110563/100000000000000 : ℝ)*(sp3) + (682763606163949/25000000000000 : ℝ)*(sp8) + (682759030366789/25000000000000 : ℝ)*(sp9) + (2730905550287151/100000000000000 : ℝ)*(sp10) + (1083720713041521/100000000000000 : ℝ)*(sp11) + (270935445038021/25000000000000 : ℝ)*(f.failure) + (682764370846611/25000000000000 : ℝ)*(f.sum) + (22933368383743/14232500000000000000000000000 : ℝ)*base65 + (3922727455371621493/355812500000000000000000000000000 : ℝ)*base68 + (2488022811312496493/355812500000000000000000000000000 : ℝ)*base70 + (798996736289558993/355812500000000000000000000000000 : ℝ)*base72 + (17859973027319/28465000000000000000000000000 : ℝ)*base74 + (2409088340149246493/355812500000000000000000000000000 : ℝ)*base76 + (298044044546628507/355812500000000000000000000000000 : ℝ)*base77 + (1542701936816871493/355812500000000000000000000000000 : ℝ)*base80 + (42815498696861/28465000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1471837/156250000000000000000 : ℝ)*base89 + (1471837/156250000000000000000 : ℝ)*base91 + (1471837/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-2753/3125 : ℝ) ≤ (-313448015418145997566097958511287/355812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5612021/50000000000000 : ℝ)*(lower2) + (18371391/100000000000000 : ℝ)*(upper3) + (15507/80000000000 : ℝ)*(upper5) + (982152999311121/50000000000000 : ℝ)*(major0) + (982152999311121/50000000000000 : ℝ)*(major1) + (982152999311121/50000000000000 : ℝ)*(major2) + (1530530981/100000000000000 : ℝ)*(sp0) + (1918209667/100000000000000 : ℝ)*(sp5) + (47754354037/100000000000000 : ℝ)*(sp6) + (2040413917/50000000000000 : ℝ)*(sp7) + (1424870030009971/50000000000000 : ℝ)*(sp12) + (569947934468251/20000000000000 : ℝ)*(sp13) + (1424846918098443/50000000000000 : ℝ)*(sp14) + (1108230856849327/100000000000000 : ℝ)*(sp15) + (1108234937677161/100000000000000 : ℝ)*(f.failure) + (1424870795275461/50000000000000 : ℝ)*(f.sum) + (5127319830789/28465000000000000000000000000 : ℝ)*base65 + (5639323712459032929/711625000000000000000000000000000 : ℝ)*base68 + (3056047466496532929/711625000000000000000000000000000 : ℝ)*base70 + (5305106273668342071/711625000000000000000000000000000 : ℝ)*base71 + (66202550936013/14232500000000000000000000000 : ℝ)*base74 + (3333283730210967071/711625000000000000000000000000000 : ℝ)*base75 + (1119058098606657929/711625000000000000000000000000000 : ℝ)*base78 + (2053864864591782929/711625000000000000000000000000000 : ℝ)*base80 + (35313400487373/14232500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (3689583/625000000000000000000 : ℝ)*base90 + (3689583/625000000000000000000 : ℝ)*base92 + (3689583/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1637_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11077897/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16293/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (53/500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13003/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29243/50000 : ℝ) else (20239/25000 : ℝ) ≤ X j i ∧ X j i ≤ (2753/3125 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1637_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1637_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11077897/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1639/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10513/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13003/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29243/50000 : ℝ) else (20239/25000 : ℝ) ≤ X j i ∧ X j i ≤ (2753/3125 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1637_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1637_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1637_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4863/1024 : ℝ) ≤ p) (hpb : p ≤ (4867/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11077897/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1639/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10513/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13003/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29243/50000 : ℝ) else (20239/25000 : ℝ) ≤ X j i ∧ X j i ≤ (2753/3125 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1637_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1531_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:05:27.453213+00:00
-- url     : https://prove2.me/submissions/42b5413c-7877-42fa-86d0-03b477e10478

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
theorem support_rectangle_w1531_s3_0 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-367982493/2000000000 : ℝ)*x 0 + (339587799/625000000 : ℝ)*x 1 + (2608085037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (367982493/2000000000 : ℝ)^4559 ≤ (2816874654319/25000000000000 : ℝ)^3535 := by
    have hnat : (367982493 : ℕ)^4559*25000000000000^3535 ≤ 2816874654319^3535*2000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367982493 2000000000 2816874654319 25000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339587799/625000000 : ℝ)^4559 ≤ (45533301849209/100000000000000 : ℝ)^3535 := by
    have hnat : (339587799 : ℕ)^4559*100000000000000^3535 ≤ 45533301849209^3535*625000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339587799 625000000 45533301849209 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608085037/5000000000 : ℝ)^4559 ≤ (1727967980509/4000000000000 : ℝ)^3535 := by
    have hnat : (2608085037 : ℕ)^4559*4000000000000^3535 ≤ 1727967980509^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608085037 5000000000 1727967980509 4000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-367982493/2000000000 : ℝ), (339587799/625000000 : ℝ), (2608085037/5000000000 : ℝ)] ![(2816874654319/25000000000000 : ℝ), (45533301849209/100000000000000 : ℝ), (1727967980509/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-367982493/2000000000 : ℝ)|^4559 ≤ (2816874654319/25000000000000 : ℝ)^3535
        have hw : |(-367982493/2000000000 : ℝ)|=(367982493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339587799/625000000 : ℝ)|^4559 ≤ (45533301849209/100000000000000 : ℝ)^3535
        have hw : |(339587799/625000000 : ℝ)|=(339587799/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608085037/5000000000 : ℝ)|^4559 ≤ (1727967980509/4000000000000 : ℝ)^3535
        have hw : |(2608085037/5000000000 : ℝ)|=(2608085037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s3_1 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351205729/10000000000 : ℝ)*x 0 + (-390237737/2000000000 : ℝ)*x 1 + (2608085043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351205729/10000000000 : ℝ)^4559 ≤ (22323432309197/50000000000000 : ℝ)^3535 := by
    have hnat : (5351205729 : ℕ)^4559*50000000000000^3535 ≤ 22323432309197^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351205729 10000000000 22323432309197 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (390237737/2000000000 : ℝ)^4559 ≤ (12153935727619/100000000000000 : ℝ)^3535 := by
    have hnat : (390237737 : ℕ)^4559*100000000000000^3535 ≤ 12153935727619^3535*2000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390237737 2000000000 12153935727619 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608085043/5000000000 : ℝ)^4559 ≤ (21599599820447/50000000000000 : ℝ)^3535 := by
    have hnat : (2608085043 : ℕ)^4559*50000000000000^3535 ≤ 21599599820447^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608085043 5000000000 21599599820447 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351205729/10000000000 : ℝ), (-390237737/2000000000 : ℝ), (2608085043/5000000000 : ℝ)] ![(22323432309197/50000000000000 : ℝ), (12153935727619/100000000000000 : ℝ), (21599599820447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351205729/10000000000 : ℝ)|^4559 ≤ (22323432309197/50000000000000 : ℝ)^3535
        have hw : |(5351205729/10000000000 : ℝ)|=(5351205729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-390237737/2000000000 : ℝ)|^4559 ≤ (12153935727619/100000000000000 : ℝ)^3535
        have hw : |(-390237737/2000000000 : ℝ)|=(390237737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608085043/5000000000 : ℝ)|^4559 ≤ (21599599820447/50000000000000 : ℝ)^3535
        have hw : |(2608085043/5000000000 : ℝ)|=(2608085043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s3_2 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337801427/2500000000 : ℝ)*x 0 + (5216170107/10000000000 : ℝ)*x 1 + (-487797171/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337801427/2500000000 : ℝ)^4559 ≤ (4464686439243/10000000000000 : ℝ)^3535 := by
    have hnat : (1337801427 : ℕ)^4559*10000000000000^3535 ≤ 4464686439243^3535*2500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337801427 2500000000 4464686439243 10000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216170107/10000000000 : ℝ)^4559 ≤ (43199199865191/100000000000000 : ℝ)^3535 := by
    have hnat : (5216170107 : ℕ)^4559*100000000000000^3535 ≤ 43199199865191^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216170107 10000000000 43199199865191 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (487797171/2500000000 : ℝ)^4559 ≤ (6076967859793/50000000000000 : ℝ)^3535 := by
    have hnat : (487797171 : ℕ)^4559*50000000000000^3535 ≤ 6076967859793^3535*2500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487797171 2500000000 6076967859793 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337801427/2500000000 : ℝ), (5216170107/10000000000 : ℝ), (-487797171/2500000000 : ℝ)] ![(4464686439243/10000000000000 : ℝ), (43199199865191/100000000000000 : ℝ), (6076967859793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337801427/2500000000 : ℝ)|^4559 ≤ (4464686439243/10000000000000 : ℝ)^3535
        have hw : |(1337801427/2500000000 : ℝ)|=(1337801427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216170107/10000000000 : ℝ)|^4559 ≤ (43199199865191/100000000000000 : ℝ)^3535
        have hw : |(5216170107/10000000000 : ℝ)|=(5216170107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-487797171/2500000000 : ℝ)|^4559 ≤ (6076967859793/50000000000000 : ℝ)^3535
        have hw : |(-487797171/2500000000 : ℝ)|=(487797171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s3_3 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2130377857/5000000000 : ℝ)*x 0 + (401726557/1000000000 : ℝ)*x 1 + (2258232983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130377857/5000000000 : ℝ)^4559 ≤ (33278082496547/100000000000000 : ℝ)^3535 := by
    have hnat : (2130377857 : ℕ)^4559*100000000000000^3535 ≤ 33278082496547^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130377857 5000000000 33278082496547 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401726557/1000000000 : ℝ)^4559 ≤ (30846028012033/100000000000000 : ℝ)^3535 := by
    have hnat : (401726557 : ℕ)^4559*100000000000000^3535 ≤ 30846028012033^3535*1000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401726557 1000000000 30846028012033 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2258232983/5000000000 : ℝ)^4559 ≤ (35875889473373/100000000000000 : ℝ)^3535 := by
    have hnat : (2258232983 : ℕ)^4559*100000000000000^3535 ≤ 35875889473373^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258232983 5000000000 35875889473373 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2130377857/5000000000 : ℝ), (401726557/1000000000 : ℝ), (2258232983/5000000000 : ℝ)] ![(33278082496547/100000000000000 : ℝ), (30846028012033/100000000000000 : ℝ), (35875889473373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2130377857/5000000000 : ℝ)|^4559 ≤ (33278082496547/100000000000000 : ℝ)^3535
        have hw : |(2130377857/5000000000 : ℝ)|=(2130377857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(401726557/1000000000 : ℝ)|^4559 ≤ (30846028012033/100000000000000 : ℝ)^3535
        have hw : |(401726557/1000000000 : ℝ)|=(401726557/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2258232983/5000000000 : ℝ)|^4559 ≤ (35875889473373/100000000000000 : ℝ)^3535
        have hw : |(2258232983/5000000000 : ℝ)|=(2258232983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s3_4 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1839942697/10000000000 : ℝ)*x 0 + (5217318757/10000000000 : ℝ)*x 1 + (1086449487/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1839942697/10000000000 : ℝ)^4559 ≤ (11267737386549/100000000000000 : ℝ)^3535 := by
    have hnat : (1839942697 : ℕ)^4559*100000000000000^3535 ≤ 11267737386549^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1839942697 10000000000 11267737386549 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217318757/10000000000 : ℝ)^4559 ≤ (5401433595903/12500000000000 : ℝ)^3535 := by
    have hnat : (5217318757 : ℕ)^4559*12500000000000^3535 ≤ 5401433595903^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217318757 10000000000 5401433595903 12500000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086449487/2000000000 : ℝ)^4559 ≤ (4552079383981/10000000000000 : ℝ)^3535 := by
    have hnat : (1086449487 : ℕ)^4559*10000000000000^3535 ≤ 4552079383981^3535*2000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086449487 2000000000 4552079383981 10000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1839942697/10000000000 : ℝ), (5217318757/10000000000 : ℝ), (1086449487/2000000000 : ℝ)] ![(11267737386549/100000000000000 : ℝ), (5401433595903/12500000000000 : ℝ), (4552079383981/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1839942697/10000000000 : ℝ)|^4559 ≤ (11267737386549/100000000000000 : ℝ)^3535
        have hw : |(-1839942697/10000000000 : ℝ)|=(1839942697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217318757/10000000000 : ℝ)|^4559 ≤ (5401433595903/12500000000000 : ℝ)^3535
        have hw : |(5217318757/10000000000 : ℝ)|=(5217318757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086449487/2000000000 : ℝ)|^4559 ≤ (4552079383981/10000000000000 : ℝ)^3535
        have hw : |(1086449487/2000000000 : ℝ)|=(1086449487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s3_5 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294019961/10000000000 : ℝ)*x 0 + (-1735111553/10000000000 : ℝ)*x 1 + (5432247371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294019961/10000000000 : ℝ)^4559 ≤ (44032490356529/100000000000000 : ℝ)^3535 := by
    have hnat : (5294019961 : ℕ)^4559*100000000000000^3535 ≤ 44032490356529^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294019961 10000000000 44032490356529 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1735111553/10000000000 : ℝ)^4559 ≤ (10446716487677/100000000000000 : ℝ)^3535 := by
    have hnat : (1735111553 : ℕ)^4559*100000000000000^3535 ≤ 10446716487677^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1735111553 10000000000 10446716487677 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432247371/10000000000 : ℝ)^4559 ≤ (22760396574077/50000000000000 : ℝ)^3535 := by
    have hnat : (5432247371 : ℕ)^4559*50000000000000^3535 ≤ 22760396574077^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432247371 10000000000 22760396574077 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294019961/10000000000 : ℝ), (-1735111553/10000000000 : ℝ), (5432247371/10000000000 : ℝ)] ![(44032490356529/100000000000000 : ℝ), (10446716487677/100000000000000 : ℝ), (22760396574077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294019961/10000000000 : ℝ)|^4559 ≤ (44032490356529/100000000000000 : ℝ)^3535
        have hw : |(5294019961/10000000000 : ℝ)|=(5294019961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1735111553/10000000000 : ℝ)|^4559 ≤ (10446716487677/100000000000000 : ℝ)^3535
        have hw : |(-1735111553/10000000000 : ℝ)|=(1735111553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432247371/10000000000 : ℝ)|^4559 ≤ (22760396574077/50000000000000 : ℝ)^3535
        have hw : |(5432247371/10000000000 : ℝ)|=(5432247371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s3_6 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294020081/10000000000 : ℝ)*x 0 + (271612369/500000000 : ℝ)*x 1 + (-867555687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294020081/10000000000 : ℝ)^4559 ≤ (22016245821869/50000000000000 : ℝ)^3535 := by
    have hnat : (5294020081 : ℕ)^4559*50000000000000^3535 ≤ 22016245821869^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294020081 10000000000 22016245821869 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271612369/500000000 : ℝ)^4559 ≤ (22760396622709/50000000000000 : ℝ)^3535 := by
    have hnat : (271612369 : ℕ)^4559*50000000000000^3535 ≤ 22760396622709^3535*500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271612369 500000000 22760396622709 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (867555687/5000000000 : ℝ)^4559 ≤ (1044671509777/10000000000000 : ℝ)^3535 := by
    have hnat : (867555687 : ℕ)^4559*10000000000000^3535 ≤ 1044671509777^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867555687 5000000000 1044671509777 10000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294020081/10000000000 : ℝ), (271612369/500000000 : ℝ), (-867555687/5000000000 : ℝ)] ![(22016245821869/50000000000000 : ℝ), (22760396622709/50000000000000 : ℝ), (1044671509777/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294020081/10000000000 : ℝ)|^4559 ≤ (22016245821869/50000000000000 : ℝ)^3535
        have hw : |(5294020081/10000000000 : ℝ)|=(5294020081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271612369/500000000 : ℝ)|^4559 ≤ (22760396622709/50000000000000 : ℝ)^3535
        have hw : |(271612369/500000000 : ℝ)|=(271612369/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-867555687/5000000000 : ℝ)|^4559 ≤ (1044671509777/10000000000000 : ℝ)^3535
        have hw : |(-867555687/5000000000 : ℝ)|=(867555687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s3_7 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (852165013/2000000000 : ℝ)*x 0 + (2256913233/5000000000 : ℝ)*x 1 + (4019925133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (852165013/2000000000 : ℝ)^4559 ≤ (6655756211911/20000000000000 : ℝ)^3535 := by
    have hnat : (852165013 : ℕ)^4559*20000000000000^3535 ≤ 6655756211911^3535*2000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852165013 2000000000 6655756211911 20000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2256913233/5000000000 : ℝ)^4559 ≤ (7169770363849/20000000000000 : ℝ)^3535 := by
    have hnat : (2256913233 : ℕ)^4559*20000000000000^3535 ≤ 7169770363849^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256913233 5000000000 7169770363849 20000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4019925133/10000000000 : ℝ)^4559 ≤ (30872367103907/100000000000000 : ℝ)^3535 := by
    have hnat : (4019925133 : ℕ)^4559*100000000000000^3535 ≤ 30872367103907^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4019925133 10000000000 30872367103907 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(852165013/2000000000 : ℝ), (2256913233/5000000000 : ℝ), (4019925133/10000000000 : ℝ)] ![(6655756211911/20000000000000 : ℝ), (7169770363849/20000000000000 : ℝ), (30872367103907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(852165013/2000000000 : ℝ)|^4559 ≤ (6655756211911/20000000000000 : ℝ)^3535
        have hw : |(852165013/2000000000 : ℝ)|=(852165013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2256913233/5000000000 : ℝ)|^4559 ≤ (7169770363849/20000000000000 : ℝ)^3535
        have hw : |(2256913233/5000000000 : ℝ)|=(2256913233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4019925133/10000000000 : ℝ)|^4559 ≤ (30872367103907/100000000000000 : ℝ)^3535
        have hw : |(4019925133/10000000000 : ℝ)|=(4019925133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1531_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1991/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5289/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10937/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15539/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1991/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5289/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1991/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5289/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1991/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5289/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1991/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5289/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1991/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5289/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1991/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5289/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5289/50000 : ℝ) ^ (4557/1024 : ℝ) ≤ (4554128785092203/100000000000000000000 : ℝ) := by
    have hpowers : (5289/50000 : ℝ)^4557 ≤ (4554128785092203/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5289 : ℕ)^4557*100000000000000000000^1024 ≤ 4554128785092203^1024*50000^4557 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5289 50000 4554128785092203 100000000000000000000 4557 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5289/50000 : ℝ)) (X := (4554128785092203/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1991/12500 : ℝ) ^ (4557/1024 : ℝ) ≤ (28148919000827253/100000000000000000000 : ℝ) := by
    have hpowers : (1991/12500 : ℝ)^4557 ≤ (28148919000827253/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1991 : ℕ)^4557*100000000000000000000^1024 ≤ 28148919000827253^1024*12500^4557 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1991 12500 28148919000827253 100000000000000000000 4557 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1991/12500 : ℝ)) (X := (28148919000827253/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004554128785092203/50000000000000000000 : ℝ) ≤ (5000102331868109/5000000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (50004554128785092203/50000000000000000000 : ℝ)^1024 ≤ (5000102331868109/5000000000000000 : ℝ)^4557 := by
      have hnat : (50004554128785092203 : ℕ)^1024*5000000000000000^4557 ≤ 5000102331868109^4557*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004554128785092203 50000000000000000000 5000102331868109 5000000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000102331868109/5000000000000000 : ℝ)) (X := (50004554128785092203/50000000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126021970243309983/3125000000000000000 : ℝ) ≤ (10000734774554057/10000000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (3126021970243309983/3125000000000000000 : ℝ)^1024 ≤ (10000734774554057/10000000000000000 : ℝ)^4557 := by
      have hnat : (3126021970243309983 : ℕ)^1024*10000000000000000^4557 ≤ 10000734774554057^4557*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126021970243309983 3125000000000000000 10000734774554057 10000000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000734774554057/10000000000000000 : ℝ)) (X := (3126021970243309983/3125000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028148919000827253/50000000000000000000 : ℝ) ≤ (1250158110671487/1250000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (50028148919000827253/50000000000000000000 : ℝ)^1024 ≤ (1250158110671487/1250000000000000 : ℝ)^4557 := by
      have hnat : (50028148919000827253 : ℕ)^1024*1250000000000000^4557 ≤ 1250158110671487^4557*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028148919000827253 50000000000000000000 1250158110671487 1250000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250158110671487/1250000000000000 : ℝ)) (X := (50028148919000827253/50000000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4554128785092203/100000000000000000000 : ℝ) ≤ ((835779373851977569/835937500000000000 : ℝ)+2*(530110817839/535000000000000 : ℝ)*(5289/50000 : ℝ))^(4557/1024 : ℝ) := by
    rw [show (835779373851977569/835937500000000000 : ℝ)+2*(530110817839/535000000000000 : ℝ)*(5289/50000 : ℝ)=(5000102331868109/5000000000000000 : ℝ) by norm_num, show 1+2*(4554128785092203/100000000000000000000 : ℝ)=(50004554128785092203/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28148919000827253/100000000000000000000 : ℝ)+(4554128785092203/100000000000000000000 : ℝ) ≤ ((835779373851977569/835937500000000000 : ℝ)+(530110817839/535000000000000 : ℝ)*((1991/12500 : ℝ)+(5289/50000 : ℝ)))^(4557/1024 : ℝ) := by
    rw [show (835779373851977569/835937500000000000 : ℝ)+(530110817839/535000000000000 : ℝ)*((1991/12500 : ℝ)+(5289/50000 : ℝ))=(10000734774554057/10000000000000000 : ℝ) by norm_num, show 1+(28148919000827253/100000000000000000000 : ℝ)+(4554128785092203/100000000000000000000 : ℝ)=(3126021970243309983/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28148919000827253/100000000000000000000 : ℝ) ≤ ((835779373851977569/835937500000000000 : ℝ)+2*(530110817839/535000000000000 : ℝ)*(1991/12500 : ℝ))^(4557/1024 : ℝ) := by
    rw [show (835779373851977569/835937500000000000 : ℝ)+2*(530110817839/535000000000000 : ℝ)*(1991/12500 : ℝ)=(1250158110671487/1250000000000000 : ℝ) by norm_num, show 1+2*(28148919000827253/100000000000000000000 : ℝ)=(50028148919000827253/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (835779373851977569/835937500000000000 : ℝ)*(X 1 0+X 2 0)+(530110817839/535000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (5289/50000 : ℝ)) (hi := (1991/12500 : ℝ)) (c := (835779373851977569/835937500000000000 : ℝ)) (alpha := (530110817839/535000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (835779373851977569/835937500000000000 : ℝ)*(X 0 1+X 2 1)+(530110817839/535000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (5289/50000 : ℝ)) (hi := (1991/12500 : ℝ)) (c := (835779373851977569/835937500000000000 : ℝ)) (alpha := (530110817839/535000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (835779373851977569/835937500000000000 : ℝ)*(X 0 2+X 1 2)+(530110817839/535000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (5289/50000 : ℝ)) (hi := (1991/12500 : ℝ)) (c := (835779373851977569/835937500000000000 : ℝ)) (alpha := (530110817839/535000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-367982493/2000000000 : ℝ)*X 0 0+(339587799/625000000 : ℝ)*X 0 1+(2608085037/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351205729/10000000000 : ℝ)*X 1 0+(-390237737/2000000000 : ℝ)*X 1 1+(2608085043/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337801427/2500000000 : ℝ)*X 2 0+(5216170107/10000000000 : ℝ)*X 2 1+(-487797171/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2130377857/5000000000 : ℝ)*X 0 0+(401726557/1000000000 : ℝ)*X 0 1+(2258232983/5000000000 : ℝ)*X 0 2+(2130377857/5000000000 : ℝ)*X 1 0+(401726557/1000000000 : ℝ)*X 1 1+(2258232983/5000000000 : ℝ)*X 1 2+(2130377857/5000000000 : ℝ)*X 2 0+(401726557/1000000000 : ℝ)*X 2 1+(2258232983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1839942697/10000000000 : ℝ)*X 0 0+(5217318757/10000000000 : ℝ)*X 0 1+(1086449487/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294019961/10000000000 : ℝ)*X 1 0+(-1735111553/10000000000 : ℝ)*X 1 1+(5432247371/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294020081/10000000000 : ℝ)*X 2 0+(271612369/500000000 : ℝ)*X 2 1+(-867555687/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((852165013/2000000000 : ℝ)*X 0 0+(2256913233/5000000000 : ℝ)*X 0 1+(4019925133/10000000000 : ℝ)*X 0 2+(852165013/2000000000 : ℝ)*X 1 0+(2256913233/5000000000 : ℝ)*X 1 1+(4019925133/10000000000 : ℝ)*X 1 2+(852165013/2000000000 : ℝ)*X 2 0+(2256913233/5000000000 : ℝ)*X 2 1+(4019925133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (817430579178790859646849/390625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75093723/20000000000000 : ℝ)*(base19) + (33553677/10000000000000 : ℝ)*(base23) + (11701363/100000000000000 : ℝ)*(lower2) + (85253/156250000000 : ℝ)*(upper3) + (281959/781250000000 : ℝ)*(upper5) + (1651634286783629/50000000000000 : ℝ)*(major0) + (1651634286783629/50000000000000 : ℝ)*(major1) + (1651634286783629/50000000000000 : ℝ)*(major2) + (920664463990517/20000000000000 : ℝ)*(sp0) + (575415998460509/12500000000000 : ℝ)*(sp1) + (2301664013807959/50000000000000 : ℝ)*(sp2) + (2003206000695477/100000000000000 : ℝ)*(sp3) + (3021600051/50000000000000 : ℝ)*(sp4) + (271353227/10000000000000 : ℝ)*(sp7) + (2003208714227747/100000000000000 : ℝ)*(f.failure) + (4603328363152687/100000000000000 : ℝ)*(f.sum) + (188075871839/3343750000000000000000000000 : ℝ)*base65 + (903317978775129823/83593750000000000000000000000000 : ℝ)*base68 + (26201594647004823/83593750000000000000000000000000 : ℝ)*base70 + (342248185465754823/83593750000000000000000000000000 : ℝ)*base72 + (40278630483519/13375000000000000000000000000 : ℝ)*base74 + (237517443806379823/83593750000000000000000000000000 : ℝ)*base76 + (718822268115754823/83593750000000000000000000000000 : ℝ)*base78 + (1194883229403254823/83593750000000000000000000000000 : ℝ)*base80 + (26013936550231/13375000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3925173/1250000000000000000000 : ℝ)*base89 + (3925173/1250000000000000000000 : ℝ)*base91 + (3925173/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (370055095399558705351326963/41796875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (244932593/20000000000000 : ℝ)*(base19) + (721569381/50000000000000 : ℝ)*(base23) + (44378053/25000000000000 : ℝ)*(upper3) + (28564503/100000000000000 : ℝ)*(lower4) + (160719201/100000000000000 : ℝ)*(upper5) + (1669350675059989/50000000000000 : ℝ)*(major0) + (1669350675059989/50000000000000 : ℝ)*(major1) + (1669350675059989/50000000000000 : ℝ)*(major2) + (16295383197/100000000000000 : ℝ)*(sp1) + (10881314941/50000000000000 : ℝ)*(sp2) + (4652706111185941/100000000000000 : ℝ)*(sp4) + (2326344295569889/50000000000000 : ℝ)*(sp5) + (2326341452708649/50000000000000 : ℝ)*(sp6) + (1012348146966093/50000000000000 : ℝ)*(sp7) + (1012348146966093/50000000000000 : ℝ)*(f.failure) + (4652706111185941/100000000000000 : ℝ)*(f.sum) + (2971838203763/1671875000000000000000000000 : ℝ)*base66 + (541385614610160893/83593750000000000000000000000000 : ℝ)*base68 + (376581544625785893/83593750000000000000000000000000 : ℝ)*base70 + (159567512450785893/83593750000000000000000000000000 : ℝ)*base72 + (2726434794651/3343750000000000000000000000 : ℝ)*base74 + (562757970575004643/83593750000000000000000000000000 : ℝ)*base76 + (363259008982817143/83593750000000000000000000000000 : ℝ)*base78 + (2009837002609379643/83593750000000000000000000000000 : ℝ)*base80 + (20132626870521/13375000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (7243387/625000000000000000000 : ℝ)*base89 + (7243387/625000000000000000000 : ℝ)*base91 + (7243387/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1531_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1991/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5289/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10937/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15539/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1531_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1531_s4_0 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-460065921/2500000000 : ℝ)*x 0 + (5431070961/10000000000 : ℝ)*x 1 + (5218271661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (460065921/2500000000 : ℝ)^4559 ≤ (1408784072431/12500000000000 : ℝ)^3535 := by
    have hnat : (460065921 : ℕ)^4559*12500000000000^3535 ≤ 1408784072431^3535*2500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460065921 2500000000 1408784072431 12500000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431070961/10000000000 : ℝ)^4559 ≤ (45508079928789/100000000000000 : ℝ)^3535 := by
    have hnat : (5431070961 : ℕ)^4559*100000000000000^3535 ≤ 45508079928789^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431070961 10000000000 45508079928789 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218271661/10000000000 : ℝ)^4559 ≤ (864432949417/2000000000000 : ℝ)^3535 := by
    have hnat : (5218271661 : ℕ)^4559*2000000000000^3535 ≤ 864432949417^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218271661 10000000000 864432949417 2000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-460065921/2500000000 : ℝ), (5431070961/10000000000 : ℝ), (5218271661/10000000000 : ℝ)] ![(1408784072431/12500000000000 : ℝ), (45508079928789/100000000000000 : ℝ), (864432949417/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-460065921/2500000000 : ℝ)|^4559 ≤ (1408784072431/12500000000000 : ℝ)^3535
        have hw : |(-460065921/2500000000 : ℝ)|=(460065921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431070961/10000000000 : ℝ)|^4559 ≤ (45508079928789/100000000000000 : ℝ)^3535
        have hw : |(5431070961/10000000000 : ℝ)|=(5431070961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218271661/10000000000 : ℝ)|^4559 ≤ (864432949417/2000000000000 : ℝ)^3535
        have hw : |(5218271661/10000000000 : ℝ)|=(5218271661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s4_1 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350592083/10000000000 : ℝ)*x 0 + (-1949215081/10000000000 : ℝ)*x 1 + (5218272351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350592083/10000000000 : ℝ)^4559 ≤ (44640261787331/100000000000000 : ℝ)^3535 := by
    have hnat : (5350592083 : ℕ)^4559*100000000000000^3535 ≤ 44640261787331^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350592083 10000000000 44640261787331 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1949215081/10000000000 : ℝ)^4559 ≤ (758630209823/6250000000000 : ℝ)^3535 := by
    have hnat : (1949215081 : ℕ)^4559*6250000000000^3535 ≤ 758630209823^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949215081 10000000000 758630209823 6250000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218272351/10000000000 : ℝ)^4559 ≤ (10805413710367/25000000000000 : ℝ)^3535 := by
    have hnat : (5218272351 : ℕ)^4559*25000000000000^3535 ≤ 10805413710367^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218272351 10000000000 10805413710367 25000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350592083/10000000000 : ℝ), (-1949215081/10000000000 : ℝ), (5218272351/10000000000 : ℝ)] ![(44640261787331/100000000000000 : ℝ), (758630209823/6250000000000 : ℝ), (10805413710367/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350592083/10000000000 : ℝ)|^4559 ≤ (44640261787331/100000000000000 : ℝ)^3535
        have hw : |(5350592083/10000000000 : ℝ)|=(5350592083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1949215081/10000000000 : ℝ)|^4559 ≤ (758630209823/6250000000000 : ℝ)^3535
        have hw : |(-1949215081/10000000000 : ℝ)|=(1949215081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218272351/10000000000 : ℝ)|^4559 ≤ (10805413710367/25000000000000 : ℝ)^3535
        have hw : |(5218272351/10000000000 : ℝ)|=(5218272351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s4_2 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675296501/5000000000 : ℝ)*x 0 + (2609135641/5000000000 : ℝ)*x 1 + (-1949215271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675296501/5000000000 : ℝ)^4559 ≤ (5580033959451/12500000000000 : ℝ)^3535 := by
    have hnat : (2675296501 : ℕ)^4559*12500000000000^3535 ≤ 5580033959451^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675296501 5000000000 5580033959451 12500000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609135641/5000000000 : ℝ)^4559 ≤ (43221643422351/100000000000000 : ℝ)^3535 := by
    have hnat : (2609135641 : ℕ)^4559*100000000000000^3535 ≤ 43221643422351^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609135641 5000000000 43221643422351 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1949215271/10000000000 : ℝ)^4559 ≤ (12138084883061/100000000000000 : ℝ)^3535 := by
    have hnat : (1949215271 : ℕ)^4559*100000000000000^3535 ≤ 12138084883061^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949215271 10000000000 12138084883061 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675296501/5000000000 : ℝ), (2609135641/5000000000 : ℝ), (-1949215271/10000000000 : ℝ)] ![(5580033959451/12500000000000 : ℝ), (43221643422351/100000000000000 : ℝ), (12138084883061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675296501/5000000000 : ℝ)|^4559 ≤ (5580033959451/12500000000000 : ℝ)^3535
        have hw : |(2675296501/5000000000 : ℝ)|=(2675296501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609135641/5000000000 : ℝ)|^4559 ≤ (43221643422351/100000000000000 : ℝ)^3535
        have hw : |(2609135641/5000000000 : ℝ)|=(2609135641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1949215271/10000000000 : ℝ)|^4559 ≤ (12138084883061/100000000000000 : ℝ)^3535
        have hw : |(-1949215271/10000000000 : ℝ)|=(1949215271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s4_3 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2130489349/5000000000 : ℝ)*x 0 + (4022335321/10000000000 : ℝ)*x 1 + (4511344353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130489349/5000000000 : ℝ)^4559 ≤ (8320082148799/25000000000000 : ℝ)^3535 := by
    have hnat : (2130489349 : ℕ)^4559*25000000000000^3535 ≤ 8320082148799^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130489349 5000000000 8320082148799 25000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4022335321/10000000000 : ℝ)^4559 ≤ (30896240860707/100000000000000 : ℝ)^3535 := by
    have hnat : (4022335321 : ℕ)^4559*100000000000000^3535 ≤ 30896240860707^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022335321 10000000000 30896240860707 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4511344353/10000000000 : ℝ)^4559 ≤ (8955857633263/25000000000000 : ℝ)^3535 := by
    have hnat : (4511344353 : ℕ)^4559*25000000000000^3535 ≤ 8955857633263^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511344353 10000000000 8955857633263 25000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2130489349/5000000000 : ℝ), (4022335321/10000000000 : ℝ), (4511344353/10000000000 : ℝ)] ![(8320082148799/25000000000000 : ℝ), (30896240860707/100000000000000 : ℝ), (8955857633263/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2130489349/5000000000 : ℝ)|^4559 ≤ (8320082148799/25000000000000 : ℝ)^3535
        have hw : |(2130489349/5000000000 : ℝ)|=(2130489349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4022335321/10000000000 : ℝ)|^4559 ≤ (30896240860707/100000000000000 : ℝ)^3535
        have hw : |(4022335321/10000000000 : ℝ)|=(4022335321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4511344353/10000000000 : ℝ)|^4559 ≤ (8955857633263/25000000000000 : ℝ)^3535
        have hw : |(4511344353/10000000000 : ℝ)|=(4511344353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s4_4 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-73611673/400000000 : ℝ)*x 0 + (260968699/500000000 : ℝ)*x 1 + (2714980349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (73611673/400000000 : ℝ)^4559 ≤ (2817623711617/25000000000000 : ℝ)^3535 := by
    have hnat : (73611673 : ℕ)^4559*25000000000000^3535 ≤ 2817623711617^3535*400000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73611673 400000000 2817623711617 25000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260968699/500000000 : ℝ)^4559 ≤ (4323342286319/10000000000000 : ℝ)^3535 := by
    have hnat : (260968699 : ℕ)^4559*10000000000000^3535 ≤ 4323342286319^3535*500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260968699 500000000 4323342286319 10000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714980349/5000000000 : ℝ)^4559 ≤ (22748041139009/50000000000000 : ℝ)^3535 := by
    have hnat : (2714980349 : ℕ)^4559*50000000000000^3535 ≤ 22748041139009^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714980349 5000000000 22748041139009 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-73611673/400000000 : ℝ), (260968699/500000000 : ℝ), (2714980349/5000000000 : ℝ)] ![(2817623711617/25000000000000 : ℝ), (4323342286319/10000000000000 : ℝ), (22748041139009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-73611673/400000000 : ℝ)|^4559 ≤ (2817623711617/25000000000000 : ℝ)^3535
        have hw : |(-73611673/400000000 : ℝ)|=(73611673/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260968699/500000000 : ℝ)|^4559 ≤ (4323342286319/10000000000000 : ℝ)^3535
        have hw : |(260968699/500000000 : ℝ)|=(260968699/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714980349/5000000000 : ℝ)|^4559 ≤ (22748041139009/50000000000000 : ℝ)^3535
        have hw : |(2714980349/5000000000 : ℝ)|=(2714980349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s4_5 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058915151/2000000000 : ℝ)*x 0 + (-86876283/500000000 : ℝ)*x 1 + (5429960697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058915151/2000000000 : ℝ)^4559 ≤ (22019226153103/50000000000000 : ℝ)^3535 := by
    have hnat : (1058915151 : ℕ)^4559*50000000000000^3535 ≤ 22019226153103^3535*2000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058915151 2000000000 22019226153103 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86876283/500000000 : ℝ)^4559 ≤ (10465465421501/100000000000000 : ℝ)^3535 := by
    have hnat : (86876283 : ℕ)^4559*100000000000000^3535 ≤ 10465465421501^3535*500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86876283 500000000 10465465421501 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429960697/10000000000 : ℝ)^4559 ≤ (11374020566803/25000000000000 : ℝ)^3535 := by
    have hnat : (5429960697 : ℕ)^4559*25000000000000^3535 ≤ 11374020566803^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429960697 10000000000 11374020566803 25000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058915151/2000000000 : ℝ), (-86876283/500000000 : ℝ), (5429960697/10000000000 : ℝ)] ![(22019226153103/50000000000000 : ℝ), (10465465421501/100000000000000 : ℝ), (11374020566803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058915151/2000000000 : ℝ)|^4559 ≤ (22019226153103/50000000000000 : ℝ)^3535
        have hw : |(1058915151/2000000000 : ℝ)|=(1058915151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-86876283/500000000 : ℝ)|^4559 ≤ (10465465421501/100000000000000 : ℝ)^3535
        have hw : |(-86876283/500000000 : ℝ)|=(86876283/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429960697/10000000000 : ℝ)|^4559 ≤ (11374020566803/25000000000000 : ℝ)^3535
        have hw : |(5429960697/10000000000 : ℝ)|=(5429960697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s4_6 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647287877/5000000000 : ℝ)*x 0 + (678745087/1250000000 : ℝ)*x 1 + (-868762831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647287877/5000000000 : ℝ)^4559 ≤ (44038452295479/100000000000000 : ℝ)^3535 := by
    have hnat : (2647287877 : ℕ)^4559*100000000000000^3535 ≤ 44038452295479^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647287877 5000000000 44038452295479 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678745087/1250000000 : ℝ)^4559 ≤ (22748041128203/50000000000000 : ℝ)^3535 := by
    have hnat : (678745087 : ℕ)^4559*50000000000000^3535 ≤ 22748041128203^3535*1250000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678745087 1250000000 22748041128203 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (868762831/5000000000 : ℝ)^4559 ≤ (10465465437037/100000000000000 : ℝ)^3535 := by
    have hnat : (868762831 : ℕ)^4559*100000000000000^3535 ≤ 10465465437037^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868762831 5000000000 10465465437037 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647287877/5000000000 : ℝ), (678745087/1250000000 : ℝ), (-868762831/5000000000 : ℝ)] ![(44038452295479/100000000000000 : ℝ), (22748041128203/50000000000000 : ℝ), (10465465437037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647287877/5000000000 : ℝ)|^4559 ≤ (44038452295479/100000000000000 : ℝ)^3535
        have hw : |(2647287877/5000000000 : ℝ)|=(2647287877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678745087/1250000000 : ℝ)|^4559 ≤ (22748041128203/50000000000000 : ℝ)^3535
        have hw : |(678745087/1250000000 : ℝ)|=(678745087/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-868762831/5000000000 : ℝ)|^4559 ≤ (10465465437037/100000000000000 : ℝ)^3535
        have hw : |(-868762831/5000000000 : ℝ)|=(868762831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s4_7 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4261042519/10000000000 : ℝ)*x 0 + (2254405859/5000000000 : ℝ)*x 1 + (2012444099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4261042519/10000000000 : ℝ)^4559 ≤ (16640485732453/50000000000000 : ℝ)^3535 := by
    have hnat : (4261042519 : ℕ)^4559*50000000000000^3535 ≤ 16640485732453^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4261042519 10000000000 16640485732453 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254405859/5000000000 : ℝ)^4559 ≤ (35797495986813/100000000000000 : ℝ)^3535 := by
    have hnat : (2254405859 : ℕ)^4559*100000000000000^3535 ≤ 35797495986813^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254405859 5000000000 35797495986813 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2012444099/5000000000 : ℝ)^4559 ≤ (3865191565189/12500000000000 : ℝ)^3535 := by
    have hnat : (2012444099 : ℕ)^4559*12500000000000^3535 ≤ 3865191565189^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012444099 5000000000 3865191565189 12500000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4261042519/10000000000 : ℝ), (2254405859/5000000000 : ℝ), (2012444099/5000000000 : ℝ)] ![(16640485732453/50000000000000 : ℝ), (35797495986813/100000000000000 : ℝ), (3865191565189/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4261042519/10000000000 : ℝ)|^4559 ≤ (16640485732453/50000000000000 : ℝ)^3535
        have hw : |(4261042519/10000000000 : ℝ)|=(4261042519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254405859/5000000000 : ℝ)|^4559 ≤ (35797495986813/100000000000000 : ℝ)^3535
        have hw : |(2254405859/5000000000 : ℝ)|=(2254405859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2012444099/5000000000 : ℝ)|^4559 ≤ (3865191565189/12500000000000 : ℝ)^3535
        have hw : |(2012444099/5000000000 : ℝ)|=(2012444099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1531_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15539/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10937/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5491/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15539/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10937/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15539/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10937/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15539/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10937/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15539/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10937/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15539/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10937/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15539/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10937/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10937/100000 : ℝ) ^ (4557/1024 : ℝ) ≤ (1320837338415517/25000000000000000000 : ℝ) := by
    have hpowers : (10937/100000 : ℝ)^4557 ≤ (1320837338415517/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10937 : ℕ)^4557*25000000000000000000^1024 ≤ 1320837338415517^1024*100000^4557 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10937 100000 1320837338415517 25000000000000000000 4557 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10937/100000 : ℝ)) (X := (1320837338415517/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15539/100000 : ℝ) ^ (4557/1024 : ℝ) ≤ (6303978600841451/25000000000000000000 : ℝ) := by
    have hpowers : (15539/100000 : ℝ)^4557 ≤ (6303978600841451/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15539 : ℕ)^4557*25000000000000000000^1024 ≤ 6303978600841451^1024*100000^4557 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15539 100000 6303978600841451 25000000000000000000 4557 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15539/100000 : ℝ)) (X := (6303978600841451/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501320837338415517/12500000000000000000 : ℝ) ≤ (2000047486751329/2000000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (12501320837338415517/12500000000000000000 : ℝ)^1024 ≤ (2000047486751329/2000000000000000 : ℝ)^4557 := by
      have hnat : (12501320837338415517 : ℕ)^1024*2000000000000000^4557 ≤ 2000047486751329^4557*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501320837338415517 12500000000000000000 2000047486751329 2000000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000047486751329/2000000000000000 : ℝ)) (X := (12501320837338415517/12500000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125953101992407121/3125000000000000000 : ℝ) ≤ (10000685265620253/10000000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (3125953101992407121/3125000000000000000 : ℝ)^1024 ≤ (10000685265620253/10000000000000000 : ℝ)^4557 := by
      have hnat : (3125953101992407121 : ℕ)^1024*10000000000000000^4557 ≤ 10000685265620253^4557*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125953101992407121 3125000000000000000 10000685265620253 10000000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000685265620253/10000000000000000 : ℝ)) (X := (3125953101992407121/3125000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506303978600841451/12500000000000000000 : ℝ) ≤ (10001133097483861/10000000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (12506303978600841451/12500000000000000000 : ℝ)^1024 ≤ (10001133097483861/10000000000000000 : ℝ)^4557 := by
      have hnat : (12506303978600841451 : ℕ)^1024*10000000000000000^4557 ≤ 10001133097483861^4557*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506303978600841451 12500000000000000000 10001133097483861 10000000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001133097483861/10000000000000000 : ℝ)) (X := (12506303978600841451/12500000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1320837338415517/25000000000000000000 : ℝ) ≤ ((23005648397981759449/23010000000000000000 : ℝ)+2*(55978982951/57525000000000 : ℝ)*(10937/100000 : ℝ))^(4557/1024 : ℝ) := by
    rw [show (23005648397981759449/23010000000000000000 : ℝ)+2*(55978982951/57525000000000 : ℝ)*(10937/100000 : ℝ)=(2000047486751329/2000000000000000 : ℝ) by norm_num, show 1+2*(1320837338415517/25000000000000000000 : ℝ)=(12501320837338415517/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6303978600841451/25000000000000000000 : ℝ)+(1320837338415517/25000000000000000000 : ℝ) ≤ ((23005648397981759449/23010000000000000000 : ℝ)+(55978982951/57525000000000 : ℝ)*((15539/100000 : ℝ)+(10937/100000 : ℝ)))^(4557/1024 : ℝ) := by
    rw [show (23005648397981759449/23010000000000000000 : ℝ)+(55978982951/57525000000000 : ℝ)*((15539/100000 : ℝ)+(10937/100000 : ℝ))=(10000685265620253/10000000000000000 : ℝ) by norm_num, show 1+(6303978600841451/25000000000000000000 : ℝ)+(1320837338415517/25000000000000000000 : ℝ)=(3125953101992407121/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6303978600841451/25000000000000000000 : ℝ) ≤ ((23005648397981759449/23010000000000000000 : ℝ)+2*(55978982951/57525000000000 : ℝ)*(15539/100000 : ℝ))^(4557/1024 : ℝ) := by
    rw [show (23005648397981759449/23010000000000000000 : ℝ)+2*(55978982951/57525000000000 : ℝ)*(15539/100000 : ℝ)=(10001133097483861/10000000000000000 : ℝ) by norm_num, show 1+2*(6303978600841451/25000000000000000000 : ℝ)=(12506303978600841451/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23005648397981759449/23010000000000000000 : ℝ)*(X 1 0+X 2 0)+(55978982951/57525000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (10937/100000 : ℝ)) (hi := (15539/100000 : ℝ)) (c := (23005648397981759449/23010000000000000000 : ℝ)) (alpha := (55978982951/57525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23005648397981759449/23010000000000000000 : ℝ)*(X 0 1+X 2 1)+(55978982951/57525000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (10937/100000 : ℝ)) (hi := (15539/100000 : ℝ)) (c := (23005648397981759449/23010000000000000000 : ℝ)) (alpha := (55978982951/57525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23005648397981759449/23010000000000000000 : ℝ)*(X 0 2+X 1 2)+(55978982951/57525000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (10937/100000 : ℝ)) (hi := (15539/100000 : ℝ)) (c := (23005648397981759449/23010000000000000000 : ℝ)) (alpha := (55978982951/57525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-460065921/2500000000 : ℝ)*X 0 0+(5431070961/10000000000 : ℝ)*X 0 1+(5218271661/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350592083/10000000000 : ℝ)*X 1 0+(-1949215081/10000000000 : ℝ)*X 1 1+(5218272351/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675296501/5000000000 : ℝ)*X 2 0+(2609135641/5000000000 : ℝ)*X 2 1+(-1949215271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2130489349/5000000000 : ℝ)*X 0 0+(4022335321/10000000000 : ℝ)*X 0 1+(4511344353/10000000000 : ℝ)*X 0 2+(2130489349/5000000000 : ℝ)*X 1 0+(4022335321/10000000000 : ℝ)*X 1 1+(4511344353/10000000000 : ℝ)*X 1 2+(2130489349/5000000000 : ℝ)*X 2 0+(4022335321/10000000000 : ℝ)*X 2 1+(4511344353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-73611673/400000000 : ℝ)*X 0 0+(260968699/500000000 : ℝ)*X 0 1+(2714980349/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058915151/2000000000 : ℝ)*X 1 0+(-86876283/500000000 : ℝ)*X 1 1+(5429960697/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647287877/5000000000 : ℝ)*X 2 0+(678745087/1250000000 : ℝ)*X 2 1+(-868762831/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4261042519/10000000000 : ℝ)*X 0 0+(2254405859/5000000000 : ℝ)*X 0 1+(2012444099/5000000000 : ℝ)*X 0 2+(4261042519/10000000000 : ℝ)*X 1 0+(2254405859/5000000000 : ℝ)*X 1 1+(2012444099/5000000000 : ℝ)*X 1 2+(4261042519/10000000000 : ℝ)*X 2 0+(2254405859/5000000000 : ℝ)*X 2 1+(2012444099/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9052502510850172439927/3835000000000000000000000000 : ℝ) := by norm_num
    linear_combination (248180943/50000000000000 : ℝ)*(base23) + (165854209/100000000000000 : ℝ)*(lower2) + (324248891/100000000000000 : ℝ)*(upper3) + (10649123/50000000000000 : ℝ)*(lower4) + (232435929/100000000000000 : ℝ)*(upper5) + (421513369136419/12500000000000 : ℝ)*(major0) + (421513369136419/12500000000000 : ℝ)*(major1) + (421513369136419/12500000000000 : ℝ)*(major2) + (939851859474617/20000000000000 : ℝ)*(sp0) + (939851859474617/20000000000000 : ℝ)*(sp1) + (1174813730778053/25000000000000 : ℝ)*(sp2) + (2044951396344357/100000000000000 : ℝ)*(sp3) + (3877898987/100000000000000 : ℝ)*(sp6) + (1566891027/50000000000000 : ℝ)*(sp7) + (2044954530126411/100000000000000 : ℝ)*(f.failure) + (939851859474617/20000000000000 : ℝ)*(f.sum) + (3980051406169/1438125000000000000000000000 : ℝ)*base66 + (290717901801374377/95875000000000000000000000000000 : ℝ)*base67 + (246367867507874377/95875000000000000000000000000000 : ℝ)*base69 + (913723311120000623/95875000000000000000000000000000 : ℝ)*base72 + (19335994588897/2876250000000000000000000000 : ℝ)*base73 + (250976854310875623/95875000000000000000000000000000 : ℝ)*base76 + (1040375678606125623/95875000000000000000000000000000 : ℝ)*base78 + (205885204161749377/95875000000000000000000000000000 : ℝ)*base79 + (56601344834173/11505000000000000000000000000 : ℝ)*base81 + (1086451/1250000000000000000000 : ℝ)*base90 + (1086451/1250000000000000000000 : ℝ)*base92 + (1086451/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2113210485931617777908716849/383500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (222651379/25000000000000 : ℝ)*(base19) + (481291581/50000000000000 : ℝ)*(base23) + (56713383/50000000000000 : ℝ)*(upper3) + (4171087/12500000000000 : ℝ)*(lower4) + (14314059/12500000000000 : ℝ)*(upper5) + (3407539620612601/100000000000000 : ℝ)*(major0) + (3407539620612601/100000000000000 : ℝ)*(major1) + (3407539620612601/100000000000000 : ℝ)*(major2) + (692311593/5000000000000 : ℝ)*(sp1) + (7388508667/50000000000000 : ℝ)*(sp2) + (4748637013836977/100000000000000 : ℝ)*(sp4) + (11871555692499/250000000000 : ℝ)*(sp5) + (4748621274236481/100000000000000 : ℝ)*(sp6) + (1033221021855323/50000000000000 : ℝ)*(sp7) + (1033221021855323/50000000000000 : ℝ)*(f.failure) + (4748637013836977/100000000000000 : ℝ)*(f.sum) + (12849644477459/11505000000000000000000000000 : ℝ)*base65 + (908067557089127717/767000000000000000000000000000000 : ℝ)*base68 + (4099920850211127717/767000000000000000000000000000000 : ℝ)*base70 + (6740754525188872283/767000000000000000000000000000000 : ℝ)*base71 + (167644741091/2876250000000000000000000000 : ℝ)*base73 + (4821137364350872283/767000000000000000000000000000000 : ℝ)*base75 + (235046017665127717/767000000000000000000000000000000 : ℝ)*base78 + (257724041657127717/767000000000000000000000000000000 : ℝ)*base80 + (5143996186291/719062500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (7486957/625000000000000000000 : ℝ)*base89 + (7486957/625000000000000000000 : ℝ)*base91 + (7486957/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1531_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15539/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10937/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5491/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1531_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1531_s5_0 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-230038077/1250000000 : ℝ)*x 0 + (2715400413/5000000000 : ℝ)*x 1 + (2609257337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (230038077/1250000000 : ℝ)^4559 ≤ (2254119174877/20000000000000 : ℝ)^3535 := by
    have hnat : (230038077 : ℕ)^4559*20000000000000^3535 ≤ 2254119174877^3535*1250000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230038077 1250000000 2254119174877 20000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715400413/5000000000 : ℝ)^4559 ≤ (45505160748369/100000000000000 : ℝ)^3535 := by
    have hnat : (2715400413 : ℕ)^4559*100000000000000^3535 ≤ 45505160748369^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715400413 5000000000 45505160748369 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609257337/5000000000 : ℝ)^4559 ≤ (4322424336657/10000000000000 : ℝ)^3535 := by
    have hnat : (2609257337 : ℕ)^4559*10000000000000^3535 ≤ 4322424336657^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609257337 5000000000 4322424336657 10000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-230038077/1250000000 : ℝ), (2715400413/5000000000 : ℝ), (2609257337/5000000000 : ℝ)] ![(2254119174877/20000000000000 : ℝ), (45505160748369/100000000000000 : ℝ), (4322424336657/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-230038077/1250000000 : ℝ)|^4559 ≤ (2254119174877/20000000000000 : ℝ)^3535
        have hw : |(-230038077/1250000000 : ℝ)|=(230038077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715400413/5000000000 : ℝ)|^4559 ≤ (45505160748369/100000000000000 : ℝ)^3535
        have hw : |(2715400413/5000000000 : ℝ)|=(2715400413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609257337/5000000000 : ℝ)|^4559 ≤ (4322424336657/10000000000000 : ℝ)^3535
        have hw : |(2609257337/5000000000 : ℝ)|=(2609257337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s5_1 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675260883/5000000000 : ℝ)*x 0 + (-243623373/1250000000 : ℝ)*x 1 + (5218514663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675260883/5000000000 : ℝ)^4559 ≤ (44639505190407/100000000000000 : ℝ)^3535 := by
    have hnat : (2675260883 : ℕ)^4559*100000000000000^3535 ≤ 44639505190407^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675260883 5000000000 44639505190407 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243623373/1250000000 : ℝ)^4559 ≤ (12136251537409/100000000000000 : ℝ)^3535 := by
    have hnat : (243623373 : ℕ)^4559*100000000000000^3535 ≤ 12136251537409^3535*1250000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243623373 1250000000 12136251537409 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218514663/10000000000 : ℝ)^4559 ≤ (21612121624533/50000000000000 : ℝ)^3535 := by
    have hnat : (5218514663 : ℕ)^4559*50000000000000^3535 ≤ 21612121624533^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218514663 10000000000 21612121624533 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675260883/5000000000 : ℝ), (-243623373/1250000000 : ℝ), (5218514663/10000000000 : ℝ)] ![(44639505190407/100000000000000 : ℝ), (12136251537409/100000000000000 : ℝ), (21612121624533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675260883/5000000000 : ℝ)|^4559 ≤ (44639505190407/100000000000000 : ℝ)^3535
        have hw : |(2675260883/5000000000 : ℝ)|=(2675260883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-243623373/1250000000 : ℝ)|^4559 ≤ (12136251537409/100000000000000 : ℝ)^3535
        have hw : |(-243623373/1250000000 : ℝ)|=(243623373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218514663/10000000000 : ℝ)|^4559 ≤ (21612121624533/50000000000000 : ℝ)^3535
        have hw : |(5218514663/10000000000 : ℝ)|=(5218514663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s5_2 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350521783/10000000000 : ℝ)*x 0 + (5218514657/10000000000 : ℝ)*x 1 + (-1948986971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350521783/10000000000 : ℝ)^4559 ≤ (11159876343331/25000000000000 : ℝ)^3535 := by
    have hnat : (5350521783 : ℕ)^4559*25000000000000^3535 ≤ 11159876343331^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350521783 10000000000 11159876343331 25000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218514657/10000000000 : ℝ)^4559 ≤ (43224243184973/100000000000000 : ℝ)^3535 := by
    have hnat : (5218514657 : ℕ)^4559*100000000000000^3535 ≤ 43224243184973^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218514657 10000000000 43224243184973 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1948986971/10000000000 : ℝ)^4559 ≤ (12136251433009/100000000000000 : ℝ)^3535 := by
    have hnat : (1948986971 : ℕ)^4559*100000000000000^3535 ≤ 12136251433009^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948986971 10000000000 12136251433009 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350521783/10000000000 : ℝ), (5218514657/10000000000 : ℝ), (-1948986971/10000000000 : ℝ)] ![(11159876343331/25000000000000 : ℝ), (43224243184973/100000000000000 : ℝ), (12136251433009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350521783/10000000000 : ℝ)|^4559 ≤ (11159876343331/25000000000000 : ℝ)^3535
        have hw : |(5350521783/10000000000 : ℝ)|=(5350521783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218514657/10000000000 : ℝ)|^4559 ≤ (43224243184973/100000000000000 : ℝ)^3535
        have hw : |(5218514657/10000000000 : ℝ)|=(5218514657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1948986971/10000000000 : ℝ)|^4559 ≤ (12136251433009/100000000000000 : ℝ)^3535
        have hw : |(-1948986971/10000000000 : ℝ)|=(1948986971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s5_3 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2130501253/5000000000 : ℝ)*x 0 + (2011461673/5000000000 : ℝ)*x 1 + (1127688027/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130501253/5000000000 : ℝ)^4559 ≤ (4160071051643/12500000000000 : ℝ)^3535 := by
    have hnat : (2130501253 : ℕ)^4559*12500000000000^3535 ≤ 4160071051643^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130501253 5000000000 4160071051643 12500000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2011461673/5000000000 : ℝ)^4559 ≤ (6180413216671/20000000000000 : ℝ)^3535 := by
    have hnat : (2011461673 : ℕ)^4559*20000000000000^3535 ≤ 6180413216671^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011461673 5000000000 6180413216671 20000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127688027/2500000000 : ℝ)^4559 ≤ (35817365481269/100000000000000 : ℝ)^3535 := by
    have hnat : (1127688027 : ℕ)^4559*100000000000000^3535 ≤ 35817365481269^3535*2500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127688027 2500000000 35817365481269 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2130501253/5000000000 : ℝ), (2011461673/5000000000 : ℝ), (1127688027/2500000000 : ℝ)] ![(4160071051643/12500000000000 : ℝ), (6180413216671/20000000000000 : ℝ), (35817365481269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2130501253/5000000000 : ℝ)|^4559 ≤ (4160071051643/12500000000000 : ℝ)^3535
        have hw : |(2130501253/5000000000 : ℝ)|=(2130501253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2011461673/5000000000 : ℝ)|^4559 ≤ (6180413216671/20000000000000 : ℝ)^3535
        have hw : |(2011461673/5000000000 : ℝ)|=(2011461673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127688027/2500000000 : ℝ)|^4559 ≤ (35817365481269/100000000000000 : ℝ)^3535
        have hw : |(1127688027/2500000000 : ℝ)|=(1127688027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s5_4 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1840332797/10000000000 : ℝ)*x 0 + (1304902961/2500000000 : ℝ)*x 1 + (678711949/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1840332797/10000000000 : ℝ)^4559 ≤ (11270818458773/100000000000000 : ℝ)^3535 := by
    have hnat : (1840332797 : ℕ)^4559*100000000000000^3535 ≤ 11270818458773^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840332797 10000000000 11270818458773 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304902961/2500000000 : ℝ)^4559 ≤ (43235963911741/100000000000000 : ℝ)^3535 := by
    have hnat : (1304902961 : ℕ)^4559*100000000000000^3535 ≤ 43235963911741^3535*2500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304902961 2500000000 43235963911741 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678711949/1250000000 : ℝ)^4559 ≤ (2843326100759/6250000000000 : ℝ)^3535 := by
    have hnat : (678711949 : ℕ)^4559*6250000000000^3535 ≤ 2843326100759^3535*1250000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678711949 1250000000 2843326100759 6250000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1840332797/10000000000 : ℝ), (1304902961/2500000000 : ℝ), (678711949/1250000000 : ℝ)] ![(11270818458773/100000000000000 : ℝ), (43235963911741/100000000000000 : ℝ), (2843326100759/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1840332797/10000000000 : ℝ)|^4559 ≤ (11270818458773/100000000000000 : ℝ)^3535
        have hw : |(-1840332797/10000000000 : ℝ)|=(1840332797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304902961/2500000000 : ℝ)|^4559 ≤ (43235963911741/100000000000000 : ℝ)^3535
        have hw : |(1304902961/2500000000 : ℝ)|=(1304902961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678711949/1250000000 : ℝ)|^4559 ≤ (2843326100759/6250000000000 : ℝ)^3535
        have hw : |(678711949/1250000000 : ℝ)|=(678711949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s5_5 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647319869/5000000000 : ℝ)*x 0 + (-347561221/2000000000 : ℝ)*x 1 + (5429695569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647319869/5000000000 : ℝ)^4559 ≤ (44039138657433/100000000000000 : ℝ)^3535 := by
    have hnat : (2647319869 : ℕ)^4559*100000000000000^3535 ≤ 44039138657433^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647319869 5000000000 44039138657433 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (347561221/2000000000 : ℝ)^4559 ≤ (2093528792109/20000000000000 : ℝ)^3535 := by
    have hnat : (347561221 : ℕ)^4559*20000000000000^3535 ≤ 2093528792109^3535*2000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347561221 2000000000 2093528792109 20000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429695569/10000000000 : ℝ)^4559 ≤ (22746608681807/50000000000000 : ℝ)^3535 := by
    have hnat : (5429695569 : ℕ)^4559*50000000000000^3535 ≤ 22746608681807^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429695569 10000000000 22746608681807 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647319869/5000000000 : ℝ), (-347561221/2000000000 : ℝ), (5429695569/10000000000 : ℝ)] ![(44039138657433/100000000000000 : ℝ), (2093528792109/20000000000000 : ℝ), (22746608681807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647319869/5000000000 : ℝ)|^4559 ≤ (44039138657433/100000000000000 : ℝ)^3535
        have hw : |(2647319869/5000000000 : ℝ)|=(2647319869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-347561221/2000000000 : ℝ)|^4559 ≤ (2093528792109/20000000000000 : ℝ)^3535
        have hw : |(-347561221/2000000000 : ℝ)|=(347561221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429695569/10000000000 : ℝ)|^4559 ≤ (22746608681807/50000000000000 : ℝ)^3535
        have hw : |(5429695569/10000000000 : ℝ)|=(5429695569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s5_6 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264731987/500000000 : ℝ)*x 0 + (5429695591/10000000000 : ℝ)*x 1 + (-1737806073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264731987/500000000 : ℝ)^4559 ≤ (44039138678887/100000000000000 : ℝ)^3535 := by
    have hnat : (264731987 : ℕ)^4559*100000000000000^3535 ≤ 44039138678887^3535*500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264731987 500000000 44039138678887 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429695591/10000000000 : ℝ)^4559 ≤ (45493217601339/100000000000000 : ℝ)^3535 := by
    have hnat : (5429695591 : ℕ)^4559*100000000000000^3535 ≤ 45493217601339^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429695591 10000000000 45493217601339 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1737806073/10000000000 : ℝ)^4559 ≤ (5233821855979/50000000000000 : ℝ)^3535 := by
    have hnat : (1737806073 : ℕ)^4559*50000000000000^3535 ≤ 5233821855979^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1737806073 10000000000 5233821855979 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264731987/500000000 : ℝ), (5429695591/10000000000 : ℝ), (-1737806073/10000000000 : ℝ)] ![(44039138678887/100000000000000 : ℝ), (45493217601339/100000000000000 : ℝ), (5233821855979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264731987/500000000 : ℝ)|^4559 ≤ (44039138678887/100000000000000 : ℝ)^3535
        have hw : |(264731987/500000000 : ℝ)|=(264731987/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429695591/10000000000 : ℝ)|^4559 ≤ (45493217601339/100000000000000 : ℝ)^3535
        have hw : |(5429695591/10000000000 : ℝ)|=(5429695591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1737806073/10000000000 : ℝ)|^4559 ≤ (5233821855979/50000000000000 : ℝ)^3535
        have hw : |(-1737806073/10000000000 : ℝ)|=(1737806073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s5_7 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4261067431/10000000000 : ℝ)*x 0 + (4508230841/10000000000 : ℝ)*x 1 + (1006365787/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4261067431/10000000000 : ℝ)^4559 ≤ (16640611202271/50000000000000 : ℝ)^3535 := by
    have hnat : (4261067431 : ℕ)^4559*50000000000000^3535 ≤ 16640611202271^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4261067431 10000000000 16640611202271 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508230841/10000000000 : ℝ)^4559 ≤ (7158309663539/20000000000000 : ℝ)^3535 := by
    have hnat : (4508230841 : ℕ)^4559*20000000000000^3535 ≤ 7158309663539^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508230841 10000000000 7158309663539 20000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006365787/2500000000 : ℝ)^4559 ≤ (7731807315469/25000000000000 : ℝ)^3535 := by
    have hnat : (1006365787 : ℕ)^4559*25000000000000^3535 ≤ 7731807315469^3535*2500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006365787 2500000000 7731807315469 25000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4261067431/10000000000 : ℝ), (4508230841/10000000000 : ℝ), (1006365787/2500000000 : ℝ)] ![(16640611202271/50000000000000 : ℝ), (7158309663539/20000000000000 : ℝ), (7731807315469/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4261067431/10000000000 : ℝ)|^4559 ≤ (16640611202271/50000000000000 : ℝ)^3535
        have hw : |(4261067431/10000000000 : ℝ)|=(4261067431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508230841/10000000000 : ℝ)|^4559 ≤ (7158309663539/20000000000000 : ℝ)^3535
        have hw : |(4508230841/10000000000 : ℝ)|=(4508230841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1006365787/2500000000 : ℝ)|^4559 ≤ (7731807315469/25000000000000 : ℝ)^3535
        have hw : |(1006365787/2500000000 : ℝ)|=(1006365787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1531_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5491/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10987/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (5491/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5491/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5491/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5491/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5491/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5491/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5491/50000 : ℝ) ^ (4557/1024 : ℝ) ≤ (1345194388491139/25000000000000000000 : ℝ) := by
    have hpowers : (5491/50000 : ℝ)^4557 ≤ (1345194388491139/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5491 : ℕ)^4557*25000000000000000000^1024 ≤ 1345194388491139^1024*50000^4557 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5491 50000 1345194388491139 25000000000000000000 4557 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5491/50000 : ℝ)) (X := (1345194388491139/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4557/1024 : ℝ) ≤ (24863978177188473/100000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4557 ≤ (24863978177188473/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4557*100000000000000000000^1024 ≤ 24863978177188473^1024*10000^4557 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 24863978177188473 100000000000000000000 4557 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (24863978177188473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501345194388491139/12500000000000000000 : ℝ) ≤ (2000048362399601/2000000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (12501345194388491139/12500000000000000000 : ℝ)^1024 ≤ (2000048362399601/2000000000000000 : ℝ)^4557 := by
      have hnat : (12501345194388491139 : ℕ)^1024*2000000000000000^4557 ≤ 2000048362399601^4557*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501345194388491139 12500000000000000000 2000048362399601 2000000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000048362399601/2000000000000000 : ℝ)) (X := (12501345194388491139/12500000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030244755731153029/100000000000000000000 : ℝ) ≤ (1250084943492011/1250000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (100030244755731153029/100000000000000000000 : ℝ)^1024 ≤ (1250084943492011/1250000000000000 : ℝ)^4557 := by
      have hnat : (100030244755731153029 : ℕ)^1024*1250000000000000^4557 ≤ 1250084943492011^4557*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030244755731153029 100000000000000000000 1250084943492011 1250000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250084943492011/1250000000000000 : ℝ)) (X := (100030244755731153029/100000000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024863978177188473/50000000000000000000 : ℝ) ≤ (10001117283874171/10000000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (50024863978177188473/50000000000000000000 : ℝ)^1024 ≤ (10001117283874171/10000000000000000 : ℝ)^4557 := by
      have hnat : (50024863978177188473 : ℕ)^1024*10000000000000000^4557 ≤ 10001117283874171^4557*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024863978177188473 50000000000000000000 10001117283874171 10000000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001117283874171/10000000000000000 : ℝ)) (X := (50024863978177188473/50000000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1345194388491139/25000000000000000000 : ℝ) ≤ ((5633934457042868941/5635000000000000000 : ℝ)+2*(437735938083/450800000000000 : ℝ)*(5491/50000 : ℝ))^(4557/1024 : ℝ) := by
    rw [show (5633934457042868941/5635000000000000000 : ℝ)+2*(437735938083/450800000000000 : ℝ)*(5491/50000 : ℝ)=(2000048362399601/2000000000000000 : ℝ) by norm_num, show 1+2*(1345194388491139/25000000000000000000 : ℝ)=(12501345194388491139/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24863978177188473/100000000000000000000 : ℝ)+(1345194388491139/25000000000000000000 : ℝ) ≤ ((5633934457042868941/5635000000000000000 : ℝ)+(437735938083/450800000000000 : ℝ)*((1549/10000 : ℝ)+(5491/50000 : ℝ)))^(4557/1024 : ℝ) := by
    rw [show (5633934457042868941/5635000000000000000 : ℝ)+(437735938083/450800000000000 : ℝ)*((1549/10000 : ℝ)+(5491/50000 : ℝ))=(1250084943492011/1250000000000000 : ℝ) by norm_num, show 1+(24863978177188473/100000000000000000000 : ℝ)+(1345194388491139/25000000000000000000 : ℝ)=(100030244755731153029/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24863978177188473/100000000000000000000 : ℝ) ≤ ((5633934457042868941/5635000000000000000 : ℝ)+2*(437735938083/450800000000000 : ℝ)*(1549/10000 : ℝ))^(4557/1024 : ℝ) := by
    rw [show (5633934457042868941/5635000000000000000 : ℝ)+2*(437735938083/450800000000000 : ℝ)*(1549/10000 : ℝ)=(10001117283874171/10000000000000000 : ℝ) by norm_num, show 1+2*(24863978177188473/100000000000000000000 : ℝ)=(50024863978177188473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5633934457042868941/5635000000000000000 : ℝ)*(X 1 0+X 2 0)+(437735938083/450800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (5491/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (5633934457042868941/5635000000000000000 : ℝ)) (alpha := (437735938083/450800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5633934457042868941/5635000000000000000 : ℝ)*(X 0 1+X 2 1)+(437735938083/450800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (5491/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (5633934457042868941/5635000000000000000 : ℝ)) (alpha := (437735938083/450800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5633934457042868941/5635000000000000000 : ℝ)*(X 0 2+X 1 2)+(437735938083/450800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (5491/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (5633934457042868941/5635000000000000000 : ℝ)) (alpha := (437735938083/450800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-230038077/1250000000 : ℝ)*X 0 0+(2715400413/5000000000 : ℝ)*X 0 1+(2609257337/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675260883/5000000000 : ℝ)*X 1 0+(-243623373/1250000000 : ℝ)*X 1 1+(5218514663/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350521783/10000000000 : ℝ)*X 2 0+(5218514657/10000000000 : ℝ)*X 2 1+(-1948986971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2130501253/5000000000 : ℝ)*X 0 0+(2011461673/5000000000 : ℝ)*X 0 1+(1127688027/2500000000 : ℝ)*X 0 2+(2130501253/5000000000 : ℝ)*X 1 0+(2011461673/5000000000 : ℝ)*X 1 1+(1127688027/2500000000 : ℝ)*X 1 2+(2130501253/5000000000 : ℝ)*X 2 0+(2011461673/5000000000 : ℝ)*X 2 1+(1127688027/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1840332797/10000000000 : ℝ)*X 0 0+(1304902961/2500000000 : ℝ)*X 0 1+(678711949/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647319869/5000000000 : ℝ)*X 1 0+(-347561221/2000000000 : ℝ)*X 1 1+(5429695569/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((264731987/500000000 : ℝ)*X 2 0+(5429695591/10000000000 : ℝ)*X 2 1+(-1737806073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4261067431/10000000000 : ℝ)*X 0 0+(4508230841/10000000000 : ℝ)*X 0 1+(1006365787/2500000000 : ℝ)*X 0 2+(4261067431/10000000000 : ℝ)*X 1 0+(4508230841/10000000000 : ℝ)*X 1 1+(1006365787/2500000000 : ℝ)*X 1 2+(4261067431/10000000000 : ℝ)*X 2 0+(4508230841/10000000000 : ℝ)*X 2 1+(1006365787/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (311085425554856835735408657/70437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (714904021/100000000000000 : ℝ)*(base19) + (171127003/25000000000000 : ℝ)*(base23) + (6067887/25000000000000 : ℝ)*(lower2) + (92199021/100000000000000 : ℝ)*(upper3) + (37523603/50000000000000 : ℝ)*(upper5) + (1690138907645491/50000000000000 : ℝ)*(major0) + (1690138907645491/50000000000000 : ℝ)*(major1) + (1690138907645491/50000000000000 : ℝ)*(major2) + (147207321975929/3125000000000 : ℝ)*(sp0) + (2355322581844363/50000000000000 : ℝ)*(sp1) + (36801915578787/781250000000 : ℝ)*(sp2) + (2049904413920297/100000000000000 : ℝ)*(sp3) + (11575363019/100000000000000 : ℝ)*(sp4) + (1038170619/20000000000000 : ℝ)*(sp7) + (128119350298337/6250000000000 : ℝ)*(f.failure) + (4710645878592747/100000000000000 : ℝ)*(f.sum) + (4363531613967/11270000000000000000000000000 : ℝ)*base66 + (228089868715393933/40250000000000000000000000000000 : ℝ)*base67 + (8264049556643933/40250000000000000000000000000000 : ℝ)*base69 + (155136167254893933/40250000000000000000000000000000 : ℝ)*base71 + (86422408277043/11270000000000000000000000000 : ℝ)*base73 + (387674700732143933/40250000000000000000000000000000 : ℝ)*base75 + (98625401831893933/40250000000000000000000000000000 : ℝ)*base77 + (200726514601606067/40250000000000000000000000000000 : ℝ)*base80 + (30162250355847/11270000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (340517/78125000000000000000 : ℝ)*base90 + (340517/78125000000000000000 : ℝ)*base92 + (340517/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1775365950929763359631158259/140875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (936360423/50000000000000 : ℝ)*(base19) + (132577549/6250000000000 : ℝ)*(base23) + (5986531/1000000000000 : ℝ)*(lower1) + (246289381/100000000000000 : ℝ)*(upper3) + (108779797/100000000000000 : ℝ)*(lower4) + (50530649/20000000000000 : ℝ)*(upper5) + (3415676667978483/100000000000000 : ℝ)*(major0) + (3415676667978483/100000000000000 : ℝ)*(major1) + (3415676667978483/100000000000000 : ℝ)*(major2) + (1955061807/50000000000000 : ℝ)*(sp2) + (475997630392559/10000000000000 : ℝ)*(sp4) + (594996803900593/12500000000000 : ℝ)*(sp5) + (4759970272561191/100000000000000 : ℝ)*(sp6) + (2071376611950677/100000000000000 : ℝ)*(sp7) + (2071376611950677/100000000000000 : ℝ)*(f.failure) + (475997630392559/10000000000000 : ℝ)*(f.sum) + (91714301786691/22540000000000000000000000000 : ℝ)*base66 + (854875889657341571/80500000000000000000000000000000 : ℝ)*base68 + (711958858956841571/80500000000000000000000000000000 : ℝ)*base70 + (5500784216711658429/80500000000000000000000000000000 : ℝ)*base71 + (75632988746109/22540000000000000000000000000 : ℝ)*base73 + (10010480053464841571/80500000000000000000000000000000 : ℝ)*base76 + (100687294203341571/80500000000000000000000000000000 : ℝ)*base78 + (382544660836841571/80500000000000000000000000000000 : ℝ)*base80 + (66758138238229/22540000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (7117043/1250000000000000000000 : ℝ)*base89 + (7117043/1250000000000000000000 : ℝ)*base91 + (7117043/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1531_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5491/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1531_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1531_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1991/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5289/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1531_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1531_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1531_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1991/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5289/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1531_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
